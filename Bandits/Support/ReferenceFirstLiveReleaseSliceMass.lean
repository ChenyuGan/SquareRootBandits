/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveReleaseControlTransport

/-!
# Actual first-live physical release events on whole control slices

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,293-345`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The actual retained first-live branch supplies occupied physical follower
states and one continuing live choice on every replacement whole control.
This module identifies its physical UP and DATA flags with the existing
one-round release kernel, then transfers the exact slice laws to the complete
continuous `TimeControl` carrier. It does not integrate a source-history
cylinder or assert conditional service or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped ENNReal

namespace Bandits.Support.ReferenceFirstLiveReleaseSliceMass

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Selection := ReferenceFirstLiveReleaseControlTransport.Selection
abbrev RetainedLaunchStart := ReferenceFirstLiveReleaseControlTransport.RetainedLaunchStart
abbrev Record {p : Parameters} {rate : RateInput p} :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable {p : Parameters} {rate : RateInput p}

/-- Extend the selected complement weights by the payload anchor on the
assigned slow set, as in the existing release geometry. -/
def payloadCompleteCurrentWeights
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) : Fin p.K → ℝ :=
  fun a => if ha : a ∈ payload.slowSet.val then payload.anchor a
    else weights ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩

private theorem completeCurrentWeights_eq_payload
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection (p := p) (rate := rate) x) :
    ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected =
      payloadCompleteCurrentWeights selected.view.payload
        selected.view.complementWeights := by
  rfl

private theorem choiceInputsValid_of_payload_transport
    (payload₁ payload₂ : ReferenceActivePhysicalStep.Payload rate)
    (hpayload : payload₁ = payload₂)
    (cutoff₁ cutoff₂ : Option (CoordinatorLocalArmChoice.Cutoff p))
    (hcutoff : cutoff₁ = cutoff₂)
    (time₁ time₂ : Fin p.T) (htime : time₁ = time₂)
    (weights₁ : CanonicalFastSampling.FastArm payload₁.slowSet → ℝ)
    (weights₂ : CanonicalFastSampling.FastArm payload₂.slowSet → ℝ)
    (hweights : HEq weights₁ weights₂)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid payload₂ cutoff₂ time₂ weights₂) :
    CoordinatorLocalArmChoice.ChoiceInputsValid payload₁ cutoff₁ time₁ weights₁ := by
  cases hpayload
  cases hcutoff
  cases htime
  cases hweights
  exact hvalid

/-- Form the literal release-round input from a payload, its complement
weights, and the exact pointwise envelope proofs. -/
def releaseKernelInputData
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (bounds : ∀ a, 0 < payloadCompleteCurrentWeights payload weights a ∧
      payload.anchor a ≤ payloadCompleteCurrentWeights payload weights a ∧
      payloadCompleteCurrentWeights payload weights a ≤ 2 * payload.anchor a)
    (slice : ContinuousControlSlice.Slice p.m p.K) :
    ActiveRoundActions.RoundInput payload.assignment 0 :=
  ReleaseRoundKernel.releaseRoundInput p payload.assignment payload.slowSet
    payload.assignment_image.symm rate.eta rate.eta.property
    payload.eta_le_source_cap payload.anchor
    (payloadCompleteCurrentWeights payload weights) payload.anchor_pos
    (fun a => (bounds a).1) (fun a => (bounds a).2.1)
    (fun a => (bounds a).2.2) slice

/-- Build the common action snapshot from the payload's recorded pending set
and the ordinary follower states. -/
def payloadSnapshot
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta) :
    ActiveRoundActions.Snapshot payload.assignment :=
  ⟨pending, fun i => (states i).status⟩

private theorem upKernelEventData_congr
    (payload₁ payload₂ : ReferenceActivePhysicalStep.Payload rate)
    (hpayload : payload₁ = payload₂)
    (pending₁ pending₂ : Finset (ActiveRoundActions.Follower p.m))
    (hpending : pending₁ = pending₂)
    (weights₁ : CanonicalFastSampling.FastArm payload₁.slowSet → ℝ)
    (weights₂ : CanonicalFastSampling.FastArm payload₂.slowSet → ℝ)
    (hweights : HEq weights₁ weights₂)
    (bounds₁ : ∀ a, 0 < payloadCompleteCurrentWeights payload₁ weights₁ a ∧
      payload₁.anchor a ≤ payloadCompleteCurrentWeights payload₁ weights₁ a ∧
      payloadCompleteCurrentWeights payload₁ weights₁ a ≤ 2 * payload₁.anchor a)
    (bounds₂ : ∀ a, 0 < payloadCompleteCurrentWeights payload₂ weights₂ a ∧
      payload₂.anchor a ≤ payloadCompleteCurrentWeights payload₂ weights₂ a ∧
      payloadCompleteCurrentWeights payload₂ weights₂ a ≤ 2 * payload₂.anchor a)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (row₁ row₂ : ActiveRoundActions.RewardRow p.K) (hrow : row₁ = row₂)
    (i : Fin (p.m - 1)) (slice : ContinuousControlSlice.Slice p.m p.K) :
    (ActiveRoundActions.releaseObservation p.two_le_m
        (payloadSnapshot payload₁ pending₁ states)
        (releaseKernelInputData payload₁ weights₁ bounds₁ slice) row₁ i ∧
      (releaseKernelInputData payload₁ weights₁ bounds₁ slice).slot =
        PublicDiscreteDraws.upSlot) ↔
    (ActiveRoundActions.releaseObservation p.two_le_m
        (payloadSnapshot payload₂ pending₂ states)
        (releaseKernelInputData payload₂ weights₂ bounds₂ slice) row₂ i ∧
      (releaseKernelInputData payload₂ weights₂ bounds₂ slice).slot =
        PublicDiscreteDraws.upSlot) := by
  cases hpayload
  cases hpending
  cases hweights
  cases hrow
  rfl

private theorem dataKernelEventData_congr
    (payload₁ payload₂ : ReferenceActivePhysicalStep.Payload rate)
    (hpayload : payload₁ = payload₂)
    (pending₁ pending₂ : Finset (ActiveRoundActions.Follower p.m))
    (hpending : pending₁ = pending₂)
    (weights₁ : CanonicalFastSampling.FastArm payload₁.slowSet → ℝ)
    (weights₂ : CanonicalFastSampling.FastArm payload₂.slowSet → ℝ)
    (hweights : HEq weights₁ weights₂)
    (bounds₁ : ∀ a, 0 < payloadCompleteCurrentWeights payload₁ weights₁ a ∧
      payload₁.anchor a ≤ payloadCompleteCurrentWeights payload₁ weights₁ a ∧
      payloadCompleteCurrentWeights payload₁ weights₁ a ≤ 2 * payload₁.anchor a)
    (bounds₂ : ∀ a, 0 < payloadCompleteCurrentWeights payload₂ weights₂ a ∧
      payload₂.anchor a ≤ payloadCompleteCurrentWeights payload₂ weights₂ a ∧
      payloadCompleteCurrentWeights payload₂ weights₂ a ≤ 2 * payload₂.anchor a)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (row₁ row₂ : ActiveRoundActions.RewardRow p.K) (hrow : row₁ = row₂)
    (i : Fin (p.m - 1)) (slice : ContinuousControlSlice.Slice p.m p.K) :
    (ActiveRoundActions.releaseObservation p.two_le_m
        (payloadSnapshot payload₁ pending₁ states)
        (releaseKernelInputData payload₁ weights₁ bounds₁ slice) row₁ i ∧
      (releaseKernelInputData payload₁ weights₁ bounds₁ slice).slot =
        PublicDiscreteDraws.dataSlot) ↔
    (ActiveRoundActions.releaseObservation p.two_le_m
        (payloadSnapshot payload₂ pending₂ states)
        (releaseKernelInputData payload₂ weights₂ bounds₂ slice) row₂ i ∧
      (releaseKernelInputData payload₂ weights₂ bounds₂ slice).slot =
        PublicDiscreteDraws.dataSlot) := by
  cases hpayload
  cases hpending
  cases hweights
  cases hrow
  rfl

/-- Coordinate-level UP event on the literal release-round input. -/
def upKernelConditionsData
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (bounds : ∀ a, 0 < payloadCompleteCurrentWeights payload weights a ∧
      payload.anchor a ≤ payloadCompleteCurrentWeights payload weights a ∧
      payloadCompleteCurrentWeights payload weights a ≤ 2 * payload.anchor a)
    (i : Fin (p.m - 1)) (slice : ContinuousControlSlice.Slice p.m p.K)
    (row : ActiveRoundActions.RewardRow p.K) : Prop :=
  let input := releaseKernelInputData payload weights bounds slice
  input.slot = PublicDiscreteDraws.upSlot ∧ input.selected = i ∧
    input.tuple.val (ActiveRoundActions.coordinator p.two_le_m) = payload.assignment.auxiliary ∧
    input.fast ≠ payload.assignment.auxiliary ∧
    0 < row.val payload.assignment.auxiliary

/-- Coordinate-level DATA event on the literal release-round input. -/
def dataKernelConditionsData
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (bounds : ∀ a, 0 < payloadCompleteCurrentWeights payload weights a ∧
      payload.anchor a ≤ payloadCompleteCurrentWeights payload weights a ∧
      payloadCompleteCurrentWeights payload weights a ≤ 2 * payload.anchor a)
    (i : Fin (p.m - 1)) (slice : ContinuousControlSlice.Slice p.m p.K)
    (row : ActiveRoundActions.RewardRow p.K) : Prop :=
  let input := releaseKernelInputData payload weights bounds slice
  input.slot = PublicDiscreteDraws.dataSlot ∧
    input.pilots (ActiveRoundActions.coordinator p.two_le_m) = payload.assignment.assigned i ∧
    0 < row.val (payload.assignment.assigned i)

private theorem upKernelConditionsData_congr
    (payload₁ payload₂ : ReferenceActivePhysicalStep.Payload rate)
    (hpayload : payload₁ = payload₂)
    (weights₁ : CanonicalFastSampling.FastArm payload₁.slowSet → ℝ)
    (weights₂ : CanonicalFastSampling.FastArm payload₂.slowSet → ℝ)
    (hweights : HEq weights₁ weights₂)
    (bounds₁ : ∀ a, 0 < payloadCompleteCurrentWeights payload₁ weights₁ a ∧
      payload₁.anchor a ≤ payloadCompleteCurrentWeights payload₁ weights₁ a ∧
      payloadCompleteCurrentWeights payload₁ weights₁ a ≤ 2 * payload₁.anchor a)
    (bounds₂ : ∀ a, 0 < payloadCompleteCurrentWeights payload₂ weights₂ a ∧
      payload₂.anchor a ≤ payloadCompleteCurrentWeights payload₂ weights₂ a ∧
      payloadCompleteCurrentWeights payload₂ weights₂ a ≤ 2 * payload₂.anchor a)
    (i : Fin (p.m - 1)) (slice : ContinuousControlSlice.Slice p.m p.K)
    (row₁ row₂ : ActiveRoundActions.RewardRow p.K) (hrow : row₁ = row₂) :
    upKernelConditionsData payload₁ weights₁ bounds₁ i slice row₁ ↔
      upKernelConditionsData payload₂ weights₂ bounds₂ i slice row₂ := by
  cases hpayload
  cases hweights
  cases hrow
  rfl

private theorem dataKernelConditionsData_congr
    (payload₁ payload₂ : ReferenceActivePhysicalStep.Payload rate)
    (hpayload : payload₁ = payload₂)
    (weights₁ : CanonicalFastSampling.FastArm payload₁.slowSet → ℝ)
    (weights₂ : CanonicalFastSampling.FastArm payload₂.slowSet → ℝ)
    (hweights : HEq weights₁ weights₂)
    (bounds₁ : ∀ a, 0 < payloadCompleteCurrentWeights payload₁ weights₁ a ∧
      payload₁.anchor a ≤ payloadCompleteCurrentWeights payload₁ weights₁ a ∧
      payloadCompleteCurrentWeights payload₁ weights₁ a ≤ 2 * payload₁.anchor a)
    (bounds₂ : ∀ a, 0 < payloadCompleteCurrentWeights payload₂ weights₂ a ∧
      payload₂.anchor a ≤ payloadCompleteCurrentWeights payload₂ weights₂ a ∧
      payloadCompleteCurrentWeights payload₂ weights₂ a ≤ 2 * payload₂.anchor a)
    (i : Fin (p.m - 1)) (slice : ContinuousControlSlice.Slice p.m p.K)
    (row₁ row₂ : ActiveRoundActions.RewardRow p.K) (hrow : row₁ = row₂) :
    dataKernelConditionsData payload₁ weights₁ bounds₁ i slice row₁ ↔
      dataKernelConditionsData payload₂ weights₂ bounds₂ i slice row₂ := by
  cases hpayload
  cases hweights
  cases hrow
  rfl

/-- The literal kernel input with the actual fixed payload and current
complement weights, evaluated at one complete continuous scalar slice. -/
def releaseKernelInput
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection (p := p) (rate := rate) x)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights)
    (slice : ContinuousControlSlice.Slice p.m p.K) :
    ActiveRoundActions.RoundInput selected.view.payload.assignment 0 :=
  releaseKernelInputData selected.view.payload selected.view.complementWeights
    (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected hvalid) slice

/-- The literal UP release event of the existing round kernel. -/
def upKernelEvent
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection (p := p) (rate := rate) x)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (row : ActiveRoundActions.RewardRow p.K) (i : Fin (p.m - 1))
    (slice : ContinuousControlSlice.Slice p.m p.K) : Prop :=
  ActiveRoundActions.releaseObservation p.two_le_m
    (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states)
    (releaseKernelInput selected hvalid slice) row i ∧
  (releaseKernelInput selected hvalid slice).slot = PublicDiscreteDraws.upSlot

/-- The literal DATA release event of the existing round kernel. -/
def dataKernelEvent
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection (p := p) (rate := rate) x)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (row : ActiveRoundActions.RewardRow p.K) (i : Fin (p.m - 1))
    (slice : ContinuousControlSlice.Slice p.m p.K) : Prop :=
  ActiveRoundActions.releaseObservation p.two_le_m
    (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states)
    (releaseKernelInput selected hvalid slice) row i ∧
  (releaseKernelInput selected hvalid slice).slot = PublicDiscreteDraws.dataSlot

/-- The UP event's literal slot, receiver, auxiliary-tuple, fast-arm, and
positive-reward conditions. -/
def upKernelConditions
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection (p := p) (rate := rate) x)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights)
    (i : Fin (p.m - 1)) (slice : ContinuousControlSlice.Slice p.m p.K)
    (row : ActiveRoundActions.RewardRow p.K) : Prop :=
  upKernelConditionsData selected.view.payload selected.view.complementWeights
    (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected hvalid)
    i slice row

/-- The DATA event's literal slot, coordinator pilot, and positive-reward
conditions. No recording mask appears in this event. -/
def dataKernelConditions
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection (p := p) (rate := rate) x)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights)
    (i : Fin (p.m - 1)) (slice : ContinuousControlSlice.Slice p.m p.K)
    (row : ActiveRoundActions.RewardRow p.K) : Prop :=
  dataKernelConditionsData selected.view.payload selected.view.complementWeights
    (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected hvalid)
    i slice row

/-- The exact UP mass supplied by the actual current weights and the
assignment payload's auxiliary arm. Its body is
`chi(row,e) * (1-qGamma(v,w,U,e)) / (4*(m-1)*K)`. -/
def upReleaseMassFormula
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection (p := p) (rate := rate) x)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights)
    (row : ActiveRoundActions.RewardRow p.K) : ℝ :=
  let payload := selected.view.payload
  let v := payload.anchor
  let w := ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected
  let bounds := fun a =>
    ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected hvalid a
  let hU := payload.assignment_image.symm
  let e := ReleaseRoundKernel.auxiliaryFastArm payload.assignment payload.slowSet hU
  ReleaseRoundKernel.chi row payload.assignment.auxiliary *
    (1 - CanonicalFastSampling.qGamma p rate.eta rate.eta.property
      payload.eta_le_source_cap v w payload.anchor_pos
      (fun a => (bounds a).1) (fun a => (bounds a).2.1) (fun a => (bounds a).2.2)
      payload.slowSet e) /
    (4 * (p.m - 1 : ℝ) * (p.K : ℝ))

/-- The physical UP flag on the retained first-live record, as an event on
the genuine whole-control carrier. The proof index records actual window
membership and is not an extra random coordinate. -/
def retainedUpFlagEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0)
    (hn : t.val - s <
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0).length)
    (selected0 : Selection (p := p) (rate := rate)
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].input)
    (i : Fin (p.m - 1)) : Set (TimeControl p) :=
  {u | ∃ hwindow : t.val - s <
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x u).length,
    ReferencePhysicalReleaseQuota.upFlag selected0.view.payload
      ((ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x u)[t.val - s]'hwindow) i = true}

/-- The physical DATA flag on the retained first-live record, as an event on
the genuine whole-control carrier. -/
def retainedDataFlagEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0)
    (hn : t.val - s <
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0).length)
    (selected0 : Selection (p := p) (rate := rate)
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].input)
    (i : Fin (p.m - 1)) : Set (TimeControl p) :=
  {u | ∃ hwindow : t.val - s <
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x u).length,
    ReferencePhysicalReleaseQuota.dataFlag selected0.view.payload
      ((ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x u)[t.val - s]'hwindow) i = true}

/-- On an actual occupied ordinary preparation, physical flags, the kernel's
release observations, and the literal UP/DATA draw conditions agree. Every
state, status, weight, and arm input is an explicit local field here; the
retained root below constructs them from its generated run. -/
theorem actual_release_flags_and_kernel_events_iff
    (record : Record (p := p) (rate := rate))
    (selected : Selection (p := p) (rate := rate) record.input)
    (hselected : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection =
      some selected)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ j,
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers j).configuration =
        .ordinary (states j) (memories j))
    (hfields : ∀ j, (states j).status ≠ .unoccupied ∧
      (states j).lastDown = some (selected.view.payload.downRecord j))
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff record.input.time selected.view.complementWeights)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff record.input.time)
    (hempty : selected.view.pendingAtChoice = ∅)
    (i : Fin (p.m - 1))
    (hipending : (states i).status = .pending) :
    (ReferencePhysicalReleaseQuota.upFlag selected.view.payload record i = true ↔
      upKernelEvent selected hvalid states
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
          record.input.rewards record.input.time) i
        ((record.input.row.2 record.input.time).1)) ∧
    (ReferencePhysicalReleaseQuota.dataFlag selected.view.payload record i = true ↔
      dataKernelEvent selected hvalid states
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
          record.input.rewards record.input.time) i
        ((record.input.row.2 record.input.time).1)) ∧
    (upKernelEvent selected hvalid states
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
          record.input.rewards record.input.time) i
        ((record.input.row.2 record.input.time).1) ↔
      upKernelConditions selected hvalid i
        ((record.input.row.2 record.input.time).1)
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
          record.input.rewards record.input.time)) ∧
    (dataKernelEvent selected hvalid states
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
          record.input.rewards record.input.time) i
        ((record.input.row.2 record.input.time).1) ↔
      dataKernelConditions selected hvalid i
        ((record.input.row.2 record.input.time).1)
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
          record.input.rewards record.input.time)) := by
  let snapshot := ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states
  let input := ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput selected hvalid
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
    record.input.rewards record.input.time
  have hmissing : snapshot.missing = ∅ := by
    change selected.view.pendingAtChoice = ∅
    exact hempty
  have hstatus : ∀ j, snapshot.status j = .pending ∨ snapshot.status j = .released := by
    intro j
    change (states j).status = .pending ∨ (states j).status = .released
    cases hstatus : (states j).status with
    | unoccupied => exact False.elim ((hfields j).1 hstatus)
    | pending => exact Or.inl rfl
    | released => exact Or.inr rfl
  have hstatusI : snapshot.status i = .pending := by
    change (states i).status = .pending
    exact hipending
  have hslot : PublicDiscreteDraws.slotDraw
      ((record.input.row.2 record.input.time).1) = input.slot := by rfl
  have hselectedDraw : PublicDiscreteDraws.selectedFollowerDraw
      p.two_le_m p.m_lt_K ((record.input.row.2 record.input.time).1) = input.selected := by rfl
  have htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K
      ((record.input.row.2 record.input.time).1) = input.tuple := by rfl
  have hpilots : input.pilots = fun player => PublicDiscreteDraws.pilotDraw
      (K_pos p) player ((record.input.row.2 record.input.time).1) := by rfl
  have hfastFacts :=
    ReferenceFirstLiveReleaseGeometry.actual_releaseRoundInput_fast_eq_selected
      selected hlive hempty hvalid
  have hfast : input.fast = selected.arm := by
    simpa only [input, ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput] using
      hfastFacts.1
  have hactions :=
    ReferenceFirstLiveReleaseGeometry.prepared_actions_eq_projected
      selected hselected states memories hordinary hfields input hmissing
      hslot.symm hselectedDraw.symm htuple.symm hfast
  have hrelease :=
    ReferenceFirstLiveReleaseGeometry.prepared_releaseCondition_eq_projected
      selected snapshot input i hactions hslot.symm hselectedDraw.symm htuple.symm hpilots
  have hflag := ReferenceFirstLiveReleaseGeometry.actual_release_flags_iff
    record selected.view.payload i
  have hflagUp : ReferencePhysicalReleaseQuota.upFlag selected.view.payload record i = true ↔
      ActiveFollowerLifecycle.releaseCondition rate.eta i
        (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
        ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (selected.view.payload.downRecord i) ∧ input.slot = PublicDiscreteDraws.upSlot := by
    simpa only [hslot] using hflag.1
  have hflagData : ReferencePhysicalReleaseQuota.dataFlag selected.view.payload record i = true ↔
      ActiveFollowerLifecycle.releaseCondition rate.eta i
        (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
        ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (selected.view.payload.downRecord i) ∧ input.slot = PublicDiscreteDraws.dataSlot := by
    simpa only [hslot] using hflag.2
  have hgeometry :=
    ReferenceFirstLiveReleaseGeometry.actual_pending_release_event_geometry
      selected snapshot input row hmissing hstatus i hstatusI hrelease
  have hindex : ReferenceFirstLiveReleaseGeometry.followerToFin i = i := by
    apply Fin.ext
    rfl
  have hreleaseGeometry :
      ActiveFollowerLifecycle.releaseCondition rate.eta
          (ReferenceFirstLiveReleaseGeometry.followerToFin i)
          (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
          ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))
          (selected.view.payload.downRecord i) =
        ActiveRoundActions.releaseObservation p.two_le_m snapshot input row i := by
    simpa only [hindex] using hrelease
  have hflagUp' : ReferencePhysicalReleaseQuota.upFlag selected.view.payload record i = true ↔
      ActiveRoundActions.releaseObservation p.two_le_m snapshot input row i ∧
        input.slot = PublicDiscreteDraws.upSlot := by
    simpa only [hrelease] using hflagUp
  have hflagData' : ReferencePhysicalReleaseQuota.dataFlag selected.view.payload record i = true ↔
      ActiveRoundActions.releaseObservation p.two_le_m snapshot input row i ∧
        input.slot = PublicDiscreteDraws.dataSlot := by
    simpa only [hrelease] using hflagData
  have hgeometryUp :
      (ActiveRoundActions.releaseObservation p.two_le_m snapshot input row i ∧
        input.slot = PublicDiscreteDraws.upSlot) ↔
      input.slot = PublicDiscreteDraws.upSlot ∧ input.selected = i ∧
        input.tuple.val (ActiveRoundActions.coordinator p.two_le_m) =
          selected.view.payload.assignment.auxiliary ∧
        input.fast ≠ selected.view.payload.assignment.auxiliary ∧
        0 < row.val selected.view.payload.assignment.auxiliary := by
    simpa only [← hreleaseGeometry] using hgeometry.1
  have hgeometryData :
      (ActiveRoundActions.releaseObservation p.two_le_m snapshot input row i ∧
        input.slot = PublicDiscreteDraws.dataSlot) ↔
      input.slot = PublicDiscreteDraws.dataSlot ∧
        input.pilots (ActiveRoundActions.coordinator p.two_le_m) =
          selected.view.payload.assignment.assigned i ∧
        0 < row.val (selected.view.payload.assignment.assigned i) := by
    simpa only [← hreleaseGeometry] using hgeometry.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [snapshot, input, row,
      ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput,
      ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot,
      ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
      completeCurrentWeights_eq_payload,
      payloadSnapshot, payloadCompleteCurrentWeights, releaseKernelInputData,
      releaseKernelInput, upKernelEvent] using hflagUp'
  · simpa only [snapshot, input, row,
      ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput,
      ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot,
      ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
      completeCurrentWeights_eq_payload,
      payloadSnapshot, payloadCompleteCurrentWeights, releaseKernelInputData,
      releaseKernelInput, dataKernelEvent] using hflagData'
  · simpa only [snapshot, input, row, upKernelEvent,
      ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot,
      ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput,
      ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
      completeCurrentWeights_eq_payload,
      payloadSnapshot, payloadCompleteCurrentWeights, releaseKernelInputData,
      releaseKernelInput, upKernelConditions, upKernelConditionsData] using hgeometryUp
  · simpa only [snapshot, input, row, dataKernelEvent,
      ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot,
      ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput,
      ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
      completeCurrentWeights_eq_payload,
      payloadSnapshot, payloadCompleteCurrentWeights, releaseKernelInputData,
      releaseKernelInput, dataKernelConditions, dataKernelConditionsData] using hgeometryData

/-- On the computed retained branch, the actual same-time first-live record,
all ordinary follower configurations, selected continuation, fixed payload and
weights, and current pending query are returned for every whole replacement
control. Physical flags are identified with the literal `releaseKernelInput`
events on that same control's scalar slice. -/
theorem retained_first_live_release_all_controls
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0)
    (hn : t.val - s <
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0).length)
    (selected0 : Selection (p := p) (rate := rate)
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].input)
    (hselected :
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].output.preparation.coordinator.selection =
        some selected0)
    (hempty : selected0.view.pendingAtChoice = ∅)
    (i : Fin (p.m - 1))
    (hi : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart
      selected0.view.payload
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).time
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state) :
    let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0 x
    let n := t.val - s
    ∃ hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected0.view.payload
        selected0.view.cutoff
          (ReferenceFirstLiveReleaseControlTransport.retainedWindow
            rewards C_star C_h q t s hs control0 x control0)[n].input.time
          selected0.view.complementWeights,
      ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
        (∀ j, (states j).status ≠ .unoccupied ∧
          (states j).lastDown = some (selected0.view.payload.downRecord j)) ∧
        (∀ j, j ∈ ReferencePhysicalReleaseQuota.pendingAtStart
            selected0.view.payload beta.time beta.state ↔ (states j).status = .pending) ∧
        ∀ u : TimeControl p,
          ∃ hwindow : n <
            (ReferenceFirstLiveReleaseControlTransport.retainedWindow
              rewards C_star C_h q t s hs control0 x u).length,
          ∃ selectedU : Selection (p := p) (rate := rate)
            (ReferenceFirstLiveReleaseControlTransport.retainedWindow
              rewards C_star C_h q t s hs control0 x u)[n].input,
            let record :=
              (ReferenceFirstLiveReleaseControlTransport.retainedWindow
                rewards C_star C_h q t s hs control0 x u)[n]'hwindow
            record.input =
                ReferenceLaterOptionalControlResampling.withControl beta u ∧
            ReferenceCollectionPhaseHistory.cutoffChosen record.input = false ∧
            (∀ j, ((ReferenceActivePhysicalStep.prepare record.input).followers.followers j).configuration =
              .ordinary (states j) (memories j)) ∧
            (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection =
              some selectedU ∧
            record.output.preparation.coordinator.selection = some selectedU ∧
            selectedU.view.payload = selected0.view.payload ∧
            selectedU.view.pendingAtChoice = selected0.view.pendingAtChoice ∧
            selectedU.view.cutoff = selected0.view.cutoff ∧
            HEq selectedU.view.complementWeights selected0.view.complementWeights ∧
            (∀ j, j ∈ ReferencePhysicalReleaseQuota.pendingAtStart
              selectedU.view.payload record.input.time record.input.state ↔
                (states j).status = .pending) ∧
            (ReferencePhysicalReleaseQuota.upFlag selected0.view.payload record i = true ↔
              upKernelEvent selected0 hvalid states
                (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) i u.1) ∧
            (ReferencePhysicalReleaseQuota.dataFlag selected0.view.payload record i = true ↔
              dataKernelEvent selected0 hvalid states
                (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) i u.1) ∧
            (upKernelEvent selected0 hvalid states
                (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) i u.1 ↔
              upKernelConditions selected0 hvalid i u.1
                (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)) ∧
            (dataKernelEvent selected0 hvalid states
                (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) i u.1 ↔
              dataKernelConditions selected0 hvalid i u.1
                (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)) := by
  let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 x
  let n := t.val - s
  have htransport :=
    ReferenceFirstLiveReleaseControlTransport.retained_first_live_control_transport
      rewards C_star C_h q t s hs control0 x hn selected0 hselected hempty
  obtain ⟨r, owned, base, hbeta, _hstate, _htimeNext, _hprior, _hpending,
      _hnoCut, _hpayload, _hcutoff, _hweights, d, hsStart, c, arm, hctor,
      hvalidTransport, states, memories, _hprepared, hfields, hpendingStatus,
      hcontrols⟩ := htransport
  have hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected0.view.payload
      selected0.view.cutoff
        (ReferenceFirstLiveReleaseControlTransport.retainedWindow
          rewards C_star C_h q t s hs control0 x control0)[n].input.time
      selected0.view.complementWeights := by
    exact hvalidTransport
  refine ⟨hvalid, states, memories, hfields, hpendingStatus, ?_⟩
  intro u
  rcases hcontrols u with ⟨hwindow, hinput, _hinputAt, hnoCutU, hordinaryU,
      selectedU, hselectedPrepU, hselectedOutputU, hpayloadU, hpendingU,
      hcutoffU, hweightsU, hqueryU⟩
  let record :=
    (ReferenceFirstLiveReleaseControlTransport.retainedWindow
      rewards C_star C_h q t s hs control0 x u)[n]'hwindow
  have hinput' : record.input =
      ReferenceLaterOptionalControlResampling.withControl beta u := by
    simpa only [record, n, ReferenceFirstLiveReleaseControlTransport.retainedWindow] using
      hinput
  have htimeRecord : record.input.time = t := by
    rw [hinput']
    simp [beta, ReferenceLaterOptionalControlResampling.withControl_time]
  have hrewardRecord : record.input.rewards = rewards := by
    rw [hinput']
    simp [beta, ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary,
      ReferenceLaterOptionalControlResampling.withControl_rewards]
  have hfieldsU : ∀ j, (states j).status ≠ .unoccupied ∧
      (states j).lastDown = some (selectedU.view.payload.downRecord j) := by
    intro j
    refine ⟨(hfields j).1, ?_⟩
    simpa only [hpayloadU] using (hfields j).2
  have htimeBaseline :
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[n].input.time = t := by
    have htime := congrArg (fun z => z.time) hbeta
    have hwindowTime :
        (ReferenceFirstLiveReleaseControlTransport.retainedWindow
          rewards C_star C_h q t s hs control0 x control0)[n].input.time =
          beta.time := by
      exact htime.symm
    rw [hwindowTime]
    simp [beta]
  have htimeU : record.input.time =
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[n].input.time :=
    htimeRecord.trans htimeBaseline.symm
  have hcontrolSlice : (record.input.row.2 record.input.time).1 = u.1 := by
    rw [hinput']
    simp [ReferenceLaterOptionalControlResampling.withControl_row,
      htimeRecord, beta]
  have hcontrolSlice : (record.input.row.2 record.input.time).1 = u.1 := by
    rw [hinput']
    simp [ReferenceLaterOptionalControlResampling.withControl_row,
      htimeRecord, beta]
  have hvalidU : CoordinatorLocalArmChoice.ChoiceInputsValid selectedU.view.payload
      selectedU.view.cutoff record.input.time selectedU.view.complementWeights := by
    exact choiceInputsValid_of_payload_transport selectedU.view.payload
      selected0.view.payload hpayloadU selectedU.view.cutoff selected0.view.cutoff
      hcutoffU record.input.time
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[n].input.time htimeU
      selectedU.view.complementWeights selected0.view.complementWeights hweightsU hvalid
  have hliveU : CoordinatorLocalArmChoice.assignmentIsLive selectedU.view.payload
      selectedU.view.cutoff record.input.time := by
    rw [hcutoffU, _hcutoff]
    change CoordinatorLocalArmChoice.assignmentStart selectedU.view.payload ≤
        CoordinatorLocalArmChoice.sourceRound record.input.time ∧
      CoordinatorLocalArmChoice.sourceRound record.input.time <
        CoordinatorLocalArmChoice.cutoffRound none
    refine ⟨hvalidU.time.assignment_started, ?_⟩
    simp only [CoordinatorLocalArmChoice.cutoffRound, Option.elim_none]
    have hsource := hvalidU.time.source_round_le_horizon
    omega
  have hemptyU : selectedU.view.pendingAtChoice = ∅ := by
    rw [hpendingU]
    exact hempty
  have hqueryI : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart
      selectedU.view.payload record.input.time record.input.state := by
    simpa only [hpayloadU, hinput', beta,
      ReferenceLaterOptionalControlResampling.withControl_state,
      ReferenceLaterOptionalControlResampling.withControl_time] using hi
  have hiState : (states i).status = .pending := (hqueryU i).mp hqueryI
  have hhelper := actual_release_flags_and_kernel_events_iff
      record selectedU hselectedPrepU states memories hordinaryU hfieldsU hvalidU
      hliveU hemptyU i hiState
  have hrowEq :
      ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
          record.input.rewards record.input.time =
        ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t := by
    rw [hrewardRecord, htimeRecord]
  have hboundsU := ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
    selectedU hvalidU
  have hbounds0 := ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
    selected0 hvalid
  have hupEventEq :
      upKernelEvent selectedU hvalidU states
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
            record.input.rewards record.input.time) i
          (record.input.row.2 record.input.time).1 ↔
        upKernelEvent selected0 hvalid states
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) i
          (record.input.row.2 record.input.time).1 := by
    simpa only [upKernelEvent, releaseKernelInput,
      ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot, payloadSnapshot] using
      upKernelEventData_congr selectedU.view.payload selected0.view.payload
      hpayloadU selectedU.view.pendingAtChoice selected0.view.pendingAtChoice hpendingU
      selectedU.view.complementWeights selected0.view.complementWeights hweightsU
      hboundsU hbounds0 states
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow record.input.rewards record.input.time)
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) hrowEq i
      (record.input.row.2 record.input.time).1
  have hdataEventEq :
      dataKernelEvent selectedU hvalidU states
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
            record.input.rewards record.input.time) i
          (record.input.row.2 record.input.time).1 ↔
        dataKernelEvent selected0 hvalid states
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) i
          (record.input.row.2 record.input.time).1 := by
    simpa only [dataKernelEvent, releaseKernelInput,
      ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot, payloadSnapshot] using
      dataKernelEventData_congr selectedU.view.payload selected0.view.payload
      hpayloadU selectedU.view.pendingAtChoice selected0.view.pendingAtChoice hpendingU
      selectedU.view.complementWeights selected0.view.complementWeights hweightsU
      hboundsU hbounds0 states
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow record.input.rewards record.input.time)
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) hrowEq i
      (record.input.row.2 record.input.time).1
  have hupConditionsEq :
      upKernelConditions selectedU hvalidU i (record.input.row.2 record.input.time).1
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow record.input.rewards record.input.time) ↔
        upKernelConditions selected0 hvalid i (record.input.row.2 record.input.time).1
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) := by
    simpa only [upKernelConditions] using
      upKernelConditionsData_congr selectedU.view.payload selected0.view.payload
      hpayloadU selectedU.view.complementWeights selected0.view.complementWeights hweightsU
      hboundsU hbounds0 i (record.input.row.2 record.input.time).1
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow record.input.rewards record.input.time)
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) hrowEq
  have hdataConditionsEq :
      dataKernelConditions selectedU hvalidU i (record.input.row.2 record.input.time).1
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow record.input.rewards record.input.time) ↔
        dataKernelConditions selected0 hvalid i (record.input.row.2 record.input.time).1
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) := by
    simpa only [dataKernelConditions] using
      dataKernelConditionsData_congr selectedU.view.payload selected0.view.payload
      hpayloadU selectedU.view.complementWeights selected0.view.complementWeights hweightsU
      hboundsU hbounds0 i (record.input.row.2 record.input.time).1
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow record.input.rewards record.input.time)
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) hrowEq
  have hflagUpPayload :
      ReferencePhysicalReleaseQuota.upFlag selectedU.view.payload record i = true ↔
        ReferencePhysicalReleaseQuota.upFlag selected0.view.payload record i = true := by
    rw [hpayloadU]
  have hflagDataPayload :
      ReferencePhysicalReleaseQuota.dataFlag selectedU.view.payload record i = true ↔
        ReferencePhysicalReleaseQuota.dataFlag selected0.view.payload record i = true := by
    rw [hpayloadU]
  have hupBaselineCondition :
      upKernelEvent selected0 hvalid states
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) i u.1 ↔
        upKernelConditions selected0 hvalid i u.1
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) := by
    rw [← hcontrolSlice]
    exact hupEventEq.symm.trans (hhelper.2.2.1.trans hupConditionsEq)
  have hdataBaselineCondition :
      dataKernelEvent selected0 hvalid states
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) i u.1 ↔
        dataKernelConditions selected0 hvalid i u.1
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) := by
    rw [← hcontrolSlice]
    exact hdataEventEq.symm.trans (hhelper.2.2.2.trans hdataConditionsEq)
  refine ⟨hwindow, selectedU, ?_, ?_, hordinaryU, hselectedPrepU,
    hselectedOutputU, hpayloadU, hpendingU, hcutoffU, hweightsU, hqueryU,
    ?_, ?_, ?_, ?_⟩
  · exact hinput'
  · exact hnoCutU
  · exact hflagUpPayload.symm.trans
      (hhelper.1.trans (hupEventEq.trans (by rw [hcontrolSlice])))
  · exact hflagDataPayload.symm.trans
      (hhelper.2.1.trans (hdataEventEq.trans (by rw [hcontrolSlice])))
  · exact hupBaselineCondition
  · exact hdataBaselineCondition

private theorem retained_up_release_measure_results
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0)
    (hn : t.val - s <
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0).length)
    (selected0 : Selection (p := p) (rate := rate)
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].input)
    (hselected :
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].output.preparation.coordinator.selection =
        some selected0)
    (hempty : selected0.view.pendingAtChoice = ∅)
    (i : Fin (p.m - 1))
    (hi : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart
      selected0.view.payload
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).time
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state) :
    ∃ hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected0.view.payload
      selected0.view.cutoff
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].input.time
      selected0.view.complementWeights,
      ContinuousLearningRows.timeControlLaw p
          (retainedUpFlagEvent rewards C_star C_h q t s hs control0 x hn selected0 i) =
        ENNReal.ofReal (upReleaseMassFormula selected0 hvalid
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)) ∧
      ENNReal.ofReal
          (ReleaseRoundKernel.chi
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
            selected0.view.payload.assignment.auxiliary /
            (12 * (p.m - 1 : ℝ) * (p.K : ℝ))) ≤
        ContinuousLearningRows.timeControlLaw p
          (retainedUpFlagEvent rewards C_star C_h q t s hs control0 x hn selected0 i) := by
  let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 x
  let n := t.val - s
  let payload := selected0.view.payload
  let a := payload.assignment
  let U := payload.slowSet
  let hU := payload.assignment_image.symm
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  obtain ⟨hvalid, states, memories, hfields, hpendingStatus,
      hcontrols⟩ := retained_first_live_release_all_controls
        rewards C_star C_h q t s hs control0 x hn selected0 hselected hempty i hi
  let snapshot := ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected0 states
  have hmissing : snapshot.missing = ∅ := by
    change selected0.view.pendingAtChoice = ∅
    exact hempty
  have hstatus : ∀ j, snapshot.status j = .pending ∨ snapshot.status j = .released := by
    intro j
    change (states j).status = .pending ∨ (states j).status = .released
    cases hstate : (states j).status with
    | unoccupied => exact False.elim ((hfields j).1 hstate)
    | pending => exact Or.inl rfl
    | released => exact Or.inr rfl
  have hiState : (states i).status = .pending := (hpendingStatus i).mp hi
  have hsliceTransport (u : TimeControl p) :
      ∃ hwindow : n <
          (ReferenceFirstLiveReleaseControlTransport.retainedWindow
            rewards C_star C_h q t s hs control0 x u).length,
        (ReferencePhysicalReleaseQuota.upFlag selected0.view.payload
            ((ReferenceFirstLiveReleaseControlTransport.retainedWindow
              rewards C_star C_h q t s hs control0 x u)[n]'hwindow) i = true ↔
          upKernelEvent selected0 hvalid states row i u.1) ∧
        (upKernelEvent selected0 hvalid states row i u.1 ↔
          upKernelConditions selected0 hvalid i u.1 row) := by
    rcases hcontrols u with ⟨hwindow, selectedU, _hinput, _hcut, _hordinary,
        _hselected, _houtput, _hpayload, _hpending, _hcutoff, _hweights,
        _hquery, hupFlag, _hdataFlag, hupCondition, _hdataCondition⟩
    exact ⟨hwindow, hupFlag, hupCondition⟩
  let upSet : Set (ContinuousControlSlice.Slice p.m p.K) :=
    {z | upKernelEvent selected0 hvalid states row i z}
  have hflagSet : retainedUpFlagEvent rewards C_star C_h q t s hs control0
      x hn selected0 i = Prod.fst ⁻¹' upSet := by
    ext u
    change (∃ hwindow : n <
        (ReferenceFirstLiveReleaseControlTransport.retainedWindow
          rewards C_star C_h q t s hs control0 x u).length,
        ReferencePhysicalReleaseQuota.upFlag selected0.view.payload
          ((ReferenceFirstLiveReleaseControlTransport.retainedWindow
            rewards C_star C_h q t s hs control0 x u)[n]'hwindow) i = true) ↔
      u.1 ∈ upSet
    constructor
    · rintro ⟨hwindow, hflag⟩
      obtain ⟨hwindow', hiff, _⟩ := hsliceTransport u
      have hproof : hwindow = hwindow' := Subsingleton.elim _ _
      subst hwindow
      have hevent := hiff.mp hflag
      simpa only [upSet, Set.mem_setOf_eq] using hevent
    · intro hu
      obtain ⟨hwindow, hiff, _⟩ := hsliceTransport u
      have hevent : upKernelEvent selected0 hvalid states row i u.1 := by
        simpa only [upSet, Set.mem_setOf_eq] using hu
      exact ⟨hwindow, hiff.mpr hevent⟩
  let conditionSet : Set (ContinuousControlSlice.Slice p.m p.K) :=
    {z | upKernelConditions selected0 hvalid i z row}
  have hconditionSet : upSet = conditionSet := by
    ext z
    constructor
    · intro hz
      let u : TimeControl p := (z, control0.2)
      obtain ⟨_, _, hupCondition⟩ := hsliceTransport u
      have hevent : upKernelEvent selected0 hvalid states row i u.1 := by
        simpa only [upSet, Set.mem_setOf_eq, u] using hz
      have hcondition := hupCondition.mp hevent
      simpa only [conditionSet, Set.mem_setOf_eq, u] using hcondition
    · intro hz
      let u : TimeControl p := (z, control0.2)
      obtain ⟨_, _, hupCondition⟩ := hsliceTransport u
      have hcondition : upKernelConditions selected0 hvalid i u.1 row := by
        simpa only [conditionSet, Set.mem_setOf_eq, u] using hz
      have hevent := hupCondition.mpr hcondition
      simpa only [upSet, Set.mem_setOf_eq, u] using hevent
  have hconditionMeas : MeasurableSet conditionSet := by
    let inputAt := fun z : ContinuousControlSlice.Slice p.m p.K =>
      releaseKernelInput selected0 hvalid z
    have hslot : Measurable (fun z : ContinuousControlSlice.Slice p.m p.K =>
        (inputAt z).slot) := by
      change Measurable (PublicDiscreteDraws.slotDraw :
        ContinuousControlSlice.Slice p.m p.K → PublicDiscreteDraws.Slot)
      exact PublicDiscreteDraws.measurable_slotDraw
    have hselectedMap : Measurable (fun z : ContinuousControlSlice.Slice p.m p.K =>
        (inputAt z).selected) := by
      change Measurable (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K)
      exact PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K
    have htuple : Measurable (fun z : ContinuousControlSlice.Slice p.m p.K =>
        (inputAt z).tuple.val (ActiveRoundActions.coordinator p.two_le_m)) := by
      change Measurable (fun z =>
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K z).val
          (ActiveRoundActions.coordinator p.two_le_m))
      exact (measurable_pi_apply (ActiveRoundActions.coordinator p.two_le_m)).comp
        (measurable_subtype_coe.comp
          (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K))
    let payload := selected0.view.payload
    let U := payload.slowSet
    have hfast : Measurable (fun z : ContinuousControlSlice.Slice p.m p.K =>
        (inputAt z).fast) := by
      change Measurable (fun z : ContinuousControlSlice.Slice p.m p.K =>
        (CanonicalFastSampling.sampleFast p rate.eta rate.eta.property
          payload.eta_le_source_cap payload.anchor
          (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0)
          payload.anchor_pos
          (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
            selected0 hvalid a).1)
          (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
            selected0 hvalid a).2.1)
          (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
            selected0 hvalid a).2.2)
          U (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast z)).1)
      exact measurable_subtype_coe.comp
        ((CanonicalFastSampling.measurable_sampleFast p rate.eta rate.eta.property
          payload.eta_le_source_cap payload.anchor
          (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0)
          payload.anchor_pos
          (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
            selected0 hvalid a).1)
          (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
            selected0 hvalid a).2.1)
          (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
            selected0 hvalid a).2.2)
          U).comp
          (ContinuousControlSlice.measurable_coordinate ContinuousControlSlice.Label.fast))
    have hslotSet : MeasurableSet {z : ContinuousControlSlice.Slice p.m p.K |
        (inputAt z).slot = PublicDiscreteDraws.upSlot} :=
      (measurableSet_singleton PublicDiscreteDraws.upSlot).preimage hslot
    have hselectedSet : MeasurableSet {z : ContinuousControlSlice.Slice p.m p.K |
        (inputAt z).selected = i} :=
      (measurableSet_singleton i).preimage hselectedMap
    have htupleSet : MeasurableSet {z : ContinuousControlSlice.Slice p.m p.K |
        (inputAt z).tuple.val (ActiveRoundActions.coordinator p.two_le_m) =
          selected0.view.payload.assignment.auxiliary} :=
      (measurableSet_singleton selected0.view.payload.assignment.auxiliary).preimage htuple
    have hfastSet : MeasurableSet {z : ContinuousControlSlice.Slice p.m p.K |
        (inputAt z).fast ≠ selected0.view.payload.assignment.auxiliary} :=
      ((measurableSet_singleton
        selected0.view.payload.assignment.auxiliary).preimage hfast).compl
    have hbase : MeasurableSet
        ({z : ContinuousControlSlice.Slice p.m p.K |
            (inputAt z).slot = PublicDiscreteDraws.upSlot} ∩
          ({z | (inputAt z).selected = i} ∩
            ({z | (inputAt z).tuple.val
              (ActiveRoundActions.coordinator p.two_le_m) =
                selected0.view.payload.assignment.auxiliary} ∩
              {z | (inputAt z).fast ≠
                selected0.view.payload.assignment.auxiliary}))) :=
      hslotSet.inter (hselectedSet.inter (htupleSet.inter hfastSet))
    by_cases hpos : 0 < row.val selected0.view.payload.assignment.auxiliary
    · have hset : conditionSet =
          ({z : ContinuousControlSlice.Slice p.m p.K |
              (inputAt z).slot = PublicDiscreteDraws.upSlot} ∩
            ({z | (inputAt z).selected = i} ∩
              ({z | (inputAt z).tuple.val
                (ActiveRoundActions.coordinator p.two_le_m) =
                  selected0.view.payload.assignment.auxiliary} ∩
                {z | (inputAt z).fast ≠
                  selected0.view.payload.assignment.auxiliary}))) := by
        ext z
        simp [conditionSet, upKernelConditions, upKernelConditionsData, inputAt,
          payload, U, hpos, releaseKernelInput, releaseKernelInputData,
          payloadCompleteCurrentWeights, ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
          ReleaseRoundKernel.releaseRoundInput]
      rw [hset]
      exact hbase
    · simp [conditionSet, upKernelConditions, upKernelConditionsData, inputAt,
        payload, U, hpos, releaseKernelInput, releaseKernelInputData,
        payloadCompleteCurrentWeights, ReferenceFirstLiveReleaseGeometry.completeCurrentWeights]
  have hEventMeas : MeasurableSet upSet := by
    rw [hconditionSet]
    exact hconditionMeas
  let payload := selected0.view.payload
  let a := payload.assignment
  let U := payload.slowSet
  let hU := payload.assignment_image.symm
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  let w := ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0
  let bounds := fun j =>
    ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected0 hvalid j
  have hm : 1 ≤ p.m := Nat.le_trans (by decide) p.two_le_m
  have hprobKernel := ReleaseRoundKernel.actual_up_release_probability p a snapshot row
    rate.eta rate.eta.property payload.eta_le_source_cap payload.anchor w
    payload.anchor_pos (fun j => (bounds j).1) (fun j => (bounds j).2.1)
    (fun j => (bounds j).2.2) U hU hmissing hstatus i hiState
  have hprob : (ContinuousControlSlice.sliceLaw p.m p.K) upSet =
      ENNReal.ofReal (upReleaseMassFormula selected0 hvalid row) := by
    simpa [upSet, snapshot, upKernelEvent, releaseKernelInput, releaseKernelInputData,
      payloadCompleteCurrentWeights, payloadSnapshot,
      ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot,
      ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
      completeCurrentWeights_eq_payload,
      upReleaseMassFormula, PublicDiscreteDraws.followerCount,
      payload, a, U, hU, row, w, bounds, Nat.cast_sub hm] using
        hprobKernel
  have hauxVal : (ReleaseRoundKernel.auxiliaryFastArm a U hU).1 =
      payload.auxiliaryArm := by
    change a.auxiliary = payload.auxiliaryArm
    rfl
  have hminimum : ∀ j : CanonicalFastSampling.FastArm U,
      payload.anchor (ReleaseRoundKernel.auxiliaryFastArm a U hU).1 ≤ payload.anchor j.1 := by
    intro j
    rw [hauxVal]
    exact payload.auxiliaryArm_anchor_minimum j.1 j.property
  have hlowerKernel := ReleaseRoundKernel.actual_up_release_probability_lower_bound
    p a snapshot row rate.eta rate.eta.property payload.eta_le_source_cap
    payload.anchor w payload.anchor_pos (fun j => (bounds j).1)
    (fun j => (bounds j).2.1) (fun j => (bounds j).2.2) U hU hmissing hstatus
    i hiState hminimum
  have hlower : ENNReal.ofReal
      (ReleaseRoundKernel.chi row a.auxiliary /
        (12 * (p.m - 1 : ℝ) * (p.K : ℝ))) ≤
      (ContinuousControlSlice.sliceLaw p.m p.K) upSet := by
    simpa [upSet, snapshot, upKernelEvent, releaseKernelInput, releaseKernelInputData,
      payloadCompleteCurrentWeights, payloadSnapshot,
      ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot,
      ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
      completeCurrentWeights_eq_payload,
      PublicDiscreteDraws.followerCount, payload, a, U, hU, row, w, bounds,
      Nat.cast_sub hm] using hlowerKernel
  have hmeasure : ContinuousLearningRows.timeControlLaw p
        (retainedUpFlagEvent rewards C_star C_h q t s hs control0 x hn selected0 i) =
      (ContinuousControlSlice.sliceLaw p.m p.K) upSet := by
    calc
      _ = ContinuousLearningRows.timeControlLaw p (Prod.fst ⁻¹' upSet) := by
        rw [hflagSet]
      _ = (ContinuousLearningRows.timeControlLaw p).map Prod.fst upSet :=
        (Measure.map_apply measurable_fst hEventMeas).symm
      _ = (ContinuousControlSlice.sliceLaw p.m p.K) upSet := by
        rw [ContinuousLearningRows.map_slice p]
  refine ⟨hvalid, ?_, ?_⟩
  · calc
      _ = (ContinuousControlSlice.sliceLaw p.m p.K) upSet := hmeasure
      _ = ENNReal.ofReal (upReleaseMassFormula selected0 hvalid row) := hprob
  · calc
      _ ≤ (ContinuousControlSlice.sliceLaw p.m p.K) upSet := hlower
      _ = _ := hmeasure.symm

private theorem retained_data_release_measure
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0)
    (hn : t.val - s <
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0).length)
    (selected0 : Selection (p := p) (rate := rate)
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].input)
    (hselected :
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].output.preparation.coordinator.selection =
        some selected0)
    (hempty : selected0.view.pendingAtChoice = ∅)
    (i : Fin (p.m - 1))
    (hi : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart
      selected0.view.payload
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).time
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state) :
    ContinuousLearningRows.timeControlLaw p
        (retainedDataFlagEvent rewards C_star C_h q t s hs control0 x hn selected0 i) =
      ENNReal.ofReal
        (ReleaseRoundKernel.chi
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          (selected0.view.payload.assignment.assigned i) /
          (2 * (p.K : ℝ))) := by
  let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 x
  let n := t.val - s
  let payload := selected0.view.payload
  let a := payload.assignment
  let U := payload.slowSet
  let hU := payload.assignment_image.symm
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  obtain ⟨hvalid, states, memories, hfields, hpendingStatus,
      hcontrols⟩ := retained_first_live_release_all_controls
        rewards C_star C_h q t s hs control0 x hn selected0 hselected hempty i hi
  let snapshot := ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected0 states
  have hmissing : snapshot.missing = ∅ := by
    change selected0.view.pendingAtChoice = ∅
    exact hempty
  have hstatus : ∀ j, snapshot.status j = .pending ∨ snapshot.status j = .released := by
    intro j
    change (states j).status = .pending ∨ (states j).status = .released
    cases hstate : (states j).status with
    | unoccupied => exact False.elim ((hfields j).1 hstate)
    | pending => exact Or.inl rfl
    | released => exact Or.inr rfl
  have hiState : (states i).status = .pending := (hpendingStatus i).mp hi
  have hsliceTransport (u : TimeControl p) :
      ∃ hwindow : n <
          (ReferenceFirstLiveReleaseControlTransport.retainedWindow
            rewards C_star C_h q t s hs control0 x u).length,
        (ReferencePhysicalReleaseQuota.dataFlag selected0.view.payload
            ((ReferenceFirstLiveReleaseControlTransport.retainedWindow
              rewards C_star C_h q t s hs control0 x u)[n]'hwindow) i = true ↔
          dataKernelEvent selected0 hvalid states row i u.1) ∧
        (dataKernelEvent selected0 hvalid states row i u.1 ↔
          dataKernelConditions selected0 hvalid i u.1 row) := by
    rcases hcontrols u with ⟨hwindow, selectedU, _hinput, _hcut, _hordinary,
        _hselected, _houtput, _hpayload, _hpending, _hcutoff, _hweights,
        _hquery, _hupFlag, hdataFlag, _hupCondition, hdataCondition⟩
    exact ⟨hwindow, hdataFlag, hdataCondition⟩
  let dataSet : Set (ContinuousControlSlice.Slice p.m p.K) :=
    {z | dataKernelEvent selected0 hvalid states row i z}
  have hflagSet : retainedDataFlagEvent rewards C_star C_h q t s hs control0
      x hn selected0 i = Prod.fst ⁻¹' dataSet := by
    ext u
    change (∃ hwindow : n <
        (ReferenceFirstLiveReleaseControlTransport.retainedWindow
          rewards C_star C_h q t s hs control0 x u).length,
        ReferencePhysicalReleaseQuota.dataFlag selected0.view.payload
          ((ReferenceFirstLiveReleaseControlTransport.retainedWindow
            rewards C_star C_h q t s hs control0 x u)[n]'hwindow) i = true) ↔
      u.1 ∈ dataSet
    constructor
    · rintro ⟨hwindow, hflag⟩
      obtain ⟨hwindow', hiff, _⟩ := hsliceTransport u
      have hproof : hwindow = hwindow' := Subsingleton.elim _ _
      subst hwindow
      have hevent := hiff.mp hflag
      simpa only [dataSet, Set.mem_setOf_eq] using hevent
    · intro hu
      obtain ⟨hwindow, hiff, _⟩ := hsliceTransport u
      have hevent : dataKernelEvent selected0 hvalid states row i u.1 := by
        simpa only [dataSet, Set.mem_setOf_eq] using hu
      exact ⟨hwindow, hiff.mpr hevent⟩
  let conditionSet : Set (ContinuousControlSlice.Slice p.m p.K) :=
    {z | dataKernelConditions selected0 hvalid i z row}
  have hconditionSet : dataSet = conditionSet := by
    ext z
    constructor
    · intro hz
      let u : TimeControl p := (z, control0.2)
      obtain ⟨_, _, hcondition⟩ := hsliceTransport u
      have hevent : dataKernelEvent selected0 hvalid states row i u.1 := by
        simpa only [dataSet, Set.mem_setOf_eq, u] using hz
      have hcondition' := hcondition.mp hevent
      simpa only [conditionSet, Set.mem_setOf_eq, u] using hcondition'
    · intro hz
      let u : TimeControl p := (z, control0.2)
      obtain ⟨_, _, hcondition⟩ := hsliceTransport u
      have hcondition' : dataKernelConditions selected0 hvalid i u.1 row := by
        simpa only [conditionSet, Set.mem_setOf_eq, u] using hz
      have hevent := hcondition.mpr hcondition'
      simpa only [dataSet, Set.mem_setOf_eq, u] using hevent
  have hconditionMeas : MeasurableSet conditionSet := by
    let inputAt := fun z : ContinuousControlSlice.Slice p.m p.K =>
      releaseKernelInput selected0 hvalid z
    have hslot : Measurable (fun z : ContinuousControlSlice.Slice p.m p.K =>
        (inputAt z).slot) := by
      change Measurable (PublicDiscreteDraws.slotDraw :
        ContinuousControlSlice.Slice p.m p.K → PublicDiscreteDraws.Slot)
      exact PublicDiscreteDraws.measurable_slotDraw
    have hpilot : Measurable (fun z : ContinuousControlSlice.Slice p.m p.K =>
        (inputAt z).pilots (ActiveRoundActions.coordinator p.two_le_m)) := by
      change Measurable (PublicDiscreteDraws.pilotDraw (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m))
      exact PublicDiscreteDraws.measurable_pilotDraw (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m)
    have hslotSet : MeasurableSet {z : ContinuousControlSlice.Slice p.m p.K |
        (inputAt z).slot = PublicDiscreteDraws.dataSlot} :=
      (measurableSet_singleton PublicDiscreteDraws.dataSlot).preimage hslot
    have hpilotSet : MeasurableSet {z : ContinuousControlSlice.Slice p.m p.K |
        (inputAt z).pilots (ActiveRoundActions.coordinator p.two_le_m) =
          selected0.view.payload.assignment.assigned i} :=
      (measurableSet_singleton
        (selected0.view.payload.assignment.assigned i)).preimage hpilot
    have hbase : MeasurableSet
        ({z : ContinuousControlSlice.Slice p.m p.K |
            (inputAt z).slot = PublicDiscreteDraws.dataSlot} ∩
          {z | (inputAt z).pilots (ActiveRoundActions.coordinator p.two_le_m) =
            selected0.view.payload.assignment.assigned i}) := hslotSet.inter hpilotSet
    by_cases hpos : 0 < row.val (selected0.view.payload.assignment.assigned i)
    · have hset : conditionSet =
          ({z : ContinuousControlSlice.Slice p.m p.K |
              (inputAt z).slot = PublicDiscreteDraws.dataSlot} ∩
            {z | (inputAt z).pilots (ActiveRoundActions.coordinator p.two_le_m) =
              selected0.view.payload.assignment.assigned i}) := by
        ext z
        simp [conditionSet, dataKernelConditions, dataKernelConditionsData, inputAt,
          hpos, releaseKernelInput, releaseKernelInputData,
          payloadCompleteCurrentWeights, ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
          ReleaseRoundKernel.releaseRoundInput]
      rw [hset]
      exact hbase
    · simp [conditionSet, dataKernelConditions, dataKernelConditionsData, inputAt,
        hpos, releaseKernelInput, releaseKernelInputData,
        payloadCompleteCurrentWeights, ReferenceFirstLiveReleaseGeometry.completeCurrentWeights]
  have hEventMeas : MeasurableSet dataSet := by
    rw [hconditionSet]
    exact hconditionMeas
  let w := ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0
  let bounds := fun j =>
    ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected0 hvalid j
  have hprobKernel := ReleaseRoundKernel.actual_data_release_probability p a snapshot row
    rate.eta rate.eta.property payload.eta_le_source_cap payload.anchor w
    payload.anchor_pos (fun j => (bounds j).1) (fun j => (bounds j).2.1)
    (fun j => (bounds j).2.2) U hU hmissing hstatus i hiState
  have hprob : (ContinuousControlSlice.sliceLaw p.m p.K) dataSet =
      ENNReal.ofReal
        (ReleaseRoundKernel.chi row (a.assigned i) / (2 * (p.K : ℝ))) := by
    simpa [dataSet, snapshot, dataKernelEvent, releaseKernelInput, releaseKernelInputData,
      payloadCompleteCurrentWeights, payloadSnapshot,
      ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot,
      ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
      completeCurrentWeights_eq_payload,
      PublicDiscreteDraws.followerCount, payload, a, U, hU, row, w, bounds] using
        hprobKernel
  have hmeasure : ContinuousLearningRows.timeControlLaw p
        (retainedDataFlagEvent rewards C_star C_h q t s hs control0 x hn selected0 i) =
      (ContinuousControlSlice.sliceLaw p.m p.K) dataSet := by
    calc
      _ = ContinuousLearningRows.timeControlLaw p (Prod.fst ⁻¹' dataSet) := by
        rw [hflagSet]
      _ = (ContinuousLearningRows.timeControlLaw p).map Prod.fst dataSet :=
        (Measure.map_apply measurable_fst hEventMeas).symm
      _ = (ContinuousControlSlice.sliceLaw p.m p.K) dataSet := by
        rw [ContinuousLearningRows.map_slice p]
  calc
    _ = (ContinuousControlSlice.sliceLaw p.m p.K) dataSet := hmeasure
    _ = ENNReal.ofReal
        (ReleaseRoundKernel.chi row (a.assigned i) / (2 * (p.K : ℝ))) := hprob

/-- Exact UP mass of the actual physical flag on the whole `TimeControl`
carrier. The validity proof is returned from the computed selected-empty
branch, rather than supplied as a premise. The exposed `upReleaseMassFormula`
expands to `chi_t(e) * (1-qGamma(v,w,U,e)) / (4*(m-1)*K)`. -/
theorem retained_up_release_mass
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0)
    (hn : t.val - s <
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0).length)
    (selected0 : Selection (p := p) (rate := rate)
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].input)
    (hselected :
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].output.preparation.coordinator.selection =
        some selected0)
    (hempty : selected0.view.pendingAtChoice = ∅)
    (i : Fin (p.m - 1))
    (hi : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart
      selected0.view.payload
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).time
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state) :
    ∃ hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected0.view.payload
      selected0.view.cutoff
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].input.time
      selected0.view.complementWeights,
      ContinuousLearningRows.timeControlLaw p
          (retainedUpFlagEvent rewards C_star C_h q t s hs control0 x hn selected0 i) =
        ENNReal.ofReal (upReleaseMassFormula selected0 hvalid
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)) := by
  obtain ⟨hvalid, hmass, _hlower⟩ := retained_up_release_measure_results
    rewards C_star C_h q t s hs control0 x hn selected0 hselected hempty i hi
  exact ⟨hvalid, hmass⟩

/-- The actual UP flag's uniform conditional slice lower bound. The pending
premise is the literal baseline `pendingAtStart` query. -/
theorem retained_up_release_mass_lower_bound
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0)
    (hn : t.val - s <
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0).length)
    (selected0 : Selection (p := p) (rate := rate)
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].input)
    (hselected :
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].output.preparation.coordinator.selection =
        some selected0)
    (hempty : selected0.view.pendingAtChoice = ∅)
    (i : Fin (p.m - 1))
    (hi : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart
      selected0.view.payload
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).time
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state) :
    ENNReal.ofReal
        (ReleaseRoundKernel.chi
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          selected0.view.payload.assignment.auxiliary /
          (12 * (p.m - 1 : ℝ) * (p.K : ℝ))) ≤
      ContinuousLearningRows.timeControlLaw p
        (retainedUpFlagEvent rewards C_star C_h q t s hs control0 x hn selected0 i) :=
  (retained_up_release_measure_results rewards C_star C_h q t s hs control0
    x hn selected0 hselected hempty i hi).2.2

/-- Exact DATA mass of the actual physical flag on the whole `TimeControl`
carrier. Its event uses only the DATA slot, coordinator pilot, and positive
own reward; it has no recording mask or thinning condition. -/
theorem retained_data_release_mass
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart (p := p) (rate := rate)
      rewards C_star C_h q t s hs control0)
    (hn : t.val - s <
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0).length)
    (selected0 : Selection (p := p) (rate := rate)
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].input)
    (hselected :
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s].output.preparation.coordinator.selection =
        some selected0)
    (hempty : selected0.view.pendingAtChoice = ∅)
    (i : Fin (p.m - 1))
    (hi : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart
      selected0.view.payload
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).time
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state) :
    ContinuousLearningRows.timeControlLaw p
        (retainedDataFlagEvent rewards C_star C_h q t s hs control0 x hn selected0 i) =
      ENNReal.ofReal
        (ReleaseRoundKernel.chi
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          (selected0.view.payload.assignment.assigned i) /
          (2 * (p.K : ℝ))) :=
  retained_data_release_measure rewards C_star C_h q t s hs control0
    x hn selected0 hselected hempty i hi

end Bandits.Support.ReferenceFirstLiveReleaseSliceMass

end
