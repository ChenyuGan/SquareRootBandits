/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFastErasure
public import Bandits.Support.ReferenceFirstCollectionWeightEnvelope
public import Bandits.Support.ReferenceSourceFastScalarDisintegration
public import Bandits.Support.ReferenceFirstLiveCalendarMarkedTransition

/-!
# One actual first-collection logical update

The incoming slow set is an ordinary argument. Numerical data come from the
literal optional observations of the same physical source, starting at zero.
The FAST scalar is the original current coordinate; label zero is retained
and label one supplies the fresh residual draw. No chronological construction
of the incoming set or manuscript closure is asserted.

Sources: `06_interruptions.tex:376-426`, `04_slow_fast_learner.tex:142-215,323-390`,
and `appendix_a_local_protocol.tex:28-79` in `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstLiveChronologicalPrefixFoundation
open Bandits.Support.ReferenceFirstLiveChronologicalPrefixMeasurability

namespace Bandits.Support.ReferenceFirstCollectionOneRoundLogicalCell

open ReferenceFirstLaunchNumericalCell (queueParameters)
open ReferenceFirstCollectionCurrentRetainedGate (pastCells? cell0)
open ReferenceSourcePrefixHistoryFiltration (actualRecord)
open ReferenceActiveHorizonMeasurability (roundRecordCode)
open ReferenceFirstLiveConfirmationHistory (firstLiveWindow)
open ReferenceCollectionPhaseHistory (collectionWindow)
open ReferenceCompletePhysicalHistory (completeSuffixRecords)
open ReferenceFirstCollectionFastErasure (insertCurrentFastScalar)

variable {p : ConstructorDimensions.Parameters} {rate : RateInput p}

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Option α) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance cutoffMeasurableSpace : MeasurableSpace (Option (CoordinatorLocalArmChoice.Cutoff p)) := ⊤

/-- The actual first physical collection window, without a bound on its length. -/
def firstCollection (rewards : RewardTable p) (C_star C_h : ℝ) (z : SourceInput p) :
    List (Record rate) :=
  collectionWindow (completeSuffixRecords rate z rewards C_star C_h)
    (firstLiveWindow (completeSuffixRecords rate z rewards C_star C_h)).length

section Actual

variable (rewards : RewardTable p) (C_star C_h : ℝ) (z : SourceInput p) (t : Fin p.T)
  (r : Record rate)
  (hr : actualRecord rate rewards C_star C_h t z = some r)
  (hm : r ∈ firstCollection (rate := rate) rewards C_star C_h z)

include hr hm

/-- Presence is obtained from the actual collection envelope producer. -/
theorem actual_options_present :
    (pastCells? rate rewards C_star C_h t z).isSome = true ∧
      (cell0 rate r).isSome = true := by
  obtain ⟨L, c, call, hL, _, _, hc, _⟩ :=
    ReferenceFirstCollectionWeightEnvelope.actual_first_collection_weight_envelope
      rewards C_star C_h z t r hr hm
  rw [hL, hc]
  exact ⟨rfl, rfl⟩

/-- The zero-origin prefix is extracted from the existing option, with no default. -/
def actualPast : List (RecordedQueueRun.RoundInput p.K) :=
  (pastCells? rate rewards C_star C_h t z).get
    (actual_options_present rewards C_star C_h z t r hr hm).1

/-- The complete actual numerical input, including its reward and rate vectors. -/
def actualInput : RecordedQueueRun.RoundInput p.K :=
  (cell0 rate r).get (actual_options_present rewards C_star C_h z t r hr hm).2

theorem actualPast_spec : pastCells? rate rewards C_star C_h t z =
    some (actualPast rewards C_star C_h z t r hr hm) :=
  (Option.some_get _).symm

theorem actualInput_spec : cell0 rate r =
    some (actualInput rewards C_star C_h z t r hr hm) :=
  (Option.some_get _).symm

/-- The full stopped weight vector is evaluated at the actual zero-origin PRE state. -/
def actualWeight (a : Fin p.K) : ℝ :=
  RecordedQueueRun.scoreWeight (queueParameters rate)
    (RecordedQueueRun.run (queueParameters rate)
      (actualPast rewards C_star C_h z t r hr hm)) a

/-- The actual call, old unit anchor, canonical rates, enabled flag, and all-arm
bounds are conclusions, rather than premises supplied to the logical operation. -/
theorem actual_data :
    ∃ call : ReferenceCollectionSegmentExtraction.Choice rate,
      r.input.time = t ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r =
        some (actualInput rewards C_star C_h z t r hr hm) ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r =
        some ⟨call.payload, call.preLedger, call.started, call.weights⟩ ∧
      call.payload.anchor = (fun _ => 1) ∧
      (actualInput rewards C_star C_h z t r hr hm).rate = call.payload.rate ∧
      call.payload.rate = CanonicalRecordingRates.xi p rate.eta.val call.payload.anchor ∧
      (actualInput rewards C_star C_h z t r hr hm).enabled =
        decide (t.val + 1 < call.started.clock.g) ∧
      ∀ a, 0 < actualWeight rewards C_star C_h z t r hr hm a ∧
        1 ≤ actualWeight rewards C_star C_h z t r hr hm a ∧
        actualWeight rewards C_star C_h z t r hr hm a ≤ 2 := by
  obtain ⟨L, c, call, hL, _, ht, hc, hread, hcall, hanchor, hrate, hcanonical,
    henabled, hbounds, _⟩ :=
    ReferenceFirstCollectionWeightEnvelope.actual_first_collection_weight_envelope
      rewards C_star C_h z t r hr hm
  have hLeq : L = actualPast rewards C_star C_h z t r hr hm :=
    Option.some.inj (hL.symm.trans (actualPast_spec rewards C_star C_h z t r hr hm))
  have hceq : c = actualInput rewards C_star C_h z t r hr hm :=
    Option.some.inj (hc.symm.trans (actualInput_spec rewards C_star C_h z t r hr hm))
  subst L
  subst c
  refine ⟨call, ht, hread, hcall, hanchor, hrate, hcanonical, henabled, ?_⟩
  intro a
  have h := hbounds a
  rw [hanchor] at h
  exact ⟨h.2.1, h.2.2.1, by simpa only [actualWeight, mul_one] using h.2.2.2⟩

theorem actual_weight_bounds (a : Fin p.K) :
    0 < actualWeight rewards C_star C_h z t r hr hm a ∧
      1 ≤ actualWeight rewards C_star C_h z t r hr hm a ∧
      actualWeight rewards C_star C_h z t r hr hm a ≤ 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, h⟩ := actual_data rewards C_star C_h z t r hr hm
  exact h a

/-- The canonical fast sampler on the arbitrary incoming complement. -/
def actualFast (U : SlowSet p) (f : ContinuousControlSlice.Scalar) :
    CanonicalFastSampling.FastArm U :=
  CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
    (fun _ => 1) (actualWeight rewards C_star C_h z t r hr hm)
    (fun _ => zero_lt_one)
    (fun a => (actual_weight_bounds rewards C_star C_h z t r hr hm a).1)
    (fun a => (actual_weight_bounds rewards C_star C_h z t r hr hm a).2.1)
    (fun a => by simpa only [mul_one] using
      (actual_weight_bounds rewards C_star C_h z t r hr hm a).2.2) U f

/-- Replace only the next slow set, retaining the full before-refresh cell. -/
def cellWithNext (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (f : ContinuousControlSlice.Scalar) (V : SlowSet p) : LogicalCell p rate :=
  let c := actualInput rewards C_star C_h z t r hr hm
  let S := RecordedQueueRun.run (queueParameters rate)
    (actualPast rewards C_star C_h z t r hr hm)
  let proposed := c.enabled && !S.overflow && decide ((a0 t).val < 4 * p.m * rate.eta.val)
  { time := t
    physical := roundRecordCode r
    numerical := (c.enabled, (c.recordedArm, (c.reward, c.rate)))
    before := S
    after := RecordedQueueRun.step (queueParameters rate) S c
    arrivals := RecordedQueueRun.acceptedRecord (queueParameters rate) S c
    service := fun a => RecordedQueueRun.recordService (4 * (queueParameters rate).n)
      (S.registers a) (RecordedQueueRun.acceptedRecord (queueParameters rate) S c a)
    slowSet := if S.overflow then frozenSlowSet p else U
    fastArm := if S.overflow then frozenFastArm p else
      (actualFast rewards C_star C_h z t r hr hm U f).val
    proposal := proposed
    nextSlowSet := V }

/-- Literal residual outcome. Disabled dates have no proposal; incoming
overflow uses the prescribed fixed continuation. -/
def nextSet (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (x : ContinuousControlSlice.Scalar) : SlowSet p :=
  let c := actualInput rewards C_star C_h z t r hr hm
  let S := RecordedQueueRun.run (queueParameters rate)
    (actualPast rewards C_star C_h z t r hr hm)
  if S.overflow then frozenSlowSet p else
    if c.enabled && !S.overflow && decide ((a0 t).val < 4 * p.m * rate.eta.val) then
      residualDraw rate S c (fun _ => 1) (fun _ => zero_lt_one) x else U

/-- Complete cell before the enabled/absent calendar filter. Only PRE overflow
suppresses learning; the entire first detecting update and refresh remain. -/
def cellWithScalar (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (f x : ContinuousControlSlice.Scalar) : LogicalCell p rate :=
  cellWithNext rewards C_star C_h z t r hr hm U a0 f
    (nextSet rewards C_star C_h z t r hr hm U a0 x)

/-- The optional logical cell: disabled physical dates append nothing. -/
def cellWithScalar? (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (f x : ContinuousControlSlice.Scalar) : Option (LogicalCell p rate) :=
  if (actualInput rewards C_star C_h z t r hr hm).enabled then
    some (cellWithScalar rewards C_star C_h z t r hr hm U a0 f x)
  else none

/-- The actual local operation uses the same current FAST scalar from the
complete original source. The whole label-zero array remains an argument. -/
def collectionLogicalCellAt (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) (x : ContinuousControlSlice.Scalar) :
    Option (LogicalCell p rate) :=
  cellWithScalar? rewards C_star C_h z t r hr hm U a0
    (ReferenceSourceFastScalarDisintegration.sourceFastScalar p t z) x

/-- Changing the fresh residual scalar retains every before-refresh field. -/
theorem beforeRefreshFields_eq (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) (f x y : ContinuousControlSlice.Scalar) :
    (cellWithScalar rewards C_star C_h z t r hr hm U a0 f x).beforeRefreshFields =
      (cellWithScalar rewards C_star C_h z t r hr hm U a0 f y).beforeRefreshFields := rfl

/-- Disabled dates have genuine absence, even with incoming overflow. -/
theorem cellWithScalar?_disabled (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) (f x : ContinuousControlSlice.Scalar)
    (hc : (actualInput rewards C_star C_h z t r hr hm).enabled = false) :
    cellWithScalar? rewards C_star C_h z t r hr hm U a0 f x = none := by
  simp only [cellWithScalar?, hc, Bool.false_eq_true, ite_false]

/-- On enabled dates the complete update is present, regardless of POST overflow. -/
theorem cellWithScalar?_enabled (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) (f x : ContinuousControlSlice.Scalar)
    (hc : (actualInput rewards C_star C_h z t r hr hm).enabled = true) :
    cellWithScalar? rewards C_star C_h z t r hr hm U a0 f x =
      some (cellWithScalar rewards C_star C_h z t r hr hm U a0 f x) := by
  simp only [cellWithScalar?, hc, ite_true]

/-- Explicit refresh measure. It is the existing residual PMF on proposals,
with the disabled, retained-set and incoming-overflow Dirac branches. -/
def refreshMeasure (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar) :
    Measure (SlowSet p) :=
  let c := actualInput rewards C_star C_h z t r hr hm
  let S := RecordedQueueRun.run (queueParameters rate)
    (actualPast rewards C_star C_h z t r hr hm)
  if c.enabled then
    if S.overflow then Measure.dirac (frozenSlowSet p) else
      if decide ((a0 t).val < 4 * p.m * rate.eta.val) then
        (RecordedSlowRefresh.residualPMF p (queueParameters rate) S c
          (fun _ => 1) (fun _ => zero_lt_one)).toMeasure
      else Measure.dirac U
  else Measure.dirac U

/-- Reconstruction changes only the final field. -/
theorem cellWithNext_beforeRefresh (U V : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) (f x : ContinuousControlSlice.Scalar) :
    (cellWithNext rewards C_star C_h z t r hr hm U a0 f V).beforeRefreshFields =
      (cellWithScalar rewards C_star C_h z t r hr hm U a0 f x).beforeRefreshFields := rfl

/-- The full numerical update and every physical code coordinate are retained. -/
theorem cell_fields (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (f x : ContinuousControlSlice.Scalar) :
    let e := cellWithScalar rewards C_star C_h z t r hr hm U a0 f x
    let c := actualInput rewards C_star C_h z t r hr hm
    let S := RecordedQueueRun.run (queueParameters rate)
      (actualPast rewards C_star C_h z t r hr hm)
    e.time = t ∧ e.physical = roundRecordCode r ∧
      e.numerical = (c.enabled, (c.recordedArm, (c.reward, c.rate))) ∧
      e.before = S ∧ e.after = RecordedQueueRun.step (queueParameters rate) S c ∧
      e.arrivals = RecordedQueueRun.acceptedRecord (queueParameters rate) S c ∧
      e.service = (fun a => RecordedQueueRun.recordService (4 * (queueParameters rate).n)
        (S.registers a) (RecordedQueueRun.acceptedRecord (queueParameters rate) S c a)) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Incoming overflow has no logical arrivals, service, proposal or refresh.
The actual physical output is still retained by `cell_fields`. -/
theorem cell_after_overflow (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) (f x : ContinuousControlSlice.Scalar)
    (hs : (RecordedQueueRun.run (queueParameters rate)
      (actualPast rewards C_star C_h z t r hr hm)).overflow = true) :
    let e := cellWithScalar rewards C_star C_h z t r hr hm U a0 f x
    e.slowSet = frozenSlowSet p ∧ e.fastArm = frozenFastArm p ∧
      e.proposal = false ∧ e.nextSlowSet = frozenSlowSet p ∧
      (∀ a, e.arrivals a = (false, 0) ∧ e.service a = 0 ∧
        e.after.registers a = e.before.registers a) := by
  dsimp only [cellWithScalar, cellWithNext, nextSet]
  simp only [hs, ite_true, Bool.not_true, Bool.and_false, Bool.false_and]
  refine ⟨True.intro, True.intro, True.intro, True.intro, ?_⟩
  intro a
  have ha := RecordedQueueRun.step_after_overflow_preserves (queueParameters rate)
    (RecordedQueueRun.run (queueParameters rate) (actualPast rewards C_star C_h z t r hr hm))
    (actualInput rewards C_star C_h z t r hr hm) hs a
  exact ⟨ha.2, by rw [ha.2]; rfl, ha.1⟩

/-- Disabled dates preserve numerical registers while their physical calendar
continues. Enabled zero arrivals instead remain enabled queue records. -/
theorem disabled_registers (hc : (actualInput rewards C_star C_h z t r hr hm).enabled = false)
    (a : Fin p.K) :
    (RecordedQueueRun.step (queueParameters rate)
      (RecordedQueueRun.run (queueParameters rate) (actualPast rewards C_star C_h z t r hr hm))
      (actualInput rewards C_star C_h z t r hr hm)).registers a =
    (RecordedQueueRun.run (queueParameters rate)
      (actualPast rewards C_star C_h z t r hr hm)).registers a :=
  (RecordedQueueRun.step_disabled_preserves _ _ _ hc a).1

/-- The residual inverse-CDF map is Borel, using the public actual PRE/POST API. -/
theorem measurable_nextSet (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) :
    Measurable (nextSet rewards C_star C_h z t r hr hm U a0) := by
  let c := actualInput rewards C_star C_h z t r hr hm
  let S := RecordedQueueRun.run (queueParameters rate)
    (actualPast rewards C_star C_h z t r hr hm)
  have hres : Measurable (residualDraw rate S c (fun _ => 1) (fun _ => zero_lt_one)) :=
    (measurable_residualDraw_of_actualPrePost rate (fun _ => S)
      (fun _ => RecordedQueueRun.step (queueParameters rate) S c) (fun _ => c)
      measurable_const measurable_const (fun _ => rfl) (fun _ _ => 1)
      measurable_const (fun _ _ => zero_lt_one) id measurable_id).mono le_rfl le_top
  unfold nextSet
  dsimp only
  split
  · exact measurable_const
  · split
    · exact hres
    · exact measurable_const

/-- Canonical FAST sampling on the real continuous scalar carrier. -/
theorem measurable_actualFast (U : SlowSet p) :
    Measurable (actualFast rewards C_star C_h z t r hr hm U) :=
  CanonicalFastSampling.measurable_sampleFast p rate.eta.val rate.eta.property rate.sourceCap
    _ _ _ _ _ _ U

/-- The full cell reconstruction is Borel in the original product-code space. -/
theorem measurable_cellWithNext (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) :
    Measurable (fun v : ContinuousControlSlice.Scalar × SlowSet p =>
      cellWithNext rewards C_star C_h z t r hr hm U a0 v.1 v.2) := by
  have hf : Measurable (fun v : ContinuousControlSlice.Scalar × SlowSet p =>
      if (RecordedQueueRun.run (queueParameters rate)
        (actualPast rewards C_star C_h z t r hr hm)).overflow then frozenFastArm p else
        (actualFast rewards C_star C_h z t r hr hm U v.1).val) := by
    split
    · exact measurable_const
    · exact measurable_subtype_coe.comp ((measurable_actualFast rewards C_star C_h z t r hr hm U).comp
        measurable_fst)
  have hV : @Measurable _ (SlowSet p) _ ⊤ (fun v : ContinuousControlSlice.Scalar × SlowSet p => v.2) := by
    intro A _
    exact (MeasurableSet.of_discrete (s := A)).preimage measurable_snd
  apply measurable_comap_iff.mpr
  exact measurable_const.prodMk (measurable_const.prodMk
    (measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk
      (measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk
        (hf.prodMk (measurable_const.prodMk hV)))))))))

/-- All fields of the local two-scalar cell are Borel, including overflow. -/
theorem measurable_cellWithScalar (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) :
    Measurable (fun v : ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar =>
      cellWithScalar rewards C_star C_h z t r hr hm U a0 v.1 v.2) := by
  change Measurable ((fun v : ContinuousControlSlice.Scalar × SlowSet p =>
    cellWithNext rewards C_star C_h z t r hr hm U a0 v.1 v.2) ∘
      (fun v : ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar =>
        (v.1, nextSet rewards C_star C_h z t r hr hm U a0 v.2)))
  apply (measurable_cellWithNext rewards C_star C_h z t r hr hm U a0).comp
  exact measurable_fst.prodMk
    ((measurable_nextSet rewards C_star C_h z t r hr hm U a0).comp measurable_snd)

/-- The enabled filter preserves Borelness and genuine absence. -/
theorem measurable_cellWithScalar? (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) :
    Measurable (fun v : ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar =>
      cellWithScalar? rewards C_star C_h z t r hr hm U a0 v.1 v.2) := by
  unfold cellWithScalar?
  split
  · exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      (measurable_cellWithScalar rewards C_star C_h z t r hr hm U a0)
  · exact measurable_const

/-- The actual fast marginal is the genuine canonical qGamma PMF. -/
theorem actualFast_map (U : SlowSet p) :
    ContinuousControlSlice.scalarLaw.map (actualFast rewards C_star C_h z t r hr hm U) =
      (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
        (fun _ => 1) (actualWeight rewards C_star C_h z t r hr hm)
        (fun _ => zero_lt_one)
        (fun a => (actual_weight_bounds rewards C_star C_h z t r hr hm a).1)
        (fun a => (actual_weight_bounds rewards C_star C_h z t r hr hm a).2.1)
        (fun a => by simpa only [mul_one] using
          (actual_weight_bounds rewards C_star C_h z t r hr hm a).2.2) U).toMeasure :=
  CanonicalFastSampling.uniform_map_sampleFast p rate.eta.val rate.eta.property rate.sourceCap
    _ _ _ _ _ _ U

/-- The explicit refresh measure is the law of the literal residual outcome
on enabled dates, with the overflow and no-proposal branches included. -/
theorem nextSet_map (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (hc : (actualInput rewards C_star C_h z t r hr hm).enabled = true) :
    ContinuousControlSlice.scalarLaw.map (nextSet rewards C_star C_h z t r hr hm U a0) =
      refreshMeasure rewards C_star C_h z t r hr hm U a0 := by
  unfold nextSet refreshMeasure
  simp only [hc, ite_true, Bool.true_and]
  cases hs : (RecordedQueueRun.run (queueParameters rate)
      (actualPast rewards C_star C_h z t r hr hm)).overflow with
  | true => simp only [ite_true, Measure.map_const, measure_univ, one_smul]
  | false =>
    simp only [Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_and]
    split
    · exact ReferenceFirstLiveCalendarMarkedTransition.residualDraw_map rate _ _ _ _
    · simp only [Measure.map_const, measure_univ, one_smul]

/-- Optional reconstruction replaces only `nextSlowSet` of present cells. -/
def cellWithNext? (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (f : ContinuousControlSlice.Scalar) (V : SlowSet p) : Option (LogicalCell p rate) :=
  if (actualInput rewards C_star C_h z t r hr hm).enabled then
    some (cellWithNext rewards C_star C_h z t r hr hm U a0 f V) else none

theorem measurable_cellWithNext? (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) :
    Measurable (fun v : ContinuousControlSlice.Scalar × SlowSet p =>
      cellWithNext? rewards C_star C_h z t r hr hm U a0 v.1 v.2) := by
  unfold cellWithNext?
  split
  · exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      (measurable_cellWithNext rewards C_star C_h z t r hr hm U a0)
  · exact measurable_const

/-- The full optional cell law for each fixed FAST scalar. This includes
absent disabled dates and the prescribed incoming-overflow continuation. -/
theorem cell_refresh_map (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (f : ContinuousControlSlice.Scalar) :
    ContinuousControlSlice.scalarLaw.map
        (cellWithScalar? rewards C_star C_h z t r hr hm U a0 f) =
      (refreshMeasure rewards C_star C_h z t r hr hm U a0).map
        (cellWithNext? rewards C_star C_h z t r hr hm U a0 f) := by
  have he : Measurable (cellWithNext? rewards C_star C_h z t r hr hm U a0 f) :=
    measurable_of_countable _
  cases hc : (actualInput rewards C_star C_h z t r hr hm).enabled with
  | false =>
    have hleft : cellWithScalar? rewards C_star C_h z t r hr hm U a0 f =
        fun _ => none := funext fun x =>
      cellWithScalar?_disabled rewards C_star C_h z t r hr hm U a0 f x hc
    rw [hleft, refreshMeasure]
    simp only [hc, Bool.false_eq_true, ite_false, Measure.map_const, measure_univ, one_smul]
    rw [Measure.map_dirac' he]
    simp only [cellWithNext?, hc, Bool.false_eq_true, ite_false]
  | true =>
    have hcomp : cellWithScalar? rewards C_star C_h z t r hr hm U a0 f =
        (cellWithNext? rewards C_star C_h z t r hr hm U a0 f) ∘
          (nextSet rewards C_star C_h z t r hr hm U a0) := by
      funext x
      rfl
    rw [hcomp, ← Measure.map_map he
      (measurable_nextSet rewards C_star C_h z t r hr hm U a0),
      nextSet_map rewards C_star C_h z t r hr hm U a0 hc]

/-- Source-retaining local joint tests. The retained object can include the
entire reconstructed source and all its recorder coordinates. -/
theorem cell_joint_lintegral {Y : Type*} [MeasurableSpace Y]
    (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (retain : ContinuousControlSlice.Scalar → Y) (hretain : Measurable retain)
    (test : Y × Option (LogicalCell p rate) → ENNReal) (htest : Measurable test) :
    ∫⁻ v : ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar,
        test (retain v.1, cellWithScalar? rewards C_star C_h z t r hr hm U a0 v.1 v.2)
        ∂ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw =
      ∫⁻ f, ∫⁻ V,
        test (retain f, cellWithNext? rewards C_star C_h z t r hr hm U a0 f V)
        ∂refreshMeasure rewards C_star C_h z t r hr hm U a0
        ∂ContinuousControlSlice.scalarLaw := by
  have hleft : Measurable (fun v : ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar =>
      test (retain v.1, cellWithScalar? rewards C_star C_h z t r hr hm U a0 v.1 v.2)) :=
    htest.comp ((hretain.comp measurable_fst).prodMk
      (measurable_cellWithScalar? rewards C_star C_h z t r hr hm U a0))
  rw [lintegral_prod _ hleft.aemeasurable]
  apply lintegral_congr
  intro f
  have hlocal : Measurable (fun e : Option (LogicalCell p rate) => test (retain f, e)) :=
    htest.comp (measurable_const.prodMk measurable_id)
  have hcell : Measurable (cellWithScalar? rewards C_star C_h z t r hr hm U a0 f) := by
    change Measurable ((cellWithNext? rewards C_star C_h z t r hr hm U a0 f) ∘
      (nextSet rewards C_star C_h z t r hr hm U a0))
    exact (measurable_of_countable _).comp
      (measurable_nextSet rewards C_star C_h z t r hr hm U a0)
  have hnext : Measurable (cellWithNext? rewards C_star C_h z t r hr hm U a0 f) :=
    measurable_of_countable _
  rw [← lintegral_map hlocal hcell, cell_refresh_map rewards C_star C_h z t r hr hm U a0 f,
    lintegral_map hlocal hnext]

/-- With FAST erased from the retained test, the fast arm and residual draw
have the genuine canonical product law on enabled PRE-nonoverflow proposals. -/
theorem fast_residual_product (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) :
    (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw).map
      (fun v => (actualFast rewards C_star C_h z t r hr hm U v.1,
        nextSet rewards C_star C_h z t r hr hm U a0 v.2)) =
      (ContinuousControlSlice.scalarLaw.map (actualFast rewards C_star C_h z t r hr hm U)).prod
        (ContinuousControlSlice.scalarLaw.map (nextSet rewards C_star C_h z t r hr hm U a0)) := by
  exact (Measure.map_prod_map _ _ (measurable_actualFast rewards C_star C_h z t r hr hm U)
    (measurable_nextSet rewards C_star C_h z t r hr hm U a0)).symm

omit hr hm

/-- The inserted source is exactly the inverse FAST split with its original
remainder, including all private arrays and the original coordinator index. -/
theorem insertCurrentFastScalar_eq_split (f : ContinuousControlSlice.Scalar) :
    insertCurrentFastScalar t z f =
      (ReferenceSourceFastScalarDisintegration.sourceFastScalarSplit p
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z) t).symm
        (f, (ReferenceSourceFastScalarDisintegration.sourceFastScalarSplit p
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z) t z).2) := by
  symm
  have h := ReferenceSourceFastScalarDisintegration.sourceFastScalarSplit_replaceSourceControl
    p (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z) t z f rfl
  simpa only [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
    ReferenceFirstCollectionFastErasure.insertCurrentFastScalar,
    ReferenceFirstCollectionFastErasure.replaceFastScalar,
    ReferenceSourceFastScalarDisintegration.FastLabel] using h

theorem measurable_insertCurrentFastScalar : Measurable (insertCurrentFastScalar t z) := by
  have h : insertCurrentFastScalar t z = fun f =>
      (ReferenceSourceFastScalarDisintegration.sourceFastScalarSplit p
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z) t).symm
        (f, (ReferenceSourceFastScalarDisintegration.sourceFastScalarSplit p
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z) t z).2) :=
    funext (insertCurrentFastScalar_eq_split z t)
  rw [h]
  exact (ReferenceSourceFastScalarDisintegration.measurable_sourceFastScalarSplit_symm p _ t).comp
    (measurable_id.prodMk measurable_const)

include hr hm

/-- The source and its logical FAST are fed by the SAME scalar. This identity
keeps all source correlations in the test. -/
theorem source_retaining_cell_lintegral (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (test : SourceInput p × Option (LogicalCell p rate) → ENNReal) (htest : Measurable test) :
    ∫⁻ v : ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar,
        test (insertCurrentFastScalar t z v.1,
          cellWithScalar? rewards C_star C_h z t r hr hm U a0 v.1 v.2)
        ∂ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw =
      ∫⁻ f, ∫⁻ V,
        test (insertCurrentFastScalar t z f,
          cellWithNext? rewards C_star C_h z t r hr hm U a0 f V)
        ∂refreshMeasure rewards C_star C_h z t r hr hm U a0
        ∂ContinuousControlSlice.scalarLaw :=
  cell_joint_lintegral rewards C_star C_h z t r hr hm U a0
    (insertCurrentFastScalar t z)
    (measurable_insertCurrentFastScalar z t) test htest

/-- Actual current collection presence after inserting only FAST. -/
theorem insertedRecord_present (f : ContinuousControlSlice.Scalar) :
    (actualRecord rate rewards C_star C_h t (insertCurrentFastScalar t z f)).isSome = true := by
  obtain ⟨q, hq, _⟩ := ReferenceFirstCollectionFastErasure.firstCollection_currentFast_domain
    rewards C_star C_h t z t le_rfl r hr hm f
  rw [hq]
  rfl

/-- The inserted record is extracted from the actual option, never chosen. -/
def insertedRecord (f : ContinuousControlSlice.Scalar) : Record rate :=
  (actualRecord rate rewards C_star C_h t (insertCurrentFastScalar t z f)).get
    (insertedRecord_present rewards C_star C_h z t r hr hm f)

theorem insertedRecord_spec (f : ContinuousControlSlice.Scalar) :
    actualRecord rate rewards C_star C_h t (insertCurrentFastScalar t z f) =
      some (insertedRecord rewards C_star C_h z t r hr hm f) := (Option.some_get _).symm

theorem insertedRecord_mem (f : ContinuousControlSlice.Scalar) :
    insertedRecord rewards C_star C_h z t r hr hm f ∈
      firstCollection (rate := rate) rewards C_star C_h (insertCurrentFastScalar t z f) := by
  obtain ⟨q, hq, hmem, _⟩ := ReferenceFirstCollectionFastErasure.firstCollection_currentFast_domain
    rewards C_star C_h t z t le_rfl r hr hm f
  have he := Option.some.inj (hq.symm.trans
    (insertedRecord_spec rewards C_star C_h z t r hr hm f))
  rwa [← he]

/-- The actual code, successor, evidence, dependent call, readout and `cell0`
are all retained. Raw records with different input rows are not equated. -/
theorem insertedRecord_frames (f : ContinuousControlSlice.Scalar) :
    let q := insertedRecord rewards C_star C_h z t r hr hm f
    roundRecordCode q = roundRecordCode r ∧ q.output.next = r.output.next ∧
      q.evidence = r.evidence ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 q =
        ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 q =
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r ∧
      cell0 rate q = cell0 rate r := by
  obtain ⟨q, hq, hcode, hnext, hevidence, hcall, hread, hc⟩ :=
    ReferenceFirstCollectionFastErasure.firstCollection_currentFast_recordCode_eq
      rewards C_star C_h t z r hr hm f
  have he := Option.some.inj (hq.symm.trans
    (insertedRecord_spec rewards C_star C_h z t r hr hm f))
  rw [← he]
  exact ⟨hcode, hnext, hevidence, hcall, hread, hc⟩

theorem actualPast_insert (f : ContinuousControlSlice.Scalar) :
    actualPast rewards C_star C_h (insertCurrentFastScalar t z f) t
      (insertedRecord rewards C_star C_h z t r hr hm f)
      (insertedRecord_spec rewards C_star C_h z t r hr hm f)
      (insertedRecord_mem rewards C_star C_h z t r hr hm f) =
        actualPast rewards C_star C_h z t r hr hm := by
  apply Option.some.inj
  rw [← actualPast_spec, ← actualPast_spec]
  exact ReferenceFirstCollectionFastErasure.insertCurrentFastScalar_pastCells_eq
    rewards C_star C_h (r.input.row.2 t) t z f

theorem actualInput_insert (f : ContinuousControlSlice.Scalar) :
    actualInput rewards C_star C_h (insertCurrentFastScalar t z f) t
      (insertedRecord rewards C_star C_h z t r hr hm f)
      (insertedRecord_spec rewards C_star C_h z t r hr hm f)
      (insertedRecord_mem rewards C_star C_h z t r hr hm f) =
        actualInput rewards C_star C_h z t r hr hm := by
  apply Option.some.inj
  rw [← actualInput_spec, ← actualInput_spec]
  exact (insertedRecord_frames rewards C_star C_h z t r hr hm f).2.2.2.2.2

theorem actualFast_insert (U : SlowSet p) (f g : ContinuousControlSlice.Scalar) :
    actualFast rewards C_star C_h (insertCurrentFastScalar t z f) t
      (insertedRecord rewards C_star C_h z t r hr hm f)
      (insertedRecord_spec rewards C_star C_h z t r hr hm f)
      (insertedRecord_mem rewards C_star C_h z t r hr hm f) U g =
        actualFast rewards C_star C_h z t r hr hm U g := by
  unfold actualFast
  apply FastComplementLocality.sampleFast_eq_of_eq_on_complement
  intro a _
  unfold actualWeight
  rw [actualPast_insert rewards C_star C_h z t r hr hm f]

/-- FAST insertion affects only the sampled logical fast arm; the literal
cell at the inserted source uses the same full before/after numerical data. -/
theorem cellWithScalar_insert (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) (f g x : ContinuousControlSlice.Scalar) :
    cellWithScalar rewards C_star C_h (insertCurrentFastScalar t z f) t
      (insertedRecord rewards C_star C_h z t r hr hm f)
      (insertedRecord_spec rewards C_star C_h z t r hr hm f)
      (insertedRecord_mem rewards C_star C_h z t r hr hm f) U a0 g x =
        cellWithScalar rewards C_star C_h z t r hr hm U a0 g x := by
  unfold cellWithScalar cellWithNext nextSet
  rw [actualFast_insert, actualInput_insert, actualPast_insert,
    (insertedRecord_frames rewards C_star C_h z t r hr hm f).1]

omit hr hm

theorem sourceFastScalar_insert (f : ContinuousControlSlice.Scalar) :
    ReferenceSourceFastScalarDisintegration.sourceFastScalar p t
      (insertCurrentFastScalar t z f) = f := by
  unfold ReferenceSourceFastScalarDisintegration.sourceFastScalar
  simp only [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  rw [(ReferenceFirstCollectionFastErasure.insertCurrentFastScalar_source_frames t z f).2.2.1]
  exact (ReferenceFirstCollectionFastErasure.insertCurrentFastScalar_control_frames t z f).2.1

include hr hm

/-- The actual inserted-source optional cell is the literal fixed-remainder
cell used by the source-retaining test law. -/
theorem collectionLogicalCellAt_insert (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) (f x : ContinuousControlSlice.Scalar) :
    collectionLogicalCellAt rewards C_star C_h (insertCurrentFastScalar t z f) t
      (insertedRecord rewards C_star C_h z t r hr hm f)
      (insertedRecord_spec rewards C_star C_h z t r hr hm f)
      (insertedRecord_mem rewards C_star C_h z t r hr hm f) U a0 x =
        cellWithScalar? rewards C_star C_h z t r hr hm U a0 f x := by
  unfold collectionLogicalCellAt cellWithScalar?
  rw [sourceFastScalar_insert z t f, actualInput_insert rewards C_star C_h z t r hr hm f,
    cellWithScalar_insert rewards C_star C_h z t r hr hm U a0 f f x]

/-- The actual inserted-source joint-test law. The source and cell use the
same `f`; the explicit refresh measure retains every before-refresh field. -/
theorem actual_source_retaining_lintegral (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (test : SourceInput p × Option (LogicalCell p rate) → ENNReal) (htest : Measurable test) :
    ∫⁻ v : ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar,
        test (insertCurrentFastScalar t z v.1,
          collectionLogicalCellAt rewards C_star C_h (insertCurrentFastScalar t z v.1) t
            (insertedRecord rewards C_star C_h z t r hr hm v.1)
            (insertedRecord_spec rewards C_star C_h z t r hr hm v.1)
            (insertedRecord_mem rewards C_star C_h z t r hr hm v.1) U a0 v.2)
        ∂ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw =
      ∫⁻ f, ∫⁻ V, test (insertCurrentFastScalar t z f,
        cellWithNext? rewards C_star C_h z t r hr hm U a0 f V)
        ∂refreshMeasure rewards C_star C_h z t r hr hm U a0
        ∂ContinuousControlSlice.scalarLaw := by
  simp_rw [collectionLogicalCellAt_insert rewards C_star C_h z t r hr hm U a0]
  exact source_retaining_cell_lintegral rewards C_star C_h z t r hr hm U a0 test htest

/-- On enabled PRE-nonoverflow dates the actual fast arm, proposal, and residual
are literal canonical formulas. No assertion about POST overflow is required. -/
theorem cell_pre_nonoverflow (U : SlowSet p)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) (f x : ContinuousControlSlice.Scalar)
    (hc : (actualInput rewards C_star C_h z t r hr hm).enabled = true)
    (hs : (RecordedQueueRun.run (queueParameters rate)
      (actualPast rewards C_star C_h z t r hr hm)).overflow = false) :
    let e := cellWithScalar rewards C_star C_h z t r hr hm U a0 f x
    e.slowSet = U ∧ e.fastArm = (actualFast rewards C_star C_h z t r hr hm U f).val ∧
      e.proposal = decide ((a0 t).val < 4 * p.m * rate.eta.val) ∧
      e.nextSlowSet = if (a0 t).val < 4 * p.m * rate.eta.val then
        residualDraw rate e.before (actualInput rewards C_star C_h z t r hr hm)
          (fun _ => 1) (fun _ => zero_lt_one) x else U := by
  simp only [cellWithScalar, cellWithNext, nextSet, hs, hc, Bool.false_eq_true,
    ite_false, Bool.not_false, Bool.true_and, decide_eq_true_eq, and_self]

/-- An enabled zero arrival remains an enabled service record, distinct from
a disabled date; any previously queued backlog is still served. -/
theorem enabled_zero_record (hc : (actualInput rewards C_star C_h z t r hr hm).enabled = true)
    (hs : (RecordedQueueRun.run (queueParameters rate)
      (actualPast rewards C_star C_h z t r hr hm)).overflow = false)
    (a : Fin p.K) (hz : RecordedQueueRun.quantizedArrival (queueParameters rate)
      (actualInput rewards C_star C_h z t r hr hm) a = 0) :
    RecordedQueueRun.acceptedRecord (queueParameters rate)
      (RecordedQueueRun.run (queueParameters rate) (actualPast rewards C_star C_h z t r hr hm))
      (actualInput rewards C_star C_h z t r hr hm) a = (true, 0) := by
  simp only [RecordedQueueRun.acceptedRecord, hs, hc, hz, Bool.false_eq_true, ite_false, ite_true]

/-- On enabled dates the erased-FAST fast/residual law is the product of the
canonical fast law and the explicit refresh law. `actualFast_map` identifies
its first factor with `qGammaPMF`, including every genuine complement arm. -/
theorem fast_refresh_product (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (hc : (actualInput rewards C_star C_h z t r hr hm).enabled = true) :
    (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw).map
      (fun v => (actualFast rewards C_star C_h z t r hr hm U v.1,
        nextSet rewards C_star C_h z t r hr hm U a0 v.2)) =
      (ContinuousControlSlice.scalarLaw.map (actualFast rewards C_star C_h z t r hr hm U)).prod
        (refreshMeasure rewards C_star C_h z t r hr hm U a0) := by
  rw [fast_residual_product rewards C_star C_h z t r hr hm U a0,
    nextSet_map rewards C_star C_h z t r hr hm U a0 hc]

/-- The literal collection recorder with the derived full stopped weights. -/
def literalRecorder (enabled : Bool) (slice : ContinuousControlSlice.Slice p.m p.K) : Option (Fin p.K) :=
  SnapshotRecordingKernel.recordingMap p .collection enabled rate.eta.val rate.eta.property rate.sourceCap
    (fun _ => 1) (actualWeight rewards C_star C_h z t r hr hm) (fun _ => zero_lt_one)
    (fun a => (actual_weight_bounds rewards C_star C_h z t r hr hm a).1)
    (fun a => (actual_weight_bounds rewards C_star C_h z t r hr hm a).2.1)
    (fun a => by simpa only [mul_one] using
      (actual_weight_bounds rewards C_star C_h z t r hr hm a).2.2) slice

private theorem collection_recordingMap_eq_literal (enabled : Bool) (v w : Fin p.K → ℝ)
    (hv : ∀ a, 0 < v a) (hw : ∀ a, 0 < w a)
    (hl : ∀ a, v a ≤ w a) (hh : ∀ a, w a ≤ 2 * v a)
    (hunit : v = (fun _ => 1)) (slice : ContinuousControlSlice.Slice p.m p.K) :
    SnapshotRecordingKernel.recordingMap p .collection enabled rate.eta.val rate.eta.property rate.sourceCap
      v w hv hw hl hh slice = literalRecorder rewards C_star C_h z t r hr hm enabled slice := by
  subst v
  rfl

/-- The actual numerical marker is this same collection recorder, including
all absent markers and all disabled dates. No LIVE independence is asserted. -/
theorem actual_marker_eq_literalRecorder :
    (actualInput rewards C_star C_h z t r hr hm).recordedArm =
      literalRecorder rewards C_star C_h z t r hr hm
        (actualInput rewards C_star C_h z t r hr hm).enabled
        (ContinuousLearningRows.sliceAt r.input.time r.input.row.2) := by
  obtain ⟨call, _, hread, hcall, hanchor, _⟩ := actual_data rewards C_star C_h z t r hr hm
  have hu := congrArg (Option.map (fun args => args.1.anchor)) hcall
  rw [Option.map_some, hanchor] at hu
  have hp : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).isSome = true := by
    rw [hread]
    rfl
  obtain ⟨hf, hb⟩ := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 r).mp hp
  cases he : r.output.preparation.coordinator with
  | first outcome => simp only [he] at hb
  | invalidCollectionCutoff => simp only [he] at hb
  | dagger => simp only [he] at hb
  | collection payload ledger clock cutoff outcome =>
    cases outcome with
    | continuing core snapshot boundary scores =>
      have hc : ReferenceLaterCollectionArrivalReadout.continuingCollectionInput
          r payload ledger clock cutoff snapshot = actualInput rewards C_star C_h z t r hr hm := by
        simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
          dite_eq_left hf, he, Option.some.injEq] using hread
      have hunit : payload.anchor = (fun _ => 1) := by
        simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall, ite_eq_left hf,
          he, Option.map_some, Option.some.injEq] using hu
      rw [← hc]
      unfold ReferenceLaterCollectionArrivalReadout.continuingCollectionInput
      exact collection_recordingMap_eq_literal rewards C_star C_h z t r hr hm _ _ _ _ _ _ _ hunit _
    | _ => simp only [he] at hb
  | live registers owned base outcome =>
    cases outcome with
    | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected =>
      have hpos : 0 < registers.payload.sigma.val := by simpa only [he] using hb
      have hc : ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
          r registers owned base dispatched selected = actualInput rewards C_star C_h z t r hr hm := by
        simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
          dite_eq_left hf, he, dite_eq_left hpos, Option.some.injEq] using hread
      have hunit : registers.payload.anchor = (fun _ => 1) := by
        simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall, ite_eq_left hf,
          he, ite_eq_left hpos, Option.map_some, Option.some.injEq] using hu
      rw [← hc]
      unfold ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
      exact collection_recordingMap_eq_literal rewards C_star C_h z t r hr hm _ _ _ _ _ _ _ hunit _
    | _ => simp only [he] at hb

/-- The genuine disjoint-label slice marginal of the same literal collection
recorder. Tests retaining recorder coordinates must keep their source values. -/
theorem literalRecorder_map :
    (ContinuousControlSlice.sliceLaw p.m p.K).map
      (literalRecorder rewards C_star C_h z t r hr hm true) =
      (RecordedRoundMoments.recordingOutcomePMF
        (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property rate.sourceCap
          (fun _ => 1) (fun _ => zero_lt_one))).toMeasure :=
  SnapshotRecordingKernel.map_recordingMap p .collection rate.eta.val rate.eta.property rate.sourceCap
    _ _ _ _ _ _

/-- The actual cell's FAST/next-set readout has the erased-FAST product law on
enabled PRE-nonoverflow dates. `actualFast_map` identifies its fast factor
with the genuine canonical `qGammaPMF`; proposals use the residual PMF. -/
theorem cell_fast_next_map (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (hc : (actualInput rewards C_star C_h z t r hr hm).enabled = true)
    (hs : (RecordedQueueRun.run (queueParameters rate)
      (actualPast rewards C_star C_h z t r hr hm)).overflow = false) :
    (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw).map
      (fun v => ((cellWithScalar rewards C_star C_h z t r hr hm U a0 v.1 v.2).fastArm,
        (cellWithScalar rewards C_star C_h z t r hr hm U a0 v.1 v.2).nextSlowSet)) =
      ((ContinuousControlSlice.scalarLaw.map (actualFast rewards C_star C_h z t r hr hm U)).map
        Subtype.val).prod (refreshMeasure rewards C_star C_h z t r hr hm U a0) := by
  have heq : (fun v : ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar =>
      ((cellWithScalar rewards C_star C_h z t r hr hm U a0 v.1 v.2).fastArm,
        (cellWithScalar rewards C_star C_h z t r hr hm U a0 v.1 v.2).nextSlowSet)) =
      fun v => ((actualFast rewards C_star C_h z t r hr hm U v.1).val,
        nextSet rewards C_star C_h z t r hr hm U a0 v.2) := by
    funext v
    simp only [cellWithScalar, cellWithNext, hs, Bool.false_eq_true, ite_false]
  rw [heq, Measure.map_map measurable_subtype_coe
    (measurable_actualFast rewards C_star C_h z t r hr hm U)]
  have hprod := (Measure.map_prod_map ContinuousControlSlice.scalarLaw ContinuousControlSlice.scalarLaw
    (measurable_subtype_coe.comp (measurable_actualFast rewards C_star C_h z t r hr hm U))
    (measurable_nextSet rewards C_star C_h z t r hr hm U a0)).symm
  rw [nextSet_map rewards C_star C_h z t r hr hm U a0 hc] at hprod
  exact hprod

end Actual

/-- The actual lookup/window domain, with its inherited original-source Borel
space. It contains no history, state, or correctness package. -/
abbrev ActualSource (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T) :=
  {z : SourceInput p // ∃ r : Record rate,
    actualRecord rate rewards C_star C_h t z = some r ∧
      r ∈ firstCollection (rate := rate) rewards C_star C_h z}

section Domain

variable (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)

local notation "D" => ActualSource (rate := rate) rewards C_star C_h t

theorem domainRecord_present (z : D) :
    (actualRecord rate rewards C_star C_h t z.val).isSome = true := by
  obtain ⟨r, hr, _⟩ := z.property
  rw [hr]
  rfl

/-- Canonical actual-record option extraction on the actual source domain. -/
def domainRecord (z : D) : Record rate :=
  (actualRecord rate rewards C_star C_h t z.val).get
    (domainRecord_present rewards C_star C_h t z)

theorem domainRecord_spec (z : D) :
    actualRecord rate rewards C_star C_h t z.val =
      some (domainRecord rewards C_star C_h t z) := (Option.some_get _).symm

theorem domainRecord_mem (z : D) :
    domainRecord rewards C_star C_h t z ∈ firstCollection (rate := rate) rewards C_star C_h z.val := by
  obtain ⟨r, hr, hm⟩ := z.property
  have he := Option.some.inj (hr.symm.trans (domainRecord_spec rewards C_star C_h t z))
  rwa [← he]

local notation "rD" z => domainRecord rewards C_star C_h t z
local notation "hrD" z => domainRecord_spec rewards C_star C_h t z
local notation "hmD" z => domainRecord_mem rewards C_star C_h t z
local notation "LD" z => actualPast rewards C_star C_h (Subtype.val z) t (rD z) (hrD z) (hmD z)
local notation "cD" z => actualInput rewards C_star C_h (Subtype.val z) t (rD z) (hrD z) (hmD z)
local notation "SD" z => RecordedQueueRun.run (queueParameters rate) (LD z)

private theorem measurable_of_some {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (f : X → A) (hf : Measurable (fun x => some (f x))) : Measurable f := by
  have he : Measurable (Equiv.optionEquivSumPUnit A) := comap_measurable _
  have hinl : MeasurableEmbedding (@Sum.inl A PUnit) :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩
  exact hinl.measurable_comp_iff.mp (he.comp hf)

/-- The full physical code remains Borel on the actual source domain. -/
theorem measurable_domainPhysical : Measurable (fun z : D => roundRecordCode (rD z)) := by
  apply measurable_of_some
  have h := (ReferenceCalendarActualControlCallbackSections.measurable_codeAt
    rate rewards C_star C_h t).comp (measurable_subtype_coe (p := fun z => ∃ r : Record rate,
      actualRecord rate rewards C_star C_h t z = some r ∧
        r ∈ firstCollection (rate := rate) rewards C_star C_h z))
  convert h using 1
  funext z
  simp only [Function.comp_apply, ReferenceCalendarActualControlCallbackSections.codeAt, hrD z, Option.map_some]

private theorem measurable_numericalFromCode : Measurable
    (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalFromRecordCode code
        (fun a => ((rewards t a).val : ℝ) / (ConstructorDimensions.D p : ℝ))) := by
  let Entry := ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
    (Bool × (Bool × Option (CoordinatorRecordingOperation.Output p)))
  have hpayload : Measurable (fun entry : Entry => entry.1.1.payload) := by
    have hview : Measurable (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
        (p := p) (rate := rate)) := comap_measurable _
    exact measurable_fst.comp (hview.comp (measurable_fst.comp measurable_fst))
  have hrate : Measurable (fun entry : Entry => entry.1.1.payload.rate) :=
    AssignmentPayloadDerivedMeasurability.measurable_inputRate.comp hpayload
  have hmarker : Measurable (fun entry : Entry =>
      entry.2.2.2.bind (fun out => out.gateArm)) := by
    have hg : Measurable (fun out : Option (CoordinatorRecordingOperation.Output p) =>
        out.bind (fun x => x.gateArm)) := Measurable.of_discrete
    exact hg.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_id)))
  have hentry : Measurable (fun v : Entry ×
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
      (v.1.2.2.1, (v.1.2.2.2.bind (fun out => out.gateArm),
        ((fun a => ((rewards t a).val : ℝ) / (ConstructorDimensions.D p : ℝ)), v.1.1.1.payload.rate)))) :=
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
      ((hmarker.comp measurable_fst).prodMk (measurable_const.prodMk (hrate.comp measurable_fst)))
  exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent _ hentry
    ReferenceCoordinatorRecorderCallTrace.cell ReferenceCoordinatorRecorderCallTrace.measurable_cell

/-- No range certificate or real reward/rate vector is discarded by the
Borel numerical observation. -/
theorem measurable_domainNumerical : Measurable (fun z : D =>
    ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates (cD z)) := by
  apply measurable_of_some
  have h := (measurable_numericalFromCode (rate := rate) rewards t).comp
    (measurable_domainPhysical rewards C_star C_h t)
  convert h using 1
  funext z
  obtain ⟨call, _, hread, _⟩ := actual_data rewards C_star C_h z.val t (rD z) (hrD z) (hmD z)
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t z.val (rD z) (hrD z)
  have he := ReferenceLaterCollectionSourceReadoutMeasurability.readout_numerical_factorization
    0 (rD z)
  rw [hread] at he
  simp only [Option.map_some, Option.isSome_some, ite_true] at he
  rw [hf.2.2.1, hf.2.2.2] at he
  exact he

private instance sumMeasurableSingleton {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] : MeasurableSingletonClass (A ⊕ B) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
    | inr b => simpa only [Set.image_singleton] using (MeasurableSet.singleton b).inr_image

private instance listMeasurableSingleton {A : Type*}
    [MeasurableSpace A] [MeasurableSingletonClass A] : MeasurableSingletonClass (List A) where
  measurableSet_singleton L := by
    have hinj : Function.Injective
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates (α := A)) := by
      intro B C h
      have hlen : B.length = C.length := congrArg Prod.fst h
      apply List.ext_getElem hlen
      intro k hk hk'
      have he := congrFun (congrArg Prod.snd h) k
      simpa only [ReferenceActiveHorizonMeasurability.listObservationCoordinates,
        ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Sum.inr.injEq] using he
    have h := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (MeasurableSet.singleton (ReferenceActiveHorizonMeasurability.listObservationCoordinates L))
    convert h using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

/-- PRE is the actual zero-origin canonical run. Its countable state is
observed measurably through the existing strict-past readout. -/
theorem measurable_domainBefore (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (fun z : D => SD z) := by
  let Code := (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))
  have hc : Measurable (fun z : D =>
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (SD z)) := by
    apply measurable_of_some
    have hp := ReferenceFirstCollectionCurrentRetainedGate.prefixReadout_measurable
      rate rewards C_star C_h control0 t
    have hle := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (t.val + 1)
    have hfull := hp.mono hle le_rfl
    have h := hfull.comp (measurable_subtype_coe (p := fun z => ∃ r : Record rate,
      actualRecord rate rewards C_star C_h t z = some r ∧
        r ∈ firstCollection (rate := rate) rewards C_star C_h z))
    convert h using 1
    funext z
    simp only [Function.comp_apply, ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?,
      actualPast_spec rewards C_star C_h z.val t (rD z) (hrD z) (hmD z), Option.map_some]
  exact (measurable_of_countable (fun v : Code =>
    (⟨v.1, v.2.1, v.2.2⟩ : RecordedQueueRun.RunState p.K))).comp hc

/-- Borelness of the complete cell jointly in the actual original source,
the retained label-zero array, and the two scalar coordinates. The incoming
slow set is arbitrary and has no distributional hypothesis. -/
theorem measurable_domainCell (control0 : ContinuousLearningRows.TimeControl p) (U : SlowSet p) :
    Measurable (fun v : D × ((Fin p.T → ContinuousControlSlice.Scalar) ×
        (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar)) =>
      cellWithScalar rewards C_star C_h v.1.val t (rD v.1) (hrD v.1) (hmD v.1)
        U v.2.1 v.2.2.1 v.2.2.2) := by
  let X := D × ((Fin p.T → ContinuousControlSlice.Scalar) ×
    (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar))
  let Q := queueParameters rate
  let before := fun v : X => SD v.1
  let round := fun v : X => cD v.1
  have hb : Measurable before := (measurable_domainBefore rewards C_star C_h t control0).comp
    measurable_fst
  have hn : Measurable (fun v : X =>
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates (round v)) :=
    (measurable_domainNumerical rewards C_star C_h t).comp measurable_fst
  have ho : Measurable (fun v : X => (before v).overflow) :=
    (measurable_of_countable (fun S : RecordedQueueRun.RunState p.K => S.overflow)).comp hb
  have he : Measurable (fun v : X => (round v).enabled) := measurable_fst.comp hn
  have ha : Measurable (fun v : X => RecordedQueueRun.acceptedRecord Q (before v) (round v)) := by
    let accepted := fun v : RecordedQueueRun.RunState p.K × (Bool × (Fin p.K → ℕ)) =>
      fun a => if v.1.overflow then (false, 0) else if v.2.1 then (true, v.2.2 a) else (false, 0)
    exact (measurable_of_countable accepted).comp
      (hb.prodMk ((ReferenceLaterCollectionSourceReadoutMeasurability.measurable_arrivalsFromNumerical rate).comp hn))
  have hafter : Measurable (fun v : X => RecordedQueueRun.step Q (before v) (round v)) := by
    let update := fun v : RecordedQueueRun.RunState p.K × (Fin p.K → Bool × ℕ) =>
      let registers := fun a => QueueReplay.transition (4 * Q.n) (v.1.registers a) (v.2 a)
      (⟨registers, v.1.overflow || decide (∃ a, 32 * (registers a).2 > Q.D),
        fun a => v.1.records a ++ [v.2 a]⟩ : RecordedQueueRun.RunState p.K)
    exact (measurable_of_countable update).comp (hb.prodMk ha)
  have hservice : Measurable (fun v : X => fun a => RecordedQueueRun.recordService (4 * Q.n)
      ((before v).registers a) (RecordedQueueRun.acceptedRecord Q (before v) (round v) a)) :=
    (measurable_of_countable (fun v : RecordedQueueRun.RunState p.K × (Fin p.K → Bool × ℕ) =>
      fun a => RecordedQueueRun.recordService (4 * Q.n) (v.1.registers a) (v.2 a))).comp (hb.prodMk ha)
  have hw : Measurable (fun v : X => fun a : CanonicalFastSampling.FastArm U =>
      actualWeight rewards C_star C_h v.1.val t (rD v.1) (hrD v.1) (hmD v.1) a.val) :=
    (measurable_of_countable (fun S : RecordedQueueRun.RunState p.K =>
      fun a : CanonicalFastSampling.FastArm U => RecordedQueueRun.scoreWeight Q S a.val)).comp hb
  have hlocal := measurable_sampleLocalFast_varyingWeights rate U (fun _ : X => fun _ => 1)
    measurable_const _ hw (fun _ _ => zero_lt_one)
    (fun v a => (actual_weight_bounds rewards C_star C_h v.1.val t (rD v.1) (hrD v.1) (hmD v.1) a.val).1)
    (fun v a => (actual_weight_bounds rewards C_star C_h v.1.val t (rD v.1) (hrD v.1) (hmD v.1) a.val).2.1)
    (fun v a => by simpa only [mul_one] using
      (actual_weight_bounds rewards C_star C_h v.1.val t (rD v.1) (hrD v.1) (hmD v.1) a.val).2.2)
    (fun v => v.2.2.1) (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hf : Measurable (fun v : X =>
      actualFast rewards C_star C_h v.1.val t (rD v.1) (hrD v.1) (hmD v.1) U v.2.2.1) := by
    convert hlocal using 1
    funext v
    exact (FastComplementLocality.sampleLocalFast_eq_sampleFast p rate.eta.property rate.sourceCap
      (fun _ => 1) _ (fun _ => zero_lt_one) _ _ _ U v.2.2.1).symm
  have hfast : Measurable (fun v : X => if (before v).overflow then frozenFastArm p else
      (actualFast rewards C_star C_h v.1.val t (rD v.1) (hrD v.1) (hmD v.1) U v.2.2.1).val) :=
    measurable_const.ite ((measurableSet_singleton true).preimage ho) (measurable_subtype_coe.comp hf)
  have hcoin : Measurable (fun v : X => decide ((v.2.1 t).val < 4 * p.m * rate.eta.val)) := by
    have hvalue : Measurable (fun v : X => (v.2.1 t).val) :=
      measurable_subtype_coe.comp ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd))
    have hi : Measurable (fun v : X => if (v.2.1 t).val < 4 * p.m * rate.eta.val
        then true else false) :=
      (measurable_const (a := true)).ite (measurableSet_lt hvalue
        (measurable_const (a := 4 * p.m * rate.eta.val))) (measurable_const (a := false))
    convert hi using 1
    funext v
    by_cases h : (v.2.1 t).val < 4 * p.m * rate.eta.val <;> simp only [h, decide_true,
      decide_false, ite_true, ite_false]
  let proposal := fun v : X => (round v).enabled && !(before v).overflow &&
    decide ((v.2.1 t).val < 4 * p.m * rate.eta.val)
  have hp : Measurable proposal :=
    (measurable_of_countable (fun b : Bool × (Bool × Bool) => b.1 && !b.2.1 && b.2.2)).comp
      (he.prodMk (ho.prodMk hcoin))
  have hres := measurable_residualDraw_of_actualPrePost rate before
    (fun v => RecordedQueueRun.step Q (before v) (round v)) round hb hafter (fun _ => rfl)
    (fun _ _ => 1) measurable_const (fun _ _ => zero_lt_one)
    (fun v => v.2.2.2) (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hnext : @Measurable X (SlowSet p) inferInstance ⊤ (fun v =>
      if (before v).overflow then frozenSlowSet p else
      if proposal v then residualDraw rate (before v) (round v) (fun _ => 1)
        (fun _ => zero_lt_one) v.2.2.2 else U) :=
    measurable_const.ite ((measurableSet_singleton true).preimage ho)
      (hres.ite ((measurableSet_singleton true).preimage hp) measurable_const)
  have hslow : @Measurable X (SlowSet p) inferInstance ⊤ (fun v =>
      if (before v).overflow then frozenSlowSet p else U) :=
    measurable_const.ite ((measurableSet_singleton true).preimage ho) measurable_const
  apply measurable_comap_iff.mpr
  exact measurable_const.prodMk (((measurable_domainPhysical rewards C_star C_h t).comp
    measurable_fst).prodMk (hn.prodMk (hb.prodMk (hafter.prodMk
      (ha.prodMk (hservice.prodMk (hslow.prodMk (hfast.prodMk (hp.prodMk hnext)))))))))

/-- The optional operation remains Borel through all disabled/overflow branches. -/
theorem measurable_domainCell? (control0 : ContinuousLearningRows.TimeControl p) (U : SlowSet p) :
    Measurable (fun v : D × ((Fin p.T → ContinuousControlSlice.Scalar) ×
        (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar)) =>
      cellWithScalar? rewards C_star C_h v.1.val t (rD v.1) (hrD v.1) (hmD v.1)
        U v.2.1 v.2.2.1 v.2.2.2) := by
  have hen : Measurable (fun v : D × ((Fin p.T → ContinuousControlSlice.Scalar) ×
        (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar)) => (cD v.1).enabled) :=
    measurable_fst.comp ((measurable_domainNumerical rewards C_star C_h t).comp measurable_fst)
  exact (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
    (measurable_domainCell rewards C_star C_h t control0 U)).ite
      ((measurableSet_singleton true).preimage hen) measurable_const

/-- Borelness for the actual source FAST, retaining the full original label-zero
array and a fresh residual scalar, on the literal lookup/window domain. -/
theorem measurable_collectionLogicalCellAt (control0 : ContinuousLearningRows.TimeControl p)
    (U : SlowSet p) : Measurable
    (fun v : D × ((Fin p.T → ContinuousControlSlice.Scalar) × ContinuousControlSlice.Scalar) =>
      collectionLogicalCellAt rewards C_star C_h v.1.val t (rD v.1) (hrD v.1) (hmD v.1)
        U v.2.1 v.2.2) := by
  have hfast : Measurable (fun v : D × ((Fin p.T → ContinuousControlSlice.Scalar) ×
        ContinuousControlSlice.Scalar) =>
      ReferenceSourceFastScalarDisintegration.sourceFastScalar p t v.1.val) :=
    (ReferenceSourceFastScalarDisintegration.measurable_sourceFastScalar p t).comp
      (measurable_subtype_coe.comp measurable_fst)
  change Measurable ((fun v : D × ((Fin p.T → ContinuousControlSlice.Scalar) ×
    (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar)) =>
      cellWithScalar? rewards C_star C_h v.1.val t (rD v.1) (hrD v.1) (hmD v.1)
        U v.2.1 v.2.2.1 v.2.2.2) ∘
    (fun v : D × ((Fin p.T → ContinuousControlSlice.Scalar) × ContinuousControlSlice.Scalar) =>
      (v.1, (v.2.1, (ReferenceSourceFastScalarDisintegration.sourceFastScalar p t v.1.val, v.2.2)))))
  apply (measurable_domainCell? rewards C_star C_h t control0 U).comp
  exact measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (hfast.prodMk (measurable_snd.comp measurable_snd)))

/-- Borelness also holds jointly in the ordinary incoming slow-set argument. -/
theorem measurable_collectionLogicalCellAt_varyingSlowSet
    (control0 : ContinuousLearningRows.TimeControl p) : Measurable
    (fun v : SlowSet p × (D × ((Fin p.T → ContinuousControlSlice.Scalar) × ContinuousControlSlice.Scalar)) =>
      collectionLogicalCellAt rewards C_star C_h v.2.1.val t (rD v.2.1) (hrD v.2.1) (hmD v.2.1)
        v.1 v.2.2.1 v.2.2.2) := by
  apply measurable_from_prod_countable_right
  intro U
  exact measurable_collectionLogicalCellAt rewards C_star C_h t control0 U

/-- The one-round kernel retains the complete reconstructed source and the
same entire label-zero array beside the optional cell. -/
def oneRoundSample (U : SlowSet p)
    (v : (D × (Fin p.T → ContinuousControlSlice.Scalar)) ×
      (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar)) :
    SourceInput p × ((Fin p.T → ContinuousControlSlice.Scalar) × Option (LogicalCell p rate)) :=
  (insertCurrentFastScalar t v.1.1.val v.2.1,
    (v.1.2, cellWithScalar? rewards C_star C_h v.1.1.val t
      (rD v.1.1) (hrD v.1.1) (hmD v.1.1) U v.1.2 v.2.1 v.2.2))

private theorem measurable_insert_joint : Measurable
    (fun v : SourceInput p × ContinuousControlSlice.Scalar => insertCurrentFastScalar t v.1 v.2) := by
  have hu := (ReferenceSourceCurrentControlFreshness.measurable_u_t (p := p) t).comp
    (measurable_fst : Measurable (Prod.fst : SourceInput p × ContinuousControlSlice.Scalar → _))
  have hs : Measurable (fun v : SourceInput p × ContinuousControlSlice.Scalar =>
      ReferenceFirstCollectionFastErasure.replaceFastScalar
        (ReferenceSourceCurrentControlFreshness.u_t p t v.1) v.2) := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro label
      by_cases hl : label = ContinuousControlSlice.Label.fast
      · simp only [hl, Function.update_self]
        exact measurable_snd
      · simp only [Function.update_of_ne hl]
        exact (measurable_pi_apply label).comp (measurable_fst.comp hu)
    · exact measurable_snd.comp hu
  exact (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
    (measurable_fst.prodMk hs)

theorem measurable_oneRoundSample (control0 : ContinuousLearningRows.TimeControl p) (U : SlowSet p) :
    Measurable (oneRoundSample (rate := rate) rewards C_star C_h t U) := by
  let X := (D × (Fin p.T → ContinuousControlSlice.Scalar)) ×
    (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar)
  have hz : Measurable (fun v : X => insertCurrentFastScalar t v.1.1.val v.2.1) :=
    (measurable_insert_joint t).comp
      ((measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_fst.comp measurable_snd))
  have hc : Measurable (fun v : X => cellWithScalar? rewards C_star C_h v.1.1.val t
      (rD v.1.1) (hrD v.1.1) (hmD v.1.1) U v.1.2 v.2.1 v.2.2) := by
    change Measurable ((fun v : D × ((Fin p.T → ContinuousControlSlice.Scalar) ×
      (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar)) =>
      cellWithScalar? rewards C_star C_h v.1.val t (rD v.1) (hrD v.1) (hmD v.1)
        U v.2.1 v.2.2.1 v.2.2.2) ∘ (fun v : X => (v.1.1, (v.1.2, v.2))))
    apply (measurable_domainCell? rewards C_star C_h t control0 U).comp
    exact (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact hz.prodMk ((measurable_snd.comp measurable_fst).prodMk hc)

/-- The kernel sample is the actual option-getter construction at the
inserted source, retaining its entire original label-zero array. -/
theorem oneRoundSample_actual (U : SlowSet p) (z : D)
    (a0 : Fin p.T → ContinuousControlSlice.Scalar) (f x : ContinuousControlSlice.Scalar) :
    oneRoundSample (rate := rate) rewards C_star C_h t U ((z, a0), (f, x)) =
      (insertCurrentFastScalar t z.val f, (a0,
        collectionLogicalCellAt rewards C_star C_h (insertCurrentFastScalar t z.val f) t
          (insertedRecord rewards C_star C_h z.val t (rD z) (hrD z) (hmD z) f)
          (insertedRecord_spec rewards C_star C_h z.val t (rD z) (hrD z) (hmD z) f)
          (insertedRecord_mem rewards C_star C_h z.val t (rD z) (hrD z) (hmD z) f) U a0 x)) := by
  rw [collectionLogicalCellAt_insert]
  rfl

/-- Borel source-retaining one-round probability kernel on the original
continuous source carrier. Its explicit refresh factor is `refreshMeasure`. -/
def oneRoundKernel (control0 : ContinuousLearningRows.TimeControl p) (U : SlowSet p) :
    ProbabilityTheory.Kernel (D × (Fin p.T → ContinuousControlSlice.Scalar))
      (SourceInput p × ((Fin p.T → ContinuousControlSlice.Scalar) × Option (LogicalCell p rate))) :=
  ProbabilityTheory.Kernel.mapOfMeasurable
    (ProbabilityTheory.Kernel.prod ProbabilityTheory.Kernel.id
      (ProbabilityTheory.Kernel.const _
        (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)))
    (oneRoundSample (rate := rate) rewards C_star C_h t U)
    (measurable_oneRoundSample (rate := rate) rewards C_star C_h t control0 U)

instance oneRoundKernel_markov (control0 : ContinuousLearningRows.TimeControl p) (U : SlowSet p) :
    ProbabilityTheory.IsMarkovKernel (oneRoundKernel (rate := rate) rewards C_star C_h t control0 U) := by
  unfold oneRoundKernel
  rw [ProbabilityTheory.Kernel.mapOfMeasurable_eq_map]
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
    (measurable_oneRoundSample (rate := rate) rewards C_star C_h t control0 U)

theorem oneRoundKernel_apply (control0 : ContinuousLearningRows.TimeControl p) (U : SlowSet p)
    (z : D) (a0 : Fin p.T → ContinuousControlSlice.Scalar) :
    oneRoundKernel (rate := rate) rewards C_star C_h t control0 U (z, a0) =
      (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw).map
        (fun v => oneRoundSample (rate := rate) rewards C_star C_h t U ((z, a0), v)) := by
  change (((ProbabilityTheory.Kernel.prod ProbabilityTheory.Kernel.id
      (ProbabilityTheory.Kernel.const _ (ContinuousControlSlice.scalarLaw.prod
        ContinuousControlSlice.scalarLaw))) (z, a0)).map
      (oneRoundSample (rate := rate) rewards C_star C_h t U)) = _
  rw [ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.id_apply,
    ProbabilityTheory.Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_oneRoundSample (rate := rate) rewards C_star C_h t control0 U)
      measurable_prodMk_left]
  rfl

/-- Joint-test form of the Borel kernel, retaining the same whole label-zero
array and reconstructed physical source in the explicit refresh integral. -/
theorem oneRoundKernel_lintegral (control0 : ContinuousLearningRows.TimeControl p)
    (U : SlowSet p) (z : D) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (test : SourceInput p × ((Fin p.T → ContinuousControlSlice.Scalar) ×
      Option (LogicalCell p rate)) → ENNReal) (htest : Measurable test) :
    ∫⁻ y, test y ∂oneRoundKernel (rate := rate) rewards C_star C_h t control0 U (z, a0) =
      ∫⁻ f, ∫⁻ V, test (insertCurrentFastScalar t z.val f,
        (a0, cellWithNext? rewards C_star C_h z.val t (rD z) (hrD z) (hmD z) U a0 f V))
        ∂refreshMeasure rewards C_star C_h z.val t (rD z) (hrD z) (hmD z) U a0
        ∂ContinuousControlSlice.scalarLaw := by
  have hsample : Measurable (fun v : ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar =>
      oneRoundSample (rate := rate) rewards C_star C_h t U ((z, a0), v)) :=
    (measurable_oneRoundSample (rate := rate) rewards C_star C_h t control0 U).comp
      ((measurable_const (a := (z, a0))).prodMk measurable_id)
  rw [oneRoundKernel_apply, lintegral_map htest hsample]
  exact source_retaining_cell_lintegral rewards C_star C_h z.val t (rD z) (hrD z) (hmD z) U a0
    (fun v => test (v.1, (a0, v.2)))
    (htest.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))

private theorem collection_lookup (R : List (Record rate)) (w j : ℕ)
    (hj : j < (collectionWindow R w).length) : R[w + j]? = some ((collectionWindow R w)[j]) := by
  have hp : collectionWindow R w <+: R.drop w := by
    refine ⟨(R.drop (w + 1)).dropWhile (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input), ?_⟩
    rw [collectionWindow, List.append_assoc, List.takeWhile_append_dropWhile]
    simp
  have h := hp.getElem hj
  rw [List.getElem_drop] at h
  rw [List.getElem?_eq_getElem (by have hb := hp.length_le; simp only [List.length_drop] at hb; omega)]
  exact congrArg some h.symm

/-- The physical first-collection endpoint is the actual first-call boundary;
when there is no later call it is the horizon, with no bound on collection length. -/
theorem firstCollection_endpoint (z : SourceInput p) :
    ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary rate rewards C_star C_h z =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        (firstLiveWindow (completeSuffixRecords rate z rewards C_star C_h)).length +
        (firstCollection (rate := rate) rewards C_star C_h z).length := by
  let R := completeSuffixRecords rate z rewards C_star C_h
  let w := (firstLiveWindow R).length
  cases hf : ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z with
  | none =>
    have hn := (ReferenceFirstCollectionSamplerCall.firstCollectionCall_none_iff rewards C_star C_h z).mp hf
    have htail : (R.drop (w + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) = R.drop (w + 1) := by
      apply List.takeWhile_eq_self_iff.mpr
      intro r hr
      have hnone := hn r (List.mem_of_mem_drop hr)
      cases hb : ReferenceCollectionPhaseHistory.laterChosen r.input with
      | false => rfl
      | true =>
        have hp := ReferenceFirstCollectionRenewalRecordingFeedback.laterChosen_parameters_present r.input hb
        change (ReferenceLaterSamplerParameterMeasurability.parameters? r.input).isSome = true at hp
        rw [hnone] at hp
        cases hp
    have hw : w ≤ R.length := (List.takeWhile_prefix _).length_le
    have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
    change R.length = _ at hlen
    simp only [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary, hf]
    change p.T = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + w +
      (collectionWindow R w).length
    rw [collectionWindow, List.length_append, List.length_take, htail, List.length_drop, List.length_drop]
    omega
  | some data =>
    rcases data with ⟨u, v, theta⟩
    obtain ⟨n, r, hr, ht, hcall, hearlier⟩ :=
      (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec rewards C_star C_h z u v theta).mp hf
    have hp := (ReferenceFirstCollectionSamplerCall.collectionCallAt_isSome r).symm
    rw [hcall, Option.isSome_some] at hp
    change (ReferenceLaterAssignmentFibreStep.parameters? r.input).isSome = true at hp
    rw [ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch] at hp
    have hindex := (List.getElem?_eq_some_iff.mp hr).1
    have hphase := (ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_phase_exhaustion
      rate rewards C_star C_h z ⟨n, hindex⟩).2
    rw [(List.getElem?_eq_some_iff.mp hr).2] at hphase
    have hprep : r.output.preparation.coordinator = ReferenceActivePhysicalStep.dispatch r.input := by
      rw [r.output_eq]
      rfl
    have hchosen : ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
      cases hd : ReferenceActivePhysicalStep.dispatch r.input with
      | collection payload ledger clock cutoff out =>
        cases out <;> simp_all only [ReferenceLaterAssignmentFibreStep.dispatchParameters?,
          ReferenceLaterAssignmentFibreStep.outcomeParameters?, Option.isSome_none, Bool.false_eq_true,
          ReferenceCollectionPhaseHistory.laterChosen, ReferenceActivePhysicalStep.prepare]
        all_goals rcases hphase with ⟨selected, hsel, _⟩ | ⟨c, hc⟩
        all_goals first
          | simp [hprep, ReferenceActivePhysicalStep.DispatchCut.selection] at hsel
          | simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, hprep] at hc
      | first out => simp only [hd, ReferenceLaterAssignmentFibreStep.dispatchParameters?, Option.isSome_none,
          Bool.false_eq_true] at hp
      | live registers owned base out => simp only [hd, ReferenceLaterAssignmentFibreStep.dispatchParameters?,
          Option.isSome_none, Bool.false_eq_true] at hp
      | dagger => simp only [hd, ReferenceLaterAssignmentFibreStep.dispatchParameters?, Option.isSome_none,
          Bool.false_eq_true] at hp
      | invalidCollectionCutoff => simp only [hd, ReferenceLaterAssignmentFibreStep.dispatchParameters?,
          Option.isSome_none, Bool.false_eq_true] at hp
    have hi := ReferenceFirstCollectionCurrentNumericalCell.firstCall_replacement_index rate rewards C_star C_h
      z n r u theta hr hcall hearlier hchosen
    have hd := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time rate z rewards C_star C_h n r hr
    rw [ht] at hd
    simp only [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary, hf]
    simpa only [firstCollection, Nat.add_assoc] using hd.trans
      (congrArg (fun n => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n) hi)

/-- The actual lookup/window event has the admitted OLD-selector description. -/
theorem actualDomain_iff_oldSelector (z : SourceInput p) :
    (∃ r : Record rate, actualRecord rate rewards C_star C_h t z = some r ∧
      r ∈ firstCollection (rate := rate) rewards C_star C_h z) ↔
      z ∈ ReferenceFirstCollectionOldRecorderFoundation.oldSelector rate rewards C_star C_h t := by
  let R := completeSuffixRecords rate z rewards C_star C_h
  let w := (firstLiveWindow R).length
  constructor
  · rintro ⟨r, hr, hm⟩
    obtain ⟨call, ht, hread, _⟩ := actual_data rewards C_star C_h z t r hr hm
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hm
    have hget := collection_lookup (rate := rate) R w j hj
    change (collectionWindow R w)[j] = r at he
    rw [he] at hget
    have hd := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time rate z rewards C_star C_h _ r hget
    rw [ht] at hd
    have hb : t.val < ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary rate rewards C_star C_h z := by
      rw [firstCollection_endpoint]
      dsimp only [w, R] at hd
      omega
    refine ⟨?_, ?_⟩
    · exact (ReferenceFirstCollectionPrecallCalendarSupport.before_cut_iff_no_call_through
        rate rewards C_star C_h t z).mp hb
    · simp only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?, hr, Option.bind_some, hread,
        Option.isSome_some, Set.mem_ofPred_eq]
  · rintro ⟨hbefore, hpresent⟩
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hpresent
    obtain ⟨r, hr, hread⟩ := Option.bind_eq_some_iff.mp hc
    have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z := by
      by_contra hn
      rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
        rate rewards C_star C_h t z hn] at hr
      cases hr
    have hw := ReferenceFirstCollectionPrecallCalendarSupport.old_readout_after_firstLiveWindow
      rate rewards C_star C_h t z hlaunch r hr (by rw [hread]; rfl)
    have hb := (ReferenceFirstCollectionPrecallCalendarSupport.before_cut_iff_no_call_through
      rate rewards C_star C_h t z).mpr hbefore
    rw [firstCollection_endpoint] at hb
    let n := t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let j := n - w
    have hj : j < (collectionWindow R w).length := by dsimp [j, n, w, R, firstCollection] at *; omega
    have hget := collection_lookup (rate := rate) R w j hj
    have hi : w + j = n := by dsimp [j, n, w, R, firstCollection] at *; omega
    have hrR : R[n]? = some r := by simpa only [actualRecord, ite_eq_left hlaunch.2] using hr
    rw [hi, hrR] at hget
    refine ⟨r, hr, ?_⟩
    rw [Option.some.inj hget]
    exact List.getElem_mem hj

/-- Actual lookup/window event, retaining genuine absence outside collection. -/
def actualDomain : Set (SourceInput p) := {z | ∃ r : Record rate,
  actualRecord rate rewards C_star C_h t z = some r ∧
    r ∈ firstCollection (rate := rate) rewards C_star C_h z}

theorem measurableSet_actualDomain (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet (actualDomain (rate := rate) rewards C_star C_h t) := by
  have h := ReferenceFirstCollectionOldSelectorRecordingLaw.oldSelector_measurable
    rate rewards C_star C_h control0 t
  have heq : actualDomain (rate := rate) rewards C_star C_h t =
      ReferenceFirstCollectionOldRecorderFoundation.oldSelector rate rewards C_star C_h t := by
    ext z
    exact actualDomain_iff_oldSelector rewards C_star C_h t z
  rw [heq]
  exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (t.val + 1) _ h

/-- Whole-source optional cell, using actual option getters on their proved
domain. Every absent lookup or noncollection date remains absent. -/
def sourceCell? (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (z : SourceInput p) (f x : ContinuousControlSlice.Scalar) : Option (LogicalCell p rate) :=
  if hz : z ∈ actualDomain (rate := rate) rewards C_star C_h t then
    let d : D := ⟨z, hz⟩
    cellWithScalar? rewards C_star C_h z t (rD d) (hrD d) (hmD d) U a0 f x else none

/-- Whole-source reconstruction changes only the next set on present cells. -/
def sourceCellWithNext? (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (z : SourceInput p) (f : ContinuousControlSlice.Scalar) (V : SlowSet p) : Option (LogicalCell p rate) :=
  if hz : z ∈ actualDomain (rate := rate) rewards C_star C_h t then
    let d : D := ⟨z, hz⟩
    cellWithNext? rewards C_star C_h z t (rD d) (hrD d) (hmD d) U a0 f V else none

/-- Explicit PMF/Dirac branches on the complete source, including absence. -/
def sourceRefreshMeasure (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (z : SourceInput p) : Measure (SlowSet p) :=
  if hz : z ∈ actualDomain (rate := rate) rewards C_star C_h t then
    let d : D := ⟨z, hz⟩
    refreshMeasure rewards C_star C_h z t (rD d) (hrD d) (hmD d) U a0 else Measure.dirac U

theorem measurable_sourceCell? (control0 : ContinuousLearningRows.TimeControl p)
    (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar) :
    Measurable (fun v : SourceInput p × (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar) =>
      sourceCell? (rate := rate) rewards C_star C_h t U a0 v.1 v.2.1 v.2.2) := by
  let X := SourceInput p × (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar)
  let E : Set X := {v | v.1 ∈ actualDomain (rate := rate) rewards C_star C_h t}
  have hE : MeasurableSet E := (measurableSet_actualDomain rewards C_star C_h t control0).preimage measurable_fst
  have hz : Measurable (fun v : E => (⟨v.val.1, v.property⟩ : D)) :=
    (measurable_fst.comp measurable_subtype_coe).subtype_mk
  have hpos : Measurable (fun v : E =>
      cellWithScalar? rewards C_star C_h v.val.1 t (rD (⟨v.val.1, v.property⟩ : D))
        (hrD (⟨v.val.1, v.property⟩ : D)) (hmD (⟨v.val.1, v.property⟩ : D))
        U a0 v.val.2.1 v.val.2.2) := by
    change Measurable ((fun v : D × ((Fin p.T → ContinuousControlSlice.Scalar) ×
      (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar)) =>
        cellWithScalar? rewards C_star C_h v.1.val t (rD v.1) (hrD v.1) (hmD v.1)
          U v.2.1 v.2.2.1 v.2.2.2) ∘
      (fun v : E => ((⟨v.val.1, v.property⟩ : D), (a0, v.val.2))))
    apply (measurable_domainCell? rewards C_star C_h t control0 U).comp
    exact hz.prodMk (measurable_const.prodMk (measurable_snd.comp measurable_subtype_coe))
  exact hpos.dite (measurable_const (a := (none : Option (LogicalCell p rate)))) hE

theorem sourceCell_refresh_map (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (z : SourceInput p) (f : ContinuousControlSlice.Scalar) :
    ContinuousControlSlice.scalarLaw.map (sourceCell? (rate := rate) rewards C_star C_h t U a0 z f) =
      (sourceRefreshMeasure (rate := rate) rewards C_star C_h t U a0 z).map
        (sourceCellWithNext? (rate := rate) rewards C_star C_h t U a0 z f) := by
  unfold sourceCell? sourceCellWithNext? sourceRefreshMeasure
  by_cases hz : z ∈ actualDomain (rate := rate) rewards C_star C_h t
  · simp only [dite_eq_left hz]
    exact cell_refresh_map rewards C_star C_h z t (rD (⟨z, hz⟩ : D))
      (hrD (⟨z, hz⟩ : D)) (hmD (⟨z, hz⟩ : D)) U a0 f
  · simp only [dite_eq_right hz, Measure.map_const, measure_univ, one_smul]

/-- Full original-source cell/refresh identity. The SAME extracted `f` feeds
the reconstructed source and canonical FAST. Real private-J strata are summed
with their UNNORMALIZED remainder masses; weights may depend on the remainder. -/
theorem original_source_cell_lintegral (control0 : ContinuousLearningRows.TimeControl p)
    (U : SlowSet p) (a0 : Fin p.T → ContinuousControlSlice.Scalar)
    (test : SourceInput p × Option (LogicalCell p rate) → ENNReal) (htest : Measurable test) :
    ∫⁻ z, ∫⁻ x, test (z, sourceCell? (rate := rate) rewards C_star C_h t U a0 z
        (ReferenceSourceFastScalarDisintegration.sourceFastScalar p t z) x)
        ∂ContinuousControlSlice.scalarLaw ∂BootstrapPrivateRoundStreams.sourceInputLaw p =
      ∑ q : Fin (ConstructorDimensions.M p), ∫⁻ e, ∫⁻ f,
        let zf := (ReferenceSourceFastScalarDisintegration.sourceFastScalarSplit p q t).symm (f, e)
        ∫⁻ V, test (zf, sourceCellWithNext? (rate := rate) rewards C_star C_h t U a0 zf f V)
          ∂sourceRefreshMeasure (rate := rate) rewards C_star C_h t U a0 zf
        ∂ContinuousControlSlice.scalarLaw
        ∂ReferenceSourceFastScalarDisintegration.fastScalarRemainderLaw p q t := by
  let G := fun v : SourceInput p × ContinuousControlSlice.Scalar => ∫⁻ x,
    test (v.1, sourceCell? (rate := rate) rewards C_star C_h t U a0 v.1 v.2 x) ∂ContinuousControlSlice.scalarLaw
  have hC : Measurable (fun v : (SourceInput p × ContinuousControlSlice.Scalar) × ContinuousControlSlice.Scalar =>
      sourceCell? (rate := rate) rewards C_star C_h t U a0 v.1.1 v.1.2 v.2) := by
    change Measurable ((fun v : SourceInput p × (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar) =>
      sourceCell? (rate := rate) rewards C_star C_h t U a0 v.1 v.2.1 v.2.2) ∘
      (fun v : (SourceInput p × ContinuousControlSlice.Scalar) × ContinuousControlSlice.Scalar =>
        (v.1.1, (v.1.2, v.2))))
    apply (measurable_sourceCell? (rate := rate) rewards C_star C_h t control0 U a0).comp
    exact (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hH : Measurable (fun v : (SourceInput p × ContinuousControlSlice.Scalar) × ContinuousControlSlice.Scalar =>
      test (v.1.1, sourceCell? (rate := rate) rewards C_star C_h t U a0 v.1.1 v.1.2 v.2)) :=
    htest.comp ((measurable_fst.comp measurable_fst).prodMk hC)
  have hG : Measurable G := hH.lintegral_prod_right'
  have h := ReferenceSourceFastScalarDisintegration.sourceFastScalar_lintegral p t G hG id measurable_id
  dsimp only [G, id_eq] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro q _
  apply lintegral_congr
  intro e
  apply lintegral_congr
  intro f
  let zf := (ReferenceSourceFastScalarDisintegration.sourceFastScalarSplit p q t).symm (f, e)
  have hlocal : Measurable (fun c : Option (LogicalCell p rate) => test (zf, c)) :=
    htest.comp (measurable_const.prodMk measurable_id)
  have hcell : Measurable (sourceCell? (rate := rate) rewards C_star C_h t U a0 zf f) := by
    change Measurable ((fun v : SourceInput p × (ContinuousControlSlice.Scalar × ContinuousControlSlice.Scalar) =>
      sourceCell? (rate := rate) rewards C_star C_h t U a0 v.1 v.2.1 v.2.2) ∘ (fun x => (zf, (f, x))))
    exact (measurable_sourceCell? (rate := rate) rewards C_star C_h t control0 U a0).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  rw [← lintegral_map hlocal hcell, sourceCell_refresh_map,
    lintegral_map hlocal (measurable_of_countable _)]

end Domain


end Bandits.Support.ReferenceFirstCollectionOneRoundLogicalCell

end
