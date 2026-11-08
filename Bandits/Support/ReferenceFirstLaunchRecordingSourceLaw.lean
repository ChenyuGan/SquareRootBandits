/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLaunchRecordingPhysicalMarker

/-!
# Original-source first-launch recording law

Sources: `sources/zip4/manuscript/06_interruptions.tex:41-64,391-397,408-423`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-58,794-798`.

The actual first physical marker is jointly Borel and has the canonical law
with the entire continuous assignment vector retained. The source stratum and
its measure are the original, unnormalized ones, including the original private
selected index and every private array. These internal laws do not identify an
adapted filtration, service queues, or close a manuscript statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Bandits.Support.ReferenceFirstLaunchRecordingSourceLaw

open ConstructorDimensions ContinuousControlSlice ContinuousLearningRows
open ReferenceFirstLaunchRecordingPhysicalMarker

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev AssignmentVector := ReferenceFirstLaunchRecordingPhysicalMarker.AssignmentVector
abbrev NonAssignmentControl := ReferenceFirstLaunchRecordingPhysicalMarker.NonAssignmentControl

/-- All nonassignment scalars and all original affine samples. -/
def nonAssignmentLaw (p : Parameters) : Measure (NonAssignmentControl p) :=
  (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod (ContinuousLearningRows.affineSamplesLaw p)

instance nonAssignmentLaw_probability (p : Parameters) :
    IsProbabilityMeasure (nonAssignmentLaw p) := by
  unfold nonAssignmentLaw
  infer_instance

/-- The literal unit-anchor recording PMF, with validity from the source cap. -/
def outcomeLaw {p : Parameters} (rate : RateInput p) : Measure (Option (Fin p.K)) :=
  (RecordedRoundMoments.recordingOutcomePMF
    (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
      rate.sourceCap (fun _ => 1) (by intro _; norm_num))).toMeasure

instance outcomeLaw_probability {p : Parameters} (rate : RateInput p) :
    IsProbabilityMeasure (outcomeLaw rate) := by
  unfold outcomeLaw
  infer_instance

theorem outcomeLaw_some {p : Parameters} (rate : RateInput p) (j : Fin p.K) :
    outcomeLaw rate {some j} =
      ENNReal.ofReal (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j) := by
  rw [outcomeLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rfl

theorem outcomeLaw_none {p : Parameters} (rate : RateInput p) :
    outcomeLaw rate {none} =
      ENNReal.ofReal (1 - ∑ j, CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j) := by
  rw [outcomeLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rfl

private theorem univ_nonempty (p : Parameters) :
    (Finset.univ : Finset (ActiveRoundActions.Follower p.m)) ≠ ∅ := by
  have hm := p.two_le_m
  exact Finset.ne_empty_of_mem (Finset.mem_univ
    (⟨0, by simp only [PublicDiscreteDraws.followerCount]; omega⟩ :
      ActiveRoundActions.Follower p.m))

private theorem unit_data_action {p : Parameters} (rate : RateInput p)
    (a : ActiveRoundActions.Assignment p.m p.K) (s : Slice p.m p.K) (i : Fin p.m) :
    SnapshotRecordingKernel.dataAction p (.live a (unoccupiedSnapshot a))
      rate.eta.val rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
      (by intro _; norm_num) (by intro _; norm_num) (by intro _; norm_num)
      (by intro _; norm_num) s i = PublicDiscreteDraws.pilotDraw (K_pos p) i s := by
  by_cases hi : i = ActiveRoundActions.coordinator p.two_le_m <;>
    simp [SnapshotRecordingKernel.dataAction, unoccupiedSnapshot, hi, univ_nonempty p]

/-- With the true assignment fixed, the unit recorder reads only slot, source,
pilots and thin. In particular it ignores every assignment scalar. -/
theorem unitRecordingMap_congr {p : Parameters} (rate : RateInput p)
    (a : ActiveRoundActions.Assignment p.m p.K) (s s' : Slice p.m p.K)
    (h : ∀ c : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p, s c.val = s' c.val) :
    unitRecordingMap rate a s = unitRecordingMap rate a s' := by
  classical
  have hslot : coordinate Label.slot s = coordinate Label.slot s' :=
    h ⟨Label.slot, by simp [Label.slot, Label.assign]⟩
  have hrec : coordinate Label.rec s = coordinate Label.rec s' :=
    h ⟨Label.rec, by simp [Label.rec, Label.assign]⟩
  have hthin : coordinate Label.thin s = coordinate Label.thin s' :=
    h ⟨Label.thin, by simp [Label.thin, Label.assign]⟩
  have hpilot : ∀ i : Fin p.m,
      PublicDiscreteDraws.pilotDraw (K_pos p) i s =
        PublicDiscreteDraws.pilotDraw (K_pos p) i s' := by
    intro i
    have hc := h ⟨Label.pilot i, by simp [Label.pilot, Label.assign]⟩
    simp only [PublicDiscreteDraws.pilotDraw, coordinate] at *
    rw [hc]
  have hmask : ∀ i j, CanonicalRecordingSlice.recordingMask (K_pos p) i j s ↔
      CanonicalRecordingSlice.recordingMask (K_pos p) i j s' := by
    intro i j
    simp only [CanonicalRecordingSlice.recordingMask, hpilot]
  simp only [unitRecordingMap, SnapshotRecordingKernel.recordingMap,
    unit_data_action, hslot, hrec, hthin, hpilot, hmask]

private theorem split_nonassignment {p : Parameters} (v : AssignmentVector p)
    (b : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p)
    (c : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p) :
    ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm (v, b)) c.val = b c := by
  have h := congrArg (fun z => z.2 c)
    ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).apply_symm_apply (v, b))
  simpa [LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv,
    LaunchAssignmentCoordinateSplit.assignmentLabelEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply] using h

theorem currentControl_scalar {p : Parameters} (v : AssignmentVector p)
    (d : NonAssignmentControl p) :
    (currentControl v d).1 =
      (LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm (v, d.1) := rfl

private theorem fixed_assignment_slice_map {p : Parameters} (rate : RateInput p)
    (a : ActiveRoundActions.Assignment p.m p.K) (v : AssignmentVector p) :
    (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).map
        (fun b => unitRecordingMap rate a
          ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm (v, b))) =
      outcomeLaw rate := by
  let g := fun b : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p =>
    unitRecordingMap rate a ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm (v, b))
  have hm : Measurable (unitRecordingMap rate a) :=
    SnapshotRecordingKernel.measurable_recordingMap p (.live a (unoccupiedSnapshot a))
      rate.eta.val rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
      (by intro _; norm_num) (by intro _; norm_num) (by intro _; norm_num)
      (by intro _; norm_num) true
  have hg : Measurable g := hm.comp
    ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm.measurable.comp
      (measurable_const.prodMk measurable_id))
  have heq : ∀ s : Slice p.m p.K, g ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p s).2) =
      unitRecordingMap rate a s := by
    intro s
    apply unitRecordingMap_congr
    intro c
    rw [split_nonassignment]
    have h := split_nonassignment (LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p s).1
      (LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p s).2 c
    rw [(LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm_apply_apply] at h
    exact h.symm
  have hsnd := (measurePreserving_snd
    (μ := ContinuousControlSlice.assignmentLaw p.K)
    (ν := LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p)).comp
      (LaunchAssignmentCoordinateSplit.measurePreserving_sliceAssignmentSplitEquiv p)
  calc
    _ = ((sliceLaw p.m p.K).map
        (Prod.snd ∘ LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p)).map g := by
      rw [hsnd.map_eq]
    _ = (sliceLaw p.m p.K).map (unitRecordingMap rate a) := by
      rw [Measure.map_map hg hsnd.measurable]
      exact congrArg (Measure.map · (sliceLaw p.m p.K)) (funext heq)
    _ = outcomeLaw rate := SnapshotRecordingKernel.map_recordingMap p
      (.live a (unoccupiedSnapshot a)) rate.eta.val rate.eta.property rate.sourceCap
      (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
      (by intro _; norm_num) (by intro _; norm_num)

/-- Every nonassignment-control fibre has the same recorder law, with the
actual sampled assignment held fixed throughout the calculation. -/
theorem fixed_assignment_control_map {p : Parameters} (rate : RateInput p)
    (a : ActiveRoundActions.Assignment p.m p.K) (v : AssignmentVector p) :
    (nonAssignmentLaw p).map (fun d => unitRecordingMap rate a (currentControl v d).1) =
      outcomeLaw rate := by
  have hm : Measurable (fun b : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p =>
      unitRecordingMap rate a ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm (v, b))) :=
    (SnapshotRecordingKernel.measurable_recordingMap p (.live a (unoccupiedSnapshot a))
      rate.eta.val rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
      (by intro _; norm_num) (by intro _; norm_num) (by intro _; norm_num)
      (by intro _; norm_num) true).comp
        ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm.measurable.comp
          (measurable_const.prodMk measurable_id))
  change (nonAssignmentLaw p).map
    ((fun b => unitRecordingMap rate a
      ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm (v, b))) ∘
      Prod.fst) = _
  rw [← Measure.map_map hm measurable_fst]
  change (((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
    (affineSamplesLaw p)).map Prod.fst).map _ = _
  rw [(measurePreserving_fst
    (μ := LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p)
    (ν := affineSamplesLaw p)).map_eq, fixed_assignment_slice_map]

local instance slowSetMeasurableSpace (K m : ℕ) :
    MeasurableSpace (CanonicalOrientedSetLaw.SlowSet K m) := ⊤

/- The following finite gluing index is the already sampled slow set. Its
assignment is exactly the literal first constructor, including the minimum
complement label; it introduces neither a new sampler nor a new random input. -/
private def assignmentOfSlowSet {p : Parameters}
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m) :
    ActiveRoundActions.Assignment p.m p.K where
  assigned := CanonicalAssignmentVector.followerArm p.two_le_m U
  injective := CanonicalAssignmentVector.followerArm_injective p.two_le_m U
  auxiliary := (CanonicalFastSampling.fastArmFinset U).min'
    (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2)
      (CanonicalFastSampling.fastArmFinset_card_ge_two U)))
  auxiliary_outside := by
    intro i
    exact (CanonicalAssignmentVector.followerArm_ne_of_fastCandidate p.two_le_m U
      ⟨_, Finset.min'_mem _
        (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2)
          (CanonicalFastSampling.fastArmFinset_card_ge_two U)))⟩ i).symm

private theorem coordinate_assignment {p : Parameters} (rate : RateInput p)
    (t : Fin p.T) (v : AssignmentVector p) :
    (coordinateLaunch rate t v).start.assignment =
      assignmentOfSlowSet (LaunchAssignmentFibreCoupling.firstLaunchSampler p v) := rfl

/-- Joint Borel dependence on the whole assignment vector and continuous slice,
by finite gluing over the actual sampler's outputs. -/
theorem measurable_sampled_unitRecordingMap {p : Parameters} (rate : RateInput p)
    (t : Fin p.T) :
    Measurable (fun z : AssignmentVector p × Slice p.m p.K =>
      unitRecordingMap rate (coordinateLaunch rate t z.1).start.assignment z.2) := by
  have h : Measurable (fun z : CanonicalOrientedSetLaw.SlowSet p.K p.m × Slice p.m p.K =>
      unitRecordingMap rate (assignmentOfSlowSet z.1) z.2) :=
    measurable_from_prod_countable_right fun U =>
      SnapshotRecordingKernel.measurable_recordingMap p
        (.live (assignmentOfSlowSet U) (unoccupiedSnapshot (assignmentOfSlowSet U)))
        rate.eta.val rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
        (by intro _; norm_num) (by intro _; norm_num)
        (by intro _; norm_num) (by intro _; norm_num) true
  simpa only [Function.comp_def, coordinate_assignment] using h.comp
    (((LaunchAssignmentFibreCoupling.measurable_firstLaunchSampler p).comp
      measurable_fst).prodMk measurable_snd)

theorem measurable_sampled_assigned {p : Parameters} (rate : RateInput p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    Measurable (fun v : AssignmentVector p =>
      (coordinateLaunch rate t v).start.assignment.assigned i) := by
  exact (measurable_of_countable
    (fun U : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
      CanonicalAssignmentVector.followerArm p.two_le_m U i)).comp
        (LaunchAssignmentFibreCoupling.measurable_firstLaunchSampler p)

section RetainedSource

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (control0 : TimeControl p)

local notation "X" => RetainedStart rate rewards C_star C_h q t control0
local notation "μC" => ReferenceRetainedSourceCoupling.retainedRemainderMeasure
  rate rewards C_star C_h q t t.val le_rfl control0
local notation "V" => AssignmentVector p
local notation "Dctl" => NonAssignmentControl p
local notation "Iphys" => physicalMarker rate rewards C_star C_h q t control0

/-- The actual marker, with the retained original point, complete assignment
vector and every other current control varying jointly. -/
theorem measurable_physicalMarker :
    Measurable (fun z : X × (V × Dctl) => Iphys z.1 z.2.1 z.2.2) := by
  have hc : Measurable (fun z : X × (V × Dctl) =>
      (currentControl z.2.1 z.2.2).1) :=
    measurable_fst.comp ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm.measurable.comp
      measurable_snd)
  have h := (measurable_sampled_unitRecordingMap rate t).comp
    ((measurable_fst.comp measurable_snd).prodMk hc)
  have heq := funext (fun z : X × (V × Dctl) =>
    physical_marker_eq rate rewards C_star C_h q t control0 z.1 z.2.1 z.2.2)
  rw [heq]
  exact h

/-- Beyond the stated retained-source membership, every fibre law is proved
without a supplied Borel or probability-law premise. -/
theorem map_physicalMarker (x : X) (v : V) :
    (nonAssignmentLaw p).map (Iphys x v) = outcomeLaw rate := by
  have heq : Iphys x v = fun d =>
      unitRecordingMap rate (coordinateLaunch rate t v).start.assignment (currentControl v d).1 :=
    funext (physical_marker_eq rate rewards C_star C_h q t control0 x v)
  rw [heq]
  exact fixed_assignment_control_map rate _ v

/-- The current actual checked log emission's contribution for the true assigned
follower. The buffer and observation are those of the physical record. -/
def currentSaved (x : X) (v : V) (d : Dctl) (i : Fin (p.m - 1)) : ℕ :=
  let payload := payload rate rewards C_star C_h q t control0 x v d
  let record := record rate rewards C_star C_h q t control0 x v d
  SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ) rate.eta.val
    (payload.exponent (payload.assignment.assigned i)) (payload.assignment.assigned i)
    (record.input.time.val + 1) (ReferenceFollowerBufferProvenance.logEmission i record)

/-- Literal finite-outcome floor formula for that existing physical emission. -/
theorem currentSaved_eq (x : X) (v : V) (d : Dctl) (i : Fin (p.m - 1)) :
    currentSaved rate rewards C_star C_h q t control0 x v d i =
      if Iphys x v d = some ((coordinateLaunch rate t v).start.assignment.assigned i) then
        Nat.floor ((rate.n : ℝ) *
          (((rewards t ((coordinateLaunch rate t v).start.assignment.assigned i)).val : ℝ) /
            (D p : ℝ)) /
          CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1)
            ((coordinateLaunch rate t v).start.assignment.assigned i)) else 0 := by
  unfold currentSaved
  rw [current_saved_eq_numerical_arrival,
    (numerical_cell_readout rate rewards C_star C_h q t control0 x v d).2.2,
    payload_assignment]

/-- Joint Borel first and square contributions of the actual checked emission. -/
theorem measurable_currentSaved (i : Fin (p.m - 1)) :
    Measurable (fun z : X × (V × Dctl) =>
      currentSaved rate rewards C_star C_h q t control0 z.1 z.2.1 z.2.2 i) := by
  have hfinite := measurable_of_countable (fun z : Option (Fin p.K) × Fin p.K =>
    if z.1 = some z.2 then Nat.floor ((rate.n : ℝ) *
      (((rewards t z.2).val : ℝ) / (D p : ℝ)) /
      CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) z.2) else 0)
  have h := hfinite.comp
    ((measurable_physicalMarker rate rewards C_star C_h q t control0).prodMk
      ((measurable_sampled_assigned rate t i).comp (measurable_fst.comp measurable_snd)))
  have heq := funext (fun z : X × (V × Dctl) =>
    currentSaved_eq rate rewards C_star C_h q t control0 z.1 z.2.1 z.2.2 i)
  rw [heq]
  exact h

theorem measurable_currentSaved_real_square (i : Fin (p.m - 1)) :
    Measurable (fun z : X × (V × Dctl) =>
      ((currentSaved rate rewards C_star C_h q t control0 z.1 z.2.1 z.2.2 i : ℝ),
        (currentSaved rate rewards C_star C_h q t control0 z.1 z.2.1 z.2.2 i : ℝ) ^ 2)) := by
  have h := (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (measurable_currentSaved rate rewards C_star C_h q t control0 i)
  exact h.prodMk (h.pow_const 2)

/-- First expose the retained point and the entire vector, then the actual
marker. No normalization or positive-mass premise occurs. -/
theorem retained_joint_map :
    ((μC).prod ((assignmentLaw p.K).prod (nonAssignmentLaw p))).map
        (fun z : X × (V × Dctl) => ((z.1, z.2.1), Iphys z.1 z.2.1 z.2.2)) =
      ((μC).prod (assignmentLaw p.K)).prod (outcomeLaw rate) := by
  have ha : Measurable (fun z : (X × V) × Dctl => (z.1.1, (z.1.2, z.2))) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun z : (X × V) × Dctl => Iphys z.1.1 z.1.2 z.2) := by
    simpa only [Function.comp_def] using
      (measurable_physicalMarker rate rewards C_star C_h q t control0).comp ha
  have h := (MeasurePreserving.id ((μC).prod (assignmentLaw p.K))).skew_product hm
    (Filter.Eventually.of_forall (fun z : X × V =>
      map_physicalMarker rate rewards C_star C_h q t control0 z.1 z.2))
  exact (h.comp (measurePreserving_prodAssoc μC (assignmentLaw p.K)
    (nonAssignmentLaw p)).symm).map_eq

end RetainedSource

/-- The actual first-launch stratum has elapsed boundary literally t.val. -/
def firstStratumIndex {p : Parameters} (q : Fin (M p)) (t : Fin p.T) :
    ReferenceTotalSourceDisintegration.StratumIndex t :=
  (q, ⟨t.val, Nat.lt_succ_self t.val⟩)

section OriginalSource

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (control0 : TimeControl p)

local notation "i₀" => firstStratumIndex q t
local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum
  rate rewards C_star C_h t i₀
local notation "X" => RetainedStart rate rewards C_star C_h q t control0
local notation "μZ" => ReferenceTotalSourceDisintegration.sourceStratumMeasure
  rate rewards C_star C_h t i₀
local notation "μC" => ReferenceRetainedSourceCoupling.retainedRemainderMeasure
  rate rewards C_star C_h q t t.val le_rfl control0
local notation "V" => AssignmentVector p
local notation "Dctl" => NonAssignmentControl p
local notation "e" => ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t

/-- The existing retained selector and the literal original current control. -/
def sourceControlCoordinates (z : Z) : X × TimeControl p :=
  (ReferenceTotalSourceDisintegration.sourceRetainedInput
    rate rewards C_star C_h t control0 i₀ z, (z.val.1.2 q).2 t)

theorem measurable_sourceControlCoordinates :
    Measurable (sourceControlCoordinates rate rewards C_star C_h q t control0) :=
  (ReferenceTotalSourceDisintegration.measurable_sourceRetainedInput
    rate rewards C_star C_h t control0 i₀).prodMk
      (measurable_fst.comp ((e).measurable.comp measurable_subtype_coe))

/-- Invert only on the actual source stratum, retaining the whole source. -/
def restoreSource (z : X × TimeControl p) : Z :=
  ⟨ReferenceRetainedSourceCoupling.retainedSourceMap
      rate rewards C_star C_h q t t.val le_rfl control0 z,
    (ReferenceRetainedSourceCoupling.retainedSourceEvent_reconstruct_iff
      rate rewards C_star C_h q t t.val le_rfl control0 z.1.val z.2).mpr z.1.property⟩

theorem measurable_restoreSource :
    Measurable (restoreSource rate rewards C_star C_h q t control0) :=
  (ReferenceRetainedSourceCoupling.measurable_retainedSourceMap
    rate rewards C_star C_h q t t.val le_rfl control0).subtype_mk

theorem sourceControlCoordinates_restoreSource (z : X × TimeControl p) :
    sourceControlCoordinates rate rewards C_star C_h q t control0
        (restoreSource rate rewards C_star C_h q t control0 z) = z := by
  apply Prod.ext
  · apply Subtype.ext
    change (ReferenceTotalSourceDisintegration.sourceRetainedInput
      rate rewards C_star C_h t control0 i₀
      (restoreSource rate rewards C_star C_h q t control0 z)).val = z.1.val
    rw [ReferenceTotalSourceDisintegration.sourceRetainedInput_val]
    exact congrArg Prod.snd ((e).apply_symm_apply (z.2, z.1.val))
  · exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_control p q t z.2 z.1.val

theorem map_restoreSource :
    ((μC).prod (timeControlLaw p)).map (restoreSource rate rewards C_star C_h q t control0) = μZ := by
  apply (MeasurableEmbedding.subtype_coe
    (ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h t control0 i₀)).map_injective
  rw [Measure.map_map measurable_subtype_coe
    (measurable_restoreSource rate rewards C_star C_h q t control0),
    ReferenceTotalSourceDisintegration.sourceStratumMeasure_map
      rate rewards C_star C_h t control0 i₀]
  exact ReferenceRetainedSourceCoupling.retainedSourceMap_product
    rate rewards C_star C_h q t t.val le_rfl control0

theorem map_sourceControlCoordinates :
    (μZ).map (sourceControlCoordinates rate rewards C_star C_h q t control0) =
      (μC).prod (timeControlLaw p) := by
  rw [← map_restoreSource rate rewards C_star C_h q t control0,
    Measure.map_map (measurable_sourceControlCoordinates rate rewards C_star C_h q t control0)
      (measurable_restoreSource rate rewards C_star C_h q t control0)]
  have heq : sourceControlCoordinates rate rewards C_star C_h q t control0 ∘
      restoreSource rate rewards C_star C_h q t control0 = id :=
    funext (sourceControlCoordinates_restoreSource rate rewards C_star C_h q t control0)
  rw [heq, Measure.map_id]

/-- The entire original assignment vector, including orientation, and all
nonassignment/affine coordinates, from the same original selected row. -/
def sourceCoordinates (z : Z) : X × (V × Dctl) :=
  ((sourceControlCoordinates rate rewards C_star C_h q t control0 z).1,
    LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p ((z.val.1.2 q).2 t))

theorem measurable_sourceCoordinates :
    Measurable (sourceCoordinates rate rewards C_star C_h q t control0) :=
  ((measurable_id.prodMap
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).measurable).comp
      (measurable_sourceControlCoordinates rate rewards C_star C_h q t control0))

theorem map_sourceCoordinates :
    (μZ).map (sourceCoordinates rate rewards C_star C_h q t control0) =
      (μC).prod ((assignmentLaw p.K).prod (nonAssignmentLaw p)) := by
  change (μZ).map (Prod.map id (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p) ∘
    sourceControlCoordinates rate rewards C_star C_h q t control0) = _
  rw [← Measure.map_map
    (measurable_id.prodMap (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).measurable)
    (measurable_sourceControlCoordinates rate rewards C_star C_h q t control0),
    map_sourceControlCoordinates]
  exact ((MeasurePreserving.id μC).prod
    (LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p)).map_eq

/-- Reconstructing these coordinates returns the SAME complete source,
including the original private J, all private arrays, IDs and every full row. -/
theorem source_recover (z : Z) :
    let c := sourceCoordinates rate rewards C_star C_h q t control0 z
    source rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 = z.val := by
  dsimp only [sourceCoordinates, sourceControlCoordinates, source, currentControl]
  rw [(LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm_apply_apply]
  change (e).symm ((z.val.1.2 q).2 t,
    (ReferenceTotalSourceDisintegration.sourceRetainedInput
      rate rewards C_star C_h t control0 i₀ z).val) = z.val
  rw [ReferenceTotalSourceDisintegration.sourceRetainedInput_val]
  exact (e).symm_apply_apply z.val

/-- The transported record is literally the actual first physical record of
the original source, using the stratum's actual crossing and elapsed time. -/
theorem source_record_eq (z : Z) :
    let c := sourceCoordinates rate rewards C_star C_h q t control0 z
    record rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 =
      ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h
        z.property.2.1 (by rw [z.property.2.2]; exact t.isLt) := by
  dsimp only
  unfold record
  simp only [source_recover rate rewards C_star C_h q t control0 z]

/-- Actual marker on this original-source stratum; no off-stratum extension. -/
def sourceMarker (z : Z) : Option (Fin p.K) :=
  let c := sourceCoordinates rate rewards C_star C_h q t control0 z
  physicalMarker rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2

/-- This is the literal first physical record's coordinator-or-saved-candidate
marker, with its own actual first payload, on the unchanged original source. -/
theorem sourceMarker_eq_actual (z : Z) :
    sourceMarker rate rewards C_star C_h q t control0 z =
      let r := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
        rate z.val rewards C_star C_h z.property.2.1
        (by rw [z.property.2.2]; exact t.isLt)
      ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord r
        (AssignmentStartPayload.Input.ofFirstAssignment
          (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput r.input)))
        true := by
  exact congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
    ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord r
      (AssignmentStartPayload.Input.ofFirstAssignment
        (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput r.input))) true)
    (source_record_eq rate rewards C_star C_h q t control0 z)

theorem measurable_sourceMarker :
    Measurable (sourceMarker rate rewards C_star C_h q t control0) :=
  (measurable_physicalMarker rate rewards C_star C_h q t control0).comp
    (measurable_sourceCoordinates rate rewards C_star C_h q t control0)

/-- Whole-vector and actual-marker joint pushforward on the inherited original
source measure. In particular no independent redraw of J is inserted. -/
theorem source_joint_map :
    (μZ).map (fun z : Z =>
      let c := sourceCoordinates rate rewards C_star C_h q t control0 z
      ((c.1, c.2.1), sourceMarker rate rewards C_star C_h q t control0 z)) =
        ((μC).prod (assignmentLaw p.K)).prod (outcomeLaw rate) := by
  have hm : Measurable (fun z : X × (V × Dctl) =>
      ((z.1, z.2.1), physicalMarker rate rewards C_star C_h q t control0 z.1 z.2.1 z.2.2)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_physicalMarker rate rewards C_star C_h q t control0)
  change (μZ).map ((fun z : X × (V × Dctl) =>
    ((z.1, z.2.1), physicalMarker rate rewards C_star C_h q t control0 z.1 z.2.1 z.2.2)) ∘
      sourceCoordinates rate rewards C_star C_h q t control0) = _
  rw [← Measure.map_map hm (measurable_sourceCoordinates rate rewards C_star C_h q t control0),
    map_sourceCoordinates]
  exact retained_joint_map rate rewards C_star C_h q t control0

/-- Arbitrary Borel retained-source and whole-vector cylinders, including
zero-mass strata and zero-mass test sets, with the literal physical marker. -/
theorem source_joint_cylinder (Aset : Set X) (Bset : Set V)
    (hA : MeasurableSet Aset) (hB : MeasurableSet Bset) (o : Option (Fin p.K)) :
    μZ {z | (sourceCoordinates rate rewards C_star C_h q t control0 z).1 ∈ Aset ∧
      (sourceCoordinates rate rewards C_star C_h q t control0 z).2.1 ∈ Bset ∧
      sourceMarker rate rewards C_star C_h q t control0 z = o} =
        μC Aset * assignmentLaw p.K Bset * outcomeLaw rate {o} := by
  have hm : Measurable (fun z : Z =>
      (((sourceCoordinates rate rewards C_star C_h q t control0 z).1,
        (sourceCoordinates rate rewards C_star C_h q t control0 z).2.1),
        sourceMarker rate rewards C_star C_h q t control0 z)) :=
    ((measurable_fst.comp (measurable_sourceCoordinates rate rewards C_star C_h q t control0)).prodMk
      ((measurable_fst.comp measurable_snd).comp
        (measurable_sourceCoordinates rate rewards C_star C_h q t control0))).prodMk
      (measurable_sourceMarker rate rewards C_star C_h q t control0)
  have h := congrArg (fun m : Measure ((X × V) × Option (Fin p.K)) =>
      m ((Aset ×ˢ Bset) ×ˢ {o})) (source_joint_map rate rewards C_star C_h q t control0)
  rw [Measure.map_apply hm ((hA.prod hB).prod (measurableSet_singleton o)),
    Measure.prod_prod, Measure.prod_prod] at h
  simpa only [Set.preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_ofPred_eq,
    and_assoc] using h

theorem source_joint_some (Aset : Set X) (Bset : Set V)
    (hA : MeasurableSet Aset) (hB : MeasurableSet Bset) (j : Fin p.K) :
    μZ {z | (sourceCoordinates rate rewards C_star C_h q t control0 z).1 ∈ Aset ∧
      (sourceCoordinates rate rewards C_star C_h q t control0 z).2.1 ∈ Bset ∧
      sourceMarker rate rewards C_star C_h q t control0 z = some j} =
        μC Aset * assignmentLaw p.K Bset *
          ENNReal.ofReal (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j) := by
  rw [source_joint_cylinder rate rewards C_star C_h q t control0 Aset Bset hA hB,
    outcomeLaw_some]

theorem source_joint_none (Aset : Set X) (Bset : Set V)
    (hA : MeasurableSet Aset) (hB : MeasurableSet Bset) :
    μZ {z | (sourceCoordinates rate rewards C_star C_h q t control0 z).1 ∈ Aset ∧
      (sourceCoordinates rate rewards C_star C_h q t control0 z).2.1 ∈ Bset ∧
      sourceMarker rate rewards C_star C_h q t control0 z = none} =
        μC Aset * assignmentLaw p.K Bset *
          ENNReal.ofReal (1 - ∑ j, CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j) := by
  rw [source_joint_cylinder rate rewards C_star C_h q t control0 Aset Bset hA hB,
    outcomeLaw_none]

end OriginalSource

end Bandits.Support.ReferenceFirstLaunchRecordingSourceLaw
