/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionSamplerChronology

/-!
# Original-source joint fibre transport at an arbitrary collection rank

The rank is an observer of the actual physical records. Each cell is taken at
its own pre-choice date. The joint observation retains the entire original
source, the existing strict-past mark, every optional checked outcome, and the
whole current assignment vector. All cell measures remain unnormalized.

This single-rank law does not assert consistency of earlier marks under later
adaptive composition. Its intended consumer is
`ReferenceChronologicalCollectionPhysicalMarginalInduction`.

Sources: `06_interruptions.tex:355-426` and
`appendix_b_communication.tex:25-58`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Bandits.Support.ReferenceCollectionRankCellPhysicalTransport

open ReferenceFixedTimeSourceControlCoupling
  (replaceSourceControl fixedControlSplit fixedControlSourceStratum
    fixedControlRemainderLaw fixedControlRemainderStratum sourceCoordinatorIndex)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)
open ReferenceCalendarLaterSamplerPredictability (calendarParameters)
open AssignmentParameterFibreKernel (fibreMass fibreMeasure successfulSlowSet)
open ReferenceLaterOptionalControlResampling (controlRemainderLaw)
open LaunchAssignmentCoordinateSplit (controlAssignmentSplitEquiv)
open ContinuousLearningRows (TimeControl timeControlLaw)
open BootstrapPrivateRoundStreams (sourceInputLaw)
open ReferenceFirstCollectionOriginalSourceFibreTransport
  (SourceInput Outcome AssignmentVector JointY originalSourceSection
    sourcePrefix_replaceSourceControl calendarParameters_replaceSourceControl)

local instance sourceInputMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance outcomeMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (Outcome p) := ⊤
local instance outcomeDiscreteMeasurableSpace (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (Outcome p) := ⟨fun _ => trivial⟩
local instance outcomeOptionMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (Option (Outcome p)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The literal own-date cutoff event for rank `k`. -/
def rankCell (k : ℕ) (u s : Fin p.T) : Set (SourceInput p) :=
  {z | (ReferenceCollectionSamplerChronology.nthAt
    rate rewards C_star C_h k s z).map Prod.fst = some u}

/-- Actual absence of the kth invocation, distinct from a present failed draw. -/
def rankNoCall (k : ℕ) : Set (SourceInput p) :=
  {z | ReferenceCollectionSamplerChronology.nthCollectionCall
    rate rewards C_star C_h k z = none}

/-- Add the existing marked payload to the actual ranked invocation. -/
def rankPastFibreOutput (k : ℕ) (control0 : TimeControl p)
    (z : SourceInput p) : ReferenceFirstCollectionPastSamplerFibreLaw.PastFibreY p :=
  (ReferenceCollectionSamplerChronology.nthCollectionCall
    rate rewards C_star C_h k z).map
    (fun c => (c.1, (c.2.1,
      ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
        rate rewards C_star C_h control0 c.2.1 z)))

/-- Keep the entire original source jointly with its ranked marked output. -/
def rankOriginalSourceOutput (k : ℕ) (control0 : TimeControl p)
    (z : SourceInput p) : JointY p :=
  (z, rankPastFibreOutput rate rewards C_star C_h k control0 z)

/-- A Borel indicator of the literal joint observation. -/
def rankOriginalSourceTest (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (z : SourceInput p) : ℝ :=
  B.indicator (fun _ => (1 : ℝ))
    (rankOriginalSourceOutput rate rewards C_star C_h k control0 z)

/-- Cell membership retains exactly the original cutoff and invocation date. -/
theorem mem_rankCell_iff_originalTags (k : ℕ) (u s : Fin p.T)
    (z : SourceInput p) :
    z ∈ rankCell rate rewards C_star C_h k u s ↔
      (ReferenceCollectionSamplerChronology.nthCollectionCall
        rate rewards C_star C_h k z).map (fun c => (c.1, c.2.1)) = some (u, s) := by
  cases hc : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z with
  | none => simp [rankCell, ReferenceCollectionSamplerChronology.nthAt, hc]
  | some c =>
      rcases c with ⟨v, t, theta⟩
      by_cases ht : t = s
      · subst t
        simp [rankCell, ReferenceCollectionSamplerChronology.nthAt, hc]
      · simp [rankCell, ReferenceCollectionSamplerChronology.nthAt, hc, ht]

/-- A cell supplies its actual parameter; no record or matching-state premise. -/
theorem mem_rankCell_iff_exists_call (k : ℕ) (u s : Fin p.T)
    (z : SourceInput p) :
    z ∈ rankCell rate rewards C_star C_h k u s ↔
      ∃ theta, ReferenceCollectionSamplerChronology.nthCollectionCall
        rate rewards C_star C_h k z = some (u, (s, theta)) := by
  rw [mem_rankCell_iff_originalTags]
  constructor
  · intro h
    obtain ⟨⟨v, t, theta⟩, hc, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨theta, hc⟩
  · rintro ⟨theta, hc⟩
    simp only [hc, Option.map_some]

/-- The event belongs to the original source field strictly before its draw. -/
theorem rankCell_measurable (control0 : TimeControl p) (k : ℕ) (u s : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (s.val + 1)] (rankCell rate rewards C_star C_h k u s) :=
  ReferenceCollectionSamplerChronology.nthAt_cutoff_event_measurable
    rate rewards C_star C_h control0 k u s

/-- The same event is Borel for the complete original source. -/
theorem rankCell_borel (control0 : TimeControl p) (k : ℕ) (u s : Fin p.T) :
    MeasurableSet (rankCell rate rewards C_star C_h k u s) :=
  ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le
    (s.val + 1)) _ (rankCell_measurable rate rewards C_star C_h control0 k u s)

/-- Current-control replacement preserves this cell, without a future-call claim. -/
theorem rankCell_replaceSourceControl_iff (control0 : TimeControl p)
    (k : ℕ) (u s : Fin p.T) (z : SourceInput p) (c : TimeControl p) :
    replaceSourceControl p s z c ∈ rankCell rate rewards C_star C_h k u s ↔
      z ∈ rankCell rate rewards C_star C_h k u s := by
  change (ReferenceCollectionSamplerChronology.nthAt rate rewards C_star C_h k s
    (replaceSourceControl p s z c)).map Prod.fst = some u ↔ _
  rw [ReferenceCollectionSamplerChronology.nthAt_replaceSourceControl
    rate rewards C_star C_h control0 k s z c]
  rfl

/-- The actual cell supplies a genuine record, selected output, complete vector,
checked operation code and optional sampler outcome, including checked failure. -/
theorem rankCell_actualSamplerTrace (k : ℕ) (u s : Fin p.T)
    (z : SourceInput p) (hz : z ∈ rankCell rate rewards C_star C_h k u s) :
    ∃ (theta : AssignmentParameterFibreKernel.Theta p) (n : ℕ)
      (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
      (o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p),
      ReferenceCollectionSamplerChronology.nthCollectionCall
        rate rewards C_star C_h k z = some (u, (s, theta)) ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[n]? = some r ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h s z = some r ∧
      r.input.time = s ∧
      ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta) ∧
      calendarParameters rate rewards C_star C_h s z = some theta ∧
      ReferenceCalendarLaterSamplerOutputSections.outputAt
        rate rewards C_star C_h s z = some o ∧
      o.2.1 = some theta ∧
      o.2.2.2.1 = ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector s z ∧
      o.1 = LaterAssignmentStartMeasurability.codeOfCheckedSample p
        (CheckedAssignmentSample.checkedAssignmentSample p theta.1 theta.2
          (ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector s z)) ∧
      ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt
        rate rewards C_star C_h s z = some (successfulSlowSet p theta
          (ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector s z)) := by
  obtain ⟨theta, hc⟩ :=
    (mem_rankCell_iff_exists_call rate rewards C_star C_h k u s z).mp hz
  obtain ⟨n, r, hr, ha, ht, hcall, hp, _⟩ :=
    ReferenceCollectionSamplerChronology.nthCollectionCall_actualRecord
      rate rewards C_star C_h k z u s theta hc
  have houtput := (ReferenceCalendarLaterSamplerOutputSections.outputAt_parameters
    rate rewards C_star C_h s z).trans hp
  obtain ⟨o, ho, hop⟩ := Option.bind_eq_some_iff.mp houtput
  obtain ⟨hv, hcode⟩ := ReferenceCalendarLaterSamplerOutputSections.outputAt_code_vector
    rate rewards C_star C_h s z o theta ho hop
  have houtcome := ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt_eq_selectedSampler
    rate rewards C_star C_h s z o theta ho hop
  exact ⟨theta, n, r, o, hc, hr, ha, ht, hcall, hp, ho, hop, hv, hcode, houtcome⟩

/-- On a present cell the literal observer is its existing marked pair. -/
theorem rankPastFibreOutput_on_cell (k : ℕ) (control0 : TimeControl p)
    (u s : Fin p.T) (z : SourceInput p)
    (hz : z ∈ rankCell rate rewards C_star C_h k u s) :
    rankPastFibreOutput rate rewards C_star C_h k control0 z =
      some (u, (s, ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
        rate rewards C_star C_h control0 s z)) := by
  obtain ⟨theta, hc⟩ :=
    (mem_rankCell_iff_exists_call rate rewards C_star C_h k u s z).mp hz
  simp only [rankPastFibreOutput, hc, Option.map_some]

/-- Absence is the complement of the finite union of all actual rank cells. -/
theorem rankNoCall_eq_compl_cells (k : ℕ) :
    rankNoCall rate rewards C_star C_h k =
      (⋃ u : Fin p.T, ⋃ s : Fin p.T, rankCell rate rewards C_star C_h k u s)ᶜ := by
  ext z
  cases hc : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z with
  | none => simp [rankNoCall, mem_rankCell_iff_originalTags, hc]
  | some c =>
      rcases c with ⟨u, s, theta⟩
      simp [rankNoCall, mem_rankCell_iff_originalTags, hc]

/-- No-call is Borel; no arbitrary discrete structure on parameters is used. -/
theorem rankNoCall_measurable (control0 : TimeControl p) (k : ℕ) :
    MeasurableSet (rankNoCall rate rewards C_star C_h k) := by
  rw [rankNoCall_eq_compl_cells]
  exact (MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun s =>
    rankCell_borel rate rewards C_star C_h control0 k u s).compl

private theorem rankPastFibreOutput_preimage_eq (k : ℕ) (control0 : TimeControl p)
    (B : Set (ReferenceFirstCollectionPastSamplerFibreLaw.PastFibreY p)) :
    rankPastFibreOutput rate rewards C_star C_h k control0 ⁻¹' B =
      (if none ∈ B then rankNoCall rate rewards C_star C_h k else ∅) ∪
      ⋃ u : Fin p.T, ⋃ s : Fin p.T,
        rankCell rate rewards C_star C_h k u s ∩
          (ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
            rate rewards C_star C_h control0 s ⁻¹'
              ReferenceFirstCollectionPastSamplerFibreLaw.stratumSet B u s) := by
  ext z
  cases hc : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z with
  | none =>
      simp [rankPastFibreOutput, rankNoCall,
        ReferenceFirstCollectionPastSamplerFibreLaw.stratumSet,
        mem_rankCell_iff_originalTags, hc]
  | some c =>
      rcases c with ⟨u, s, theta⟩
      simp [rankPastFibreOutput, rankNoCall,
        ReferenceFirstCollectionPastSamplerFibreLaw.stratumSet,
        ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair,
        mem_rankCell_iff_originalTags, hc]

/-- The finite own-date partition proves Borelness without discretizing rows. -/
theorem rankPastFibreOutput_measurable (k : ℕ) (control0 : TimeControl p) :
    Measurable (rankPastFibreOutput rate rewards C_star C_h k control0) := by
  intro B hB
  rw [rankPastFibreOutput_preimage_eq rate rewards C_star C_h k control0 B]
  apply MeasurableSet.union
  · split_ifs
    · exact rankNoCall_measurable rate rewards C_star C_h control0 k
    · exact MeasurableSet.empty
  · exact MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun s =>
      (rankCell_borel rate rewards C_star C_h control0 k u s).inter
        ((ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair_measurable
          rate rewards C_star C_h control0 s)
          (ReferenceFirstCollectionPastSamplerFibreLaw.stratumSet_measurable B hB u s))

/-- Joint Borelness retains the original source identity coordinate. -/
theorem rankOriginalSourceOutput_measurable (k : ℕ) (control0 : TimeControl p) :
    Measurable (rankOriginalSourceOutput rate rewards C_star C_h k control0) :=
  measurable_id.prodMk (rankPastFibreOutput_measurable rate rewards C_star C_h k control0)

/-- Every joint indicator test is Borel. -/
theorem rankOriginalSourceTest_measurable (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    Measurable (rankOriginalSourceTest rate rewards C_star C_h k control0 B) :=
  (measurable_const.indicator hB).comp
    (rankOriginalSourceOutput_measurable rate rewards C_star C_h k control0)

private theorem indicator_bounds {Y : Type*} (B : Set Y) (y : Y) :
    0 ≤ B.indicator (fun _ => (1 : ℝ)) y ∧
      B.indicator (fun _ => (1 : ℝ)) y ≤ 1 := by
  by_cases hy : y ∈ B <;> simp [Set.indicator, hy]

private theorem bounded_integrable {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (f : Y → ℝ) (hf : Measurable f)
    (hb : ∀ y, ‖f y‖ ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall hb

private theorem integrable_test {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    [IsFiniteMeasure μ] (f : X → Y) (hf : Measurable f)
    (B : Set Y) (hB : MeasurableSet B) :
    Integrable (fun x => B.indicator (fun _ => (1 : ℝ)) (f x)) μ := by
  apply bounded_integrable μ _ ((measurable_const.indicator hB).comp hf)
  intro x
  obtain ⟨h0, h1⟩ := indicator_bounds B (f x)
  simpa only [Function.comp_apply, Real.norm_of_nonneg h0] using h1

/-- Every Borel indicator is integrable under the whole original law. -/
theorem rankOriginalSourceTest_integrable (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    Integrable (rankOriginalSourceTest rate rewards C_star C_h k control0 B)
      (sourceInputLaw p) :=
  integrable_test _ _
    (rankOriginalSourceOutput_measurable rate rewards C_star C_h k control0) B hB

/-- Rank zero is exactly the accepted first-call joint observation. -/
theorem rankOriginalSourceOutput_zero (control0 : TimeControl p) (z : SourceInput p) :
    rankOriginalSourceOutput rate rewards C_star C_h 0 control0 z =
      ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceOutput
        rate rewards C_star C_h control0 z := by
  simp only [rankOriginalSourceOutput, rankPastFibreOutput,
    ReferenceCollectionSamplerChronology.nthCollectionCall_zero,
    ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceOutput,
    ReferenceFirstCollectionPastSamplerFibreLaw.pastFibreOutput,
    ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair]

private theorem vector_replacement (t : Fin p.T) (z : SourceInput p)
    (c : TimeControl p) :
    ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t
      (replaceSourceControl p t z c) = ContinuousControlSlice.assignmentVector c.1 := by
  simp [ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector,
    ReferenceSourceCurrentControlFreshness.u_t, replaceSourceControl,
    sourceCoordinatorIndex, ActualInitializationPhysicalStep.selectedRowIndex]

private theorem source_partition_integral (f : SourceInput p → ℝ)
    (hf : Integrable f (sourceInputLaw p)) :
    (∫ z, f z ∂sourceInputLaw p) =
      ∑ q : Fin (ConstructorDimensions.M p),
        ∫ z in fixedControlSourceStratum p q, f z ∂sourceInputLaw p := by
  have hindex : Measurable (sourceCoordinatorIndex p) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hp : (∑ q : Fin (ConstructorDimensions.M p),
      (sourceInputLaw p).restrict (fixedControlSourceStratum p q)) = sourceInputLaw p :=
    FiniteFibreLift.sum_restrict_fibre (sourceInputLaw p) (sourceCoordinatorIndex p) hindex
  conv_lhs => rw [← hp]
  exact integral_finsetSum_measure (fun _ _ => hf.integrableOn)

private theorem resampling_integral (t : Fin p.T) (f : SourceInput p → ℝ)
    (hf : Measurable f) (hb : ∀ z, ‖f z‖ ≤ 1) :
    (∫ z, f z ∂sourceInputLaw p) =
      ∫ z, ∫ c, f (replaceSourceControl p t z c) ∂timeControlLaw p
        ∂sourceInputLaw p := by
  let g : SourceInput p → ℝ := fun z =>
    ∫ c, f (replaceSourceControl p t z c) ∂timeControlLaw p
  have hg : Measurable g :=
    (hf.comp (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl
      p t)).stronglyMeasurable.integral_prod_right'.measurable
  have hgb : ∀ z, ‖g z‖ ≤ 1 := by
    intro z
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const
        (μ := timeControlLaw p) (Filter.Eventually.of_forall fun c => hb
          (replaceSourceControl p t z c)))
  have hfi := bounded_integrable (sourceInputLaw p) f hf hb
  have hgi := bounded_integrable (sourceInputLaw p) g hg hgb
  rw [source_partition_integral f hfi, source_partition_integral g hgi]
  apply Finset.sum_congr rfl
  intro q _
  let e := fixedControlSplit p q t
  let η := (fixedControlRemainderLaw p q t).restrict (fixedControlRemainderStratum p q t)
  have hmap : ((timeControlLaw p).prod η).map e.symm =
      (sourceInputLaw p).restrict (fixedControlSourceStratum p q) :=
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_privateStratum_map_symm p q t
  have hint (h : SourceInput p → ℝ) (hh : Measurable h) :
      (∫ z in fixedControlSourceStratum p q, h z ∂sourceInputLaw p) =
        ∫ x, h (e.symm x) ∂(timeControlLaw p).prod η := by
    rw [← hmap]
    exact integral_map_of_stronglyMeasurable e.symm.measurable hh.stronglyMeasurable
  have hfe : Integrable (fun x => f (e.symm x)) ((timeControlLaw p).prod η) :=
    bounded_integrable _ _ (hf.comp e.symm.measurable) (fun x => hb (e.symm x))
  have hge : Integrable (fun x => g (e.symm x)) ((timeControlLaw p).prod η) :=
    bounded_integrable _ _ (hg.comp e.symm.measurable) (fun x => hgb (e.symm x))
  have hrepl (r : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t)
      (hr : r ∈ fixedControlRemainderStratum p q t) (c d : TimeControl p) :
      replaceSourceControl p t (e.symm (c, r)) d = e.symm (d, r) := by
    have hq : sourceCoordinatorIndex p (e.symm (c, r)) = q := by
      change PrivateSourceStreams.coordinatorIndex p (e.symm (c, r)).2.1.2 = q
      rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_private]
      exact hr
    have he := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
      p q t (e.symm (c, r)) d hq
    change e.symm (d, (e (e.symm (c, r))).2) = _ at he
    rw [e.apply_symm_apply] at he
    exact he.symm
  rw [hint f hf, hint g hg, integral_prod_symm _ hfe, integral_prod_symm _ hge]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem
    (ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlRemainderStratum
      p q t)] with r hr
  have heq : (fun c : TimeControl p => g (e.symm (c, r))) =
      fun _ => ∫ d, f (e.symm (d, r)) ∂timeControlLaw p := by
    funext c
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun d => congrArg f (hrepl r hr c d)
  rw [heq]
  simp only [integral_const, probReal_univ, one_smul]

private theorem split_assignmentVector (vw : AssignmentVector p ×
    ReferenceLaterOptionalControlResampling.ControlRemainder p) :
    ContinuousControlSlice.assignmentVector ((controlAssignmentSplitEquiv p).symm vw).1 =
      vw.1 := by
  have hfirst (c : TimeControl p) :
      (controlAssignmentSplitEquiv p c).1 =
        ContinuousControlSlice.assignmentVector c.1 := by
    funext r
    rfl
  rw [← hfirst, (controlAssignmentSplitEquiv p).apply_symm_apply]

private theorem joint_fibre_graph_integral (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) (theta : AssignmentParameterFibreKernel.Theta p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    (∫ vw, B.indicator (fun _ => (1 : ℝ))
      (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw),
        some (u, (t, (sourcePrefix control0 t.val z,
          (some (successfulSlowSet p theta vw.1), vw.1)))))
      ∂(ContinuousControlSlice.assignmentLaw p.K).prod (controlRemainderLaw p)) =
      ∑ a : Outcome p, (fibreMass p theta a).toReal *
        ∫ vw, B.indicator (fun _ => (1 : ℝ))
          (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw),
            some (u, (t, (sourcePrefix control0 t.val z, (some a, vw.1)))))
          ∂(fibreMeasure p theta a).prod (controlRemainderLaw p) := by
  let F := successfulSlowSet p theta
  let ν := (ContinuousControlSlice.assignmentLaw p.K).prod (controlRemainderLaw p)
  let g := fun vw : AssignmentVector p ×
      ReferenceLaterOptionalControlResampling.ControlRemainder p =>
    B.indicator (fun _ => (1 : ℝ))
      (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw),
        some (u, (t, (sourcePrefix control0 t.val z, (some (F vw.1), vw.1)))))
  have hF : Measurable F :=
    (AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
      measurable_prodMk_left
  have hobs : Measurable (fun vw : AssignmentVector p ×
      ReferenceLaterOptionalControlResampling.ControlRemainder p =>
      (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw),
        (some (u, (t, (sourcePrefix control0 t.val z, (some (F vw.1), vw.1)))) :
          ReferenceFirstCollectionPastSamplerFibreLaw.PastFibreY p))) := by
    have hs : Measurable (fun vw : AssignmentVector p ×
        ReferenceLaterOptionalControlResampling.ControlRemainder p =>
        replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw)) :=
      (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
        (measurable_const.prodMk (controlAssignmentSplitEquiv p).symm.measurable)
    exact hs.prodMk
      (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
        (measurable_const.prodMk (measurable_const.prodMk
          (measurable_const.prodMk
            ((LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
              (hF.comp measurable_fst)).prodMk measurable_fst)))))
  have hg : Integrable g ν := integrable_test ν _ hobs B hB
  have hrect (a : Outcome p) :
      FiniteFibreLift.fibre (fun vw : AssignmentVector p ×
          ReferenceLaterOptionalControlResampling.ControlRemainder p => F vw.1) a =
        FiniteFibreLift.fibre F a ×ˢ Set.univ := by
    ext vw
    simp only [FiniteFibreLift.fibre, Set.mem_prod, Set.mem_univ, and_true]
    rfl
  have hrestrict (a : Outcome p) :
      ν.restrict (FiniteFibreLift.fibre (fun vw => F vw.1) a) =
        (fibreMass p theta a • fibreMeasure p theta a).prod (controlRemainderLaw p) := by
    rw [AssignmentParameterFibreKernel.fibreMass_smul_fibreMeasure, hrect]
    exact (Measure.prod_restrict _ Set.univ).symm.trans (by rw [Measure.restrict_univ])
  have hp : (∑ a : Outcome p,
      ν.restrict (FiniteFibreLift.fibre (fun vw => F vw.1) a)) = ν := by
    simp_rw [hrestrict]
    rw [← Measure.sum_fintype, ← Measure.prod_sum_left, Measure.sum_fintype,
      AssignmentParameterFibreKernel.sum_fibreMass_smul_fibreMeasure]
  calc
    _ = ∫ vw, g vw ∂∑ a : Outcome p,
        ν.restrict (FiniteFibreLift.fibre (fun vw => F vw.1) a) := by rw [hp]
    _ = ∑ a : Outcome p, ∫ vw in FiniteFibreLift.fibre (fun vw => F vw.1) a,
        g vw ∂ν := integral_finsetSum_measure (fun _ _ => hg.integrableOn)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      have heq : (∫ vw in FiniteFibreLift.fibre (fun vw => F vw.1) a, g vw ∂ν) =
          ∫ vw in FiniteFibreLift.fibre (fun vw => F vw.1) a,
            B.indicator (fun _ => (1 : ℝ))
              (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw),
                some (u, (t, (sourcePrefix control0 t.val z, (some a, vw.1))))) ∂ν := by
        apply setIntegral_congr_fun
          (FiniteFibreLift.measurableSet_fibre _ a (hF.comp measurable_fst))
        intro vw hv
        change F vw.1 = a at hv
        simp only [g, hv]
      rw [heq, hrestrict, Measure.prod_smul_left, integral_smul_measure, smul_eq_mul]

/-- On an actual rank cell, whole-control resampling gives the existing
original-source fibre section, with all optional outcomes and zero fibres. -/
theorem resampledTest_eq_fibreSum_on_cell (k : ℕ) (control0 : TimeControl p)
    (u s : Fin p.T) (B : Set (JointY p)) (hB : MeasurableSet B) (z : SourceInput p)
    (hz : z ∈ rankCell rate rewards C_star C_h k u s) :
    (∫ c, rankOriginalSourceTest rate rewards C_star C_h k control0 B
      (replaceSourceControl p s z c) ∂timeControlLaw p) =
      ∑ a : Outcome p, originalSourceSection rate rewards C_star C_h control0 u s a B z := by
  obtain ⟨theta, _n, _r, _o, _hn, _hr, _ha, _ht, _hc, htheta, _ho, _hp, _hv,
      _hcode, _houtcome⟩ := rankCell_actualSamplerTrace rate rewards C_star C_h k u s z hz
  have hcell (c : TimeControl p) :
      replaceSourceControl p s z c ∈ rankCell rate rewards C_star C_h k u s :=
    (rankCell_replaceSourceControl_iff rate rewards C_star C_h control0 k u s z c).mpr hz
  have hactive (c : TimeControl p) :
      ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt rate rewards C_star C_h s
        (replaceSourceControl p s z c) =
      some (successfulSlowSet p theta (ContinuousControlSlice.assignmentVector c.1)) := by
    obtain ⟨theta', _n', _r', _o', _hn', _hr', _ha', _ht', _hc', htheta', _ho',
        _hp', _hv', _hcode', ha'⟩ := rankCell_actualSamplerTrace rate rewards C_star C_h
          k u s (replaceSourceControl p s z c) (hcell c)
    have heq : theta' = theta := Option.some.inj
      (htheta'.symm.trans
        ((calendarParameters_replaceSourceControl rate rewards C_star C_h
          control0 s z c).trans htheta))
    rw [heq, vector_replacement] at ha'
    exact ha'
  have htest (c : TimeControl p) :
      rankOriginalSourceTest rate rewards C_star C_h k control0 B (replaceSourceControl p s z c) =
        B.indicator (fun _ => (1 : ℝ))
          (replaceSourceControl p s z c,
            some (u, (s, (sourcePrefix control0 s.val z,
              (some (successfulSlowSet p theta
                (ContinuousControlSlice.assignmentVector c.1)),
                ContinuousControlSlice.assignmentVector c.1))))) := by
    unfold rankOriginalSourceTest rankOriginalSourceOutput
    rw [rankPastFibreOutput_on_cell rate rewards C_star C_h k control0 u s _ (hcell c)]
    simp only [ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair,
      sourcePrefix_replaceSourceControl, hactive, vector_replacement]
  have hsplit : ((ContinuousControlSlice.assignmentLaw p.K).prod (controlRemainderLaw p)).map
      (controlAssignmentSplitEquiv p).symm = timeControlLaw p :=
    (LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p).symm.map_eq
  have hg : StronglyMeasurable (fun c : TimeControl p =>
      rankOriginalSourceTest rate rewards C_star C_h k control0 B
        (replaceSourceControl p s z c)) :=
    ((rankOriginalSourceTest_measurable rate rewards C_star C_h k control0 B hB).comp
      ((ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p s).comp
        measurable_prodMk_left)).stronglyMeasurable
  calc
    _ = ∫ vw, rankOriginalSourceTest rate rewards C_star C_h k control0 B
        (replaceSourceControl p s z ((controlAssignmentSplitEquiv p).symm vw))
        ∂(ContinuousControlSlice.assignmentLaw p.K).prod (controlRemainderLaw p) := by
      conv_lhs => rw [← hsplit]
      exact integral_map_of_stronglyMeasurable (controlAssignmentSplitEquiv p).symm.measurable hg
    _ = ∫ vw, B.indicator (fun _ => (1 : ℝ))
        (replaceSourceControl p s z ((controlAssignmentSplitEquiv p).symm vw),
          some (u, (s, (sourcePrefix control0 s.val z,
            (some (successfulSlowSet p theta vw.1), vw.1)))))
        ∂(ContinuousControlSlice.assignmentLaw p.K).prod (controlRemainderLaw p) := by
      apply integral_congr_ae
      filter_upwards [] with vw
      rw [htest, split_assignmentVector]
    _ = _ := by
      rw [joint_fibre_graph_integral control0 u s z theta B hB]
      apply Finset.sum_congr rfl
      intro a _
      simp only [originalSourceSection, htheta]

/-- The same single-cell identity, testing the original source jointly with
its actual marked ranked-call output. Every optional outcome is summed. -/
theorem rankOriginalSource_cell_integral (k : ℕ) (control0 : TimeControl p) (u t : Fin p.T)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    (∫ z in rankCell rate rewards C_star C_h k u t,
      rankOriginalSourceTest rate rewards C_star C_h k control0 B z ∂sourceInputLaw p) =
      ∑ a : Outcome p, ∫ z in rankCell rate rewards C_star C_h k u t,
        originalSourceSection rate rewards C_star C_h control0 u t a B z
          ∂sourceInputLaw p := by
  let E := rankCell rate rewards C_star C_h k u t
  let f := E.indicator (rankOriginalSourceTest rate rewards C_star C_h k control0 B)
  have hE : MeasurableSet E := rankCell_borel rate rewards C_star C_h control0 k u t
  have hf : Measurable f :=
    (rankOriginalSourceTest_measurable rate rewards C_star C_h k control0 B hB).indicator hE
  have hb : ∀ z, ‖f z‖ ≤ 1 := by
    intro z
    by_cases hz : z ∈ E
    · simp only [f, Set.indicator_of_mem hz]
      obtain ⟨h0, h1⟩ := indicator_bounds B
        (rankOriginalSourceOutput rate rewards C_star C_h k control0 z)
      exact (Real.norm_of_nonneg h0).le.trans h1
    · simp only [f, Set.indicator_of_notMem hz, norm_zero, zero_le_one]
  have hpoint (z : SourceInput p) :
      (∫ c, f (replaceSourceControl p t z c) ∂timeControlLaw p) =
        E.indicator (fun y => ∑ a : Outcome p,
          originalSourceSection rate rewards C_star C_h control0 u t a B y) z := by
    by_cases hz : z ∈ E
    · have hc (c : TimeControl p) : replaceSourceControl p t z c ∈ E :=
        (rankCell_replaceSourceControl_iff rate rewards C_star C_h control0 k u t z c).mpr hz
      simp only [f, Set.indicator_of_mem (hc _), Set.indicator_of_mem hz]
      exact resampledTest_eq_fibreSum_on_cell
        rate rewards C_star C_h k control0 u t B hB z hz
    · have hc (c : TimeControl p) : replaceSourceControl p t z c ∉ E :=
        fun h => hz ((rankCell_replaceSourceControl_iff
          rate rewards C_star C_h control0 k u t z c).mp h)
      simp only [f, Set.indicator_of_notMem (hc _), Set.indicator_of_notMem hz, integral_zero]
  calc
    _ = ∫ z, f z ∂sourceInputLaw p := (integral_indicator hE).symm
    _ = ∫ z, ∫ c, f (replaceSourceControl p t z c) ∂timeControlLaw p
        ∂sourceInputLaw p := resampling_integral t f hf hb
    _ = ∫ z, E.indicator (fun y => ∑ a : Outcome p,
        originalSourceSection rate rewards C_star C_h control0 u t a B y) z
        ∂sourceInputLaw p := integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ z in E, (∑ a : Outcome p,
        originalSourceSection rate rewards C_star C_h control0 u t a B z)
        ∂sourceInputLaw p := integral_indicator hE
    _ = _ := integral_finsetSum Finset.univ fun a _ =>
      (ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection_integrable
        rate rewards C_star C_h control0 u t a B hB).integrableOn

private theorem rankOriginalSource_indicator_partition (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (z : SourceInput p) :
    rankOriginalSourceTest rate rewards C_star C_h k control0 B z =
      (rankNoCall
        rate rewards C_star C_h k).indicator
          (fun y => B.indicator (fun _ => (1 : ℝ)) (y, none)) z +
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        (rankCell rate rewards C_star C_h k u t).indicator
          (rankOriginalSourceTest rate rewards C_star C_h k control0 B) z := by
  cases hcall : ReferenceCollectionSamplerChronology.nthCollectionCall
      rate rewards C_star C_h k z with
  | none =>
      have hnone : z ∈ rankNoCall
          rate rewards C_star C_h k := hcall
      have hcell (u t : Fin p.T) : z ∉ rankCell rate rewards C_star C_h k u t := by
        intro hz
        have htag := (mem_rankCell_iff_originalTags
          rate rewards C_star C_h k u t z).mp hz
        simp only [hcall, Option.map_none, reduceCtorEq] at htag
      simp only [Set.indicator_of_mem hnone, Set.indicator_of_notMem (hcell _ _),
        Finset.sum_const_zero, add_zero, rankOriginalSourceTest, rankOriginalSourceOutput,
        rankPastFibreOutput, hcall, Option.map_none]
  | some c =>
      have hnone : z ∉ rankNoCall
          rate rewards C_star C_h k := by
        intro hz
        change ReferenceCollectionSamplerChronology.nthCollectionCall
          rate rewards C_star C_h k z = none at hz
        rw [hcall] at hz
        cases hz
      have hcell (u t : Fin p.T) : z ∈ rankCell rate rewards C_star C_h k u t ↔
          c.1 = u ∧ c.2.1 = t := by
        rw [mem_rankCell_iff_originalTags, hcall]
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      simp only [Set.indicator_of_notMem hnone, zero_add]
      simp only [Set.indicator, hcell, ite_and]
      simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, Finset.sum_const_zero]

/-- The source-dependent no-call test is integrable before restriction. -/
theorem rankOriginalSource_noCallTest_integrable (B : Set (JointY p)) (hB : MeasurableSet B) :
    Integrable (fun z : SourceInput p => B.indicator (fun _ => (1 : ℝ)) (z, none))
      (sourceInputLaw p) :=
  integrable_test _ _ (measurable_id.prodMk measurable_const) B hB

/-- Arbitrary Borel tests of the original source and existing marked ranked-call
observation. Absence is the actual restricted integral, and all fibres remain. -/
theorem rankOriginalSourceOutput_borel_test_law (k : ℕ) (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    (∫ z, B.indicator (fun _ => (1 : ℝ))
      (rankOriginalSourceOutput rate rewards C_star C_h k control0 z) ∂sourceInputLaw p) =
      (∫ z in rankNoCall
          rate rewards C_star C_h k,
        B.indicator (fun _ => (1 : ℝ)) (z, none) ∂sourceInputLaw p) +
      ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
        ∫ z in rankCell rate rewards C_star C_h k u t,
          originalSourceSection rate rewards C_star C_h control0 u t a B z
            ∂sourceInputLaw p := by
  let noneTerm : SourceInput p → ℝ :=
    (rankNoCall
      rate rewards C_star C_h k).indicator
        (fun z => B.indicator (fun _ => (1 : ℝ)) (z, none))
  let cellTerm (u t : Fin p.T) : SourceInput p → ℝ :=
    (rankCell rate rewards C_star C_h k u t).indicator
      (rankOriginalSourceTest rate rewards C_star C_h k control0 B)
  have hnoneMeas := rankNoCall_measurable
    rate rewards C_star C_h control0 k
  have hnoneInt : Integrable noneTerm (sourceInputLaw p) :=
    (rankOriginalSource_noCallTest_integrable B hB).indicator hnoneMeas
  have hcellInt (u t : Fin p.T) : Integrable (cellTerm u t) (sourceInputLaw p) :=
    (rankOriginalSourceTest_integrable rate rewards C_star C_h k control0 B hB).indicator
      (rankCell_borel rate rewards C_star C_h control0 k u t)
  have hsumInt : Integrable (fun z =>
      ∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z) (sourceInputLaw p) := by
    apply integrable_finsetSum
    intro u _
    apply integrable_finsetSum
    intro t _
    exact hcellInt u t
  calc
    _ = ∫ z, noneTerm z + (∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z)
        ∂sourceInputLaw p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (rankOriginalSource_indicator_partition rate rewards C_star C_h k control0 B)
    _ = (∫ z, noneTerm z ∂sourceInputLaw p) +
        ∫ z, (∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z) ∂sourceInputLaw p :=
      integral_add' hnoneInt hsumInt
    _ = (∫ z in rankNoCall
          rate rewards C_star C_h k,
        B.indicator (fun _ => (1 : ℝ)) (z, none) ∂sourceInputLaw p) +
        ∑ u : Fin p.T, ∑ t : Fin p.T, ∫ z, cellTerm u t z ∂sourceInputLaw p := by
      rw [show (∫ z, noneTerm z ∂sourceInputLaw p) = _ from integral_indicator hnoneMeas]
      congr 1
      rw [integral_finsetSum Finset.univ (fun u _ =>
        integrable_finsetSum Finset.univ (fun t _ => hcellInt u t))]
      apply Finset.sum_congr rfl
      intro u _
      exact integral_finsetSum Finset.univ (fun t _ => hcellInt u t)
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro t _
      change (∫ z, (rankCell rate rewards C_star C_h k u t).indicator
        (rankOriginalSourceTest rate rewards C_star C_h k control0 B) z ∂sourceInputLaw p) = _
      rw [integral_indicator (rankCell_borel rate rewards C_star C_h control0 k u t)]
      exact rankOriginalSource_cell_integral rate rewards C_star C_h k control0 u t B hB

end Bandits.Support.ReferenceCollectionRankCellPhysicalTransport

end
