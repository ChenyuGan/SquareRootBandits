/-
Copyright (c) 2026 Bandits formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodeTransitionCore
public import Bandits.Support.ReferenceGeneratedCalendarPrefixProposalErasure

/-!
# Erased first-collection transition branch

Sources: ZIP4 `04_slow_fast_learner.tex:329-390` and
`06_interruptions.tex:391-426`.

The original before-first experiment is transported through current proposal
erasure and its strict LAUNCH seed/PRE support is proved. On the actual
first-COLLECTION branch, the retained source and common-kernel tests agree on
the original erased prefix experiment, raw and under every original fixed-ID
law. The whole before-first terminal transition identity remains open.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation (LogicalCell SlowSet)
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceGeneratedCalendarEpisodeHistoryTransport
open ReferenceGeneratedCalendarEpisodeTransitionCore
open ReferenceGeneratedCalendarPrefixProposalErasure
open ReferenceGeneratedCalendarEpisodePrefixRecombination
open ReferenceFirstCollectionLogicalPrefixExtension
  (betaPre noCallAt measurableSet_noCallAt)
open ReferenceFirstLiveCalendarMarkedTransition (calendarInnovationLaw)
open ContinuousControlSlice (Scalar scalarLaw)

namespace Bandits.Support.ReferenceGeneratedCalendarErasedCollectionTransition

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace : MeasurableSpace (Source p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Obs" => ReferenceFirstLiveCalendarMarkedTransition.Observation p rate
local notation "Innovation" => ContinuousLearningRows.TimeControl p × Scalar
local notation "Lambda" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw
  rate rewards C_star C_h control0
omit rewards C_star C_h in
/-- Erasing the proposal retains the entire pre-round source history. -/
theorem prefixSourceHistory_eraseProposal (s q : Fin p.T) (o : Obs) :
    prefixSourceHistory rate control0 s q (eraseProposal q o) =
      prefixSourceHistory rate control0 s q o := rfl

omit rewards C_star C_h in
/-- Refilling that coordinate also leaves the complete history unchanged. -/
theorem prefixSourceHistory_refillProposal (s q : Fin p.T) (v : Obs × Scalar) :
    prefixSourceHistory rate control0 s q (refillProposal q v) =
      prefixSourceHistory rate control0 s q v.1 := rfl

omit rewards C_star C_h control0 in
/-- The incoming set is read from the same complete past after erasure. -/
theorem incomingFromList_eraseProposal (q : Fin p.T) (o : Obs) :
    ReferenceFirstCollectionLogicalPrefixExtension.incomingFromList rate
        (eraseProposal q o).2.2 =
      ReferenceFirstCollectionLogicalPrefixExtension.incomingFromList rate o.2.2 := rfl

/-- The original innovation and the exposed current proposal are jointly
available for every nonnegative Borel test, including tests retaining the full
erased observer. No calendar component is normalized. -/
theorem betaPre_refillProposal_innovation_test
    (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T)
    (G : Obs × Innovation → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ v, G v ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).prod
        (calendarInnovationLaw p)) =
      ∫⁻ v, ∫⁻ ux, G (refillProposal q v, ux) ∂calendarInnovationLaw p
        ∂((ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
          (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
            (eraseProposal q)).prod scalarLaw := by
  have hm : Measurable (fun v : (Obs × Scalar) × Innovation =>
      G (refillProposal q v.1, v.2)) :=
    hG.comp (((measurable_refillProposal q).comp measurable_fst).prodMk measurable_snd)
  have hPhi : Measurable (fun v : Obs × Scalar =>
      ∫⁻ ux, G (refillProposal q v, ux) ∂calendarInnovationLaw p) :=
    hm.lintegral_prod_right'
  rw [lintegral_prod _ hG.aemeasurable]
  have h := betaPre_currentProposal_erasure_test rate rewards C_star C_h control0 ids q
    (fun v => ∫⁻ ux, G (refillProposal q v, ux) ∂calendarInnovationLaw p) hPhi
  simpa only [refillProposal_erase_current] using h

/-- Transport the actual before-first retained source test all the way to
the original proposal/control/residual experiment. The `q.succ` event includes
the current no-call condition; a ROOT at `q` is therefore excluded. -/
theorem terminal_beforeFirstCall_source_erasure_test
    (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, if w ∈ beforeFirstCall rate rewards C_star C_h q.succ then
        retainedSourceTest rate rewards C_star C_h s q F
          (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0
      ∂ids.elim Lambda
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
          rate rewards C_star C_h control0)) =
      ∫⁻ v, ∫⁻ ux, if noCallAt rate rewards C_star C_h q v.1.1 then
        retainedSourceTest rate rewards C_star C_h s q F
          (prefixSourceJoint rate rewards C_star C_h control0 s q
            (refillProposal q v, ux)) else 0 ∂calendarInnovationLaw p
        ∂((ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
          (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
            (eraseProposal q)).prod scalarLaw := by
  let G : Obs × Innovation → ℝ≥0∞ := fun v =>
    if noCallAt rate rewards C_star C_h q v.1.1 then
      retainedSourceTest rate rewards C_star C_h s q F
        (prefixSourceJoint rate rewards C_star C_h control0 s q v) else 0
  have hG : Measurable G :=
    ((measurable_retainedSourceTest rate rewards C_star C_h control0 s q F hF).comp
      (measurable_prefixSourceJoint rate rewards C_star C_h control0 s q)).ite
        ((measurableSet_noCallAt rate rewards C_star C_h control0 q).preimage
          measurable_fst.fst) measurable_const
  exact (terminalLaw_beforeFirstCall_transition_test rate rewards C_star C_h control0
    ids s q hsq F hF).trans
      (betaPre_refillProposal_innovation_test rate rewards C_star C_h control0 ids q G hG)

/-- The same erasure transport for the literal common-kernel test, keeping
the same actual old set and the same start, retention and no-call gates. -/
theorem terminal_beforeFirstCall_kernel_erasure_test
    (ids : Option (CompletePublicTable.IDArray p))
    (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, if w ∈ beforeFirstCall rate rewards C_star C_h q.succ then
        retainedKernelTest rate rewards C_star C_h s q F
          (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0
      ∂ids.elim Lambda
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
          rate rewards C_star C_h control0)) =
      ∫⁻ v, ∫⁻ ux, if noCallAt rate rewards C_star C_h q v.1.1 then
        retainedKernelTest rate rewards C_star C_h s q F
          (prefixSourceJoint rate rewards C_star C_h control0 s q
            (refillProposal q v, ux)) else 0 ∂calendarInnovationLaw p
        ∂((ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
          (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
            (eraseProposal q)).prod scalarLaw :=
  terminal_beforeFirstCall_source_erasure_test rate rewards C_star C_h control0 ids s q hsq
    (kernelLiftTest rate rewards C_star C_h s q F)
    (measurable_kernelLiftTest rate rewards C_star C_h s q F hF)
section SourceGeometry

open ReferenceGeneratedCalendarEpisodeSlowLaw
open ReferenceOriginalCalendarEpisodeChronology
open ReferenceFirstCollectionOneRoundLogicalCell

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- Before the first invocation, an original episode opportunity can only be
LAUNCH. Its strict numerical seed is produced as the complete zero state,
including empty accepted-record arrays; no seed or anchor equality is assumed. -/
theorem sourceStartEvent_beforeFirstCall_seed (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hno : ReferenceFirstCollectionLogicalPrefixExtension.NoCallBefore
      rate rewards C_star C_h q.succ z)
    (hs : z ∈ sourceStartEvent rate rewards C_star C_h s) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s.val ∧
      ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z) =
          some (RecordedQueueRun.initialState p.K) := by
  have hcall : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h s z = none :=
    (ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none
      rate rewards C_star C_h s z).mp (hno s (by change s.val < q.val + 1; omega))
  have hlaunch : z ∈ ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h s.val := by
    rcases hs.1 with hl | ⟨hc, _⟩
    · exact hl
    · rw [hcall] at hc
      cases hc
  refine ⟨hlaunch.2, ?_⟩
  obtain ⟨rho, _, _⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s z hs
  have hl := complete_record_launch rate rewards C_star C_h z rho
  rw [← ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix
      rate rewards C_star C_h control0 s.castSucc s.val le_rfl z,
    ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord
      rate rewards C_star C_h s.castSucc z hl hlaunch.2.le]
  simp only [Fin.val_castSucc, hlaunch.2, Nat.sub_self, List.take_zero]
  rfl
/-- The same strict LAUNCH seed in the actual terminal history. Future source
insertions are removed only using the proved original-prefix agreement, on
the actual `q.succ` no-call event. This is pointwise on every component. -/
theorem terminal_beforeFirstCall_seed (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h)
    (hw : w ∈ beforeFirstCall rate rewards C_star C_h q.succ)
    (hs : w ∈ episodeStartEvent rate rewards C_star C_h control0 s) :
    ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
      (sourceEstimateHistory rate rewards C_star C_h control0 s q w).1.1 =
        some (RecordedQueueRun.initialState p.K) := by
  have hpre : w ∈ beforeFirstCall rate rewards C_star C_h s.castSucc :=
    fun t ht => hw t (by change t.val < q.val + 1; change t.val < s.val at ht; omega)
  have hp := sourcePrefix_terminal_original rate rewards C_star C_h control0 s.castSucc w hpre
  simp only [Fin.val_castSucc] at hp
  have hs0 : ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource
      rate rewards C_star C_h w ∈ sourceStartEvent rate rewards C_star C_h s := by
    rw [sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s, ← hp]
    exact (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s _).mp hs
  have hseed := (sourceStartEvent_beforeFirstCall_seed rate rewards C_star C_h control0 s q hsq
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource rate rewards C_star C_h w) hw hs0).2
  change ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0 w)) = _
  rw [hp]
  exact hseed
/-- The native first-COLLECTION PRE is the same full original strict prefix,
including the overflow flag and every arm's accepted records. -/
theorem firstCollection_native_pre (q : Fin p.T)
    (z : ActualSource (rate := rate) rewards C_star C_h q) :
    ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc z.val =
      some (RecordedQueueRun.run Q
        (actualPast rewards C_star C_h z.val q (domainRecord rewards C_star C_h q z)
          (domainRecord_spec rewards C_star C_h q z) (domainRecord_mem rewards C_star C_h q z))) := by
  rw [ReferencePostInvocationNoncallGeometry.prefixNumerical, Fin.val_castSucc,
    ReferenceFirstCollectionCorrectedFutureRetainedMoment.prefixInputs_eq_pastCells,
    actualPast_spec, Option.map_some]

/-- The original first-COLLECTION descriptor has exactly the anchor of the
strict seed above. Both its descriptor and seed are derived from the actual
source, rather than supplied as a numerical match. -/
theorem firstCollection_native_anchor (s q : Fin p.T) (hsq : s.val ≤ q.val)
    (z : ActualSource (rate := rate) rewards C_star C_h q)
    (hno : ReferenceFirstCollectionLogicalPrefixExtension.NoCallBefore
      rate rewards C_star C_h q.succ z.val)
    (hs : z.val ∈ sourceStartEvent rate rewards C_star C_h s) :
    ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h s.castSucc
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z.val) =
          some (RecordedQueueRun.initialState p.K) ∧
      ∃ call : ReferenceCollectionSegmentExtraction.Choice rate,
        ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0
          (domainRecord rewards C_star C_h q z) =
            some ⟨call.payload, call.preLedger, call.started, call.weights⟩ ∧
        call.payload.anchor = RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K) := by
  refine ⟨(sourceStartEvent_beforeFirstCall_seed rate rewards C_star C_h control0 s q hsq z.val hno hs).2, ?_⟩
  obtain ⟨call, _, _, hcall, hanchor, _⟩ :=
    actual_data rewards C_star C_h z.val q (domainRecord rewards C_star C_h q z)
      (domainRecord_spec rewards C_star C_h q z) (domainRecord_mem rewards C_star C_h q z)
  refine ⟨call, hcall, hanchor.trans ?_⟩
  funext i
  simp only [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState, ScoreWeights.scoreWeight, pow_zero]

private theorem roundInput_eq_of_fields {c d : RecordedQueueRun.RoundInput p.K}
    (he : c.enabled = d.enabled) (hi : c.recordedArm = d.recordedArm)
    (hr : c.reward = d.reward) (hx : c.rate = d.rate) : c = d := by
  cases c
  cases d
  cases he
  cases hi
  cases hr
  cases hx
  rfl

section CollectionAuxiliary

variable (q : Fin p.T) (z : ActualSource (rate := rate) rewards C_star C_h q)

local notation "r" => domainRecord rewards C_star C_h q z
local notation "hr" => domainRecord_spec rewards C_star C_h q z
local notation "hm" => domainRecord_mem rewards C_star C_h q z
local notation "c" => actualInput rewards C_star C_h z.val q r hr hm
local notation "S" => RecordedQueueRun.run Q (actualPast rewards C_star C_h z.val q r hr hm)

/-- Enabled first-COLLECTION inputs have exactly the same original reward
row and frozen unit-anchor rates as the produced LAUNCH seed. The actual
recorder is kept, including `none` and markers with zero reward. -/
theorem firstCollection_native_input (hen : (c).enabled = true) :
    c = episodeRoundInput rate rewards q (RecordedQueueRun.initialState p.K) (c).recordedArm := by
  obtain ⟨call, _, _, _, ha, hrate, hcanonical, _⟩ :=
    actual_data rewards C_star C_h z.val q r hr hm
  have hweight : RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K) =
      (fun _ => 1) := by
    funext i
    simp only [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState,
      ScoreWeights.scoreWeight, pow_zero]
  apply roundInput_eq_of_fields
  · exact hen
  · rfl
  · have hreward := cell0_reward rate r c (actualInput_spec rewards C_star C_h z.val q r hr hm)
    have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h q z.val r hr
    rw [hf.2.2.1, hf.2.2.2] at hreward
    exact hreward
  · change (c).rate = CanonicalRecordingRates.xi p rate.eta.val
      (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K))
    rw [hweight]
    exact hrate.trans (hcanonical.trans (congrArg (CanonicalRecordingRates.xi p rate.eta.val) ha))

/-- The existing general collection source, at the identical original
first-COLLECTION physical source. Only the membership proof is supplied. -/
def firstCollectionSource : ReferencePostInvocationNoncallGeometry.CollectionDateSource
    rate rewards C_star C_h q := by
  refine ⟨z.val, ?_⟩
  obtain ⟨_, _, hread, _⟩ := actual_data rewards C_star C_h z.val q r hr hm
  exact ReferencePostInvocationNoncallGeometry.collectionDateDomain_of_readout
    rate rewards C_star C_h q z.val r hr c hread

theorem firstCollectionSource_val :
    (firstCollectionSource rate rewards C_star C_h q z).val = z.val := rfl

/-- The accepted general collection operation has the native first-collection
input, complete PRE and actual LAUNCH anchor at this identical source. -/
theorem firstCollectionSource_fields :
    ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q
        (firstCollectionSource rate rewards C_star C_h q z) = c ∧
      ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q
        (firstCollectionSource rate rewards C_star C_h q z) = S ∧
      (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q
        (firstCollectionSource rate rewards C_star C_h q z)).1.anchor =
          RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K) := by
  let zc := firstCollectionSource rate rewards C_star C_h q z
  have hrec := ReferencePostInvocationNoncallGeometry.collectionRecord_spec rate rewards C_star C_h q zc
  have hrr : ReferencePostInvocationNoncallGeometry.collectionRecord rate rewards C_star C_h q zc = r :=
    Option.some.inj (hrec.1.symm.trans hr)
  have hi : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
      (ReferencePostInvocationNoncallGeometry.collectionRecord rate rewards C_star C_h q zc) =
        some (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q zc) :=
    (Option.some_get _).symm
  rw [hrr] at hi
  refine ⟨Option.some.inj (hi.symm.trans (actualInput_spec rewards C_star C_h z.val q r hr hm)), ?_, ?_⟩
  · have hstart := (ReferencePostInvocationNoncallGeometry.collectionInput_word
      rate rewards C_star C_h q zc).choose_spec.1
    have hnum := ReferencePostInvocationNoncallGeometry.prefixNumerical_actualWord
      rate rewards C_star C_h q.castSucc z.val
      (ReferencePostInvocationNoncallGeometry.collection_launch rate rewards C_star C_h q zc) hstart
    change ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc z.val =
      some (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q zc) at hnum
    exact Option.some.inj (hnum.symm.trans (firstCollection_native_pre rate rewards C_star C_h q z))
  · obtain ⟨call, _, _, hcall, ha, _⟩ := actual_data rewards C_star C_h z.val q r hr hm
    have hargs := ReferencePostInvocationNoncallGeometry.collectionArguments_spec rate rewards C_star C_h q zc
    rw [hrr] at hargs
    have he := congrArg (fun a => a.1.anchor) (Option.some.inj (hargs.symm.trans hcall))
    refine he.trans (ha.trans ?_)
    funext i
    simp only [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState,
      ScoreWeights.scoreWeight, pow_zero]

/-- The genuine first-COLLECTION operation and the accepted general native
operation give the identical estimate/old-set/proposal/next-set test at the
same source and auxiliary array. This projection makes no assertion about
independence of FAST and recorder, and includes disabled and overflow cases. -/
theorem firstCollection_optionalTransitionTest_eq_native (s : Fin p.T)
    (F : TransitionData rate s q → ℝ≥0∞) (h : History rate s q)
    (U : SlowSet p) (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    let e := collectionLogicalCellAt rewards C_star C_h z.val q r hr hm U
      (ReferenceFirstLiveCalendarMarkedTransition.labelZero a) (a (q, 1))
    let d := ReferencePostInvocationNoncallGeometry.laterCollectionCell? rate rewards C_star C_h q
      (firstCollectionSource rate rewards C_star C_h q z) U a
    optionalTransitionTest rate s q F (h, (sourceOptionalEstimate rate e, e)) =
      optionalTransitionTest rate s q F (h, (sourceOptionalEstimate rate d, d)) := by
  dsimp only
  obtain ⟨hi, hS, ha⟩ := firstCollectionSource_fields rate rewards C_star C_h q z
  have hweight : RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K) =
      (fun _ => 1) := by
    funext i
    simp only [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState,
      ScoreWeights.scoreWeight, pow_zero]
  have hanchor := ha.trans hweight
  simp only [collectionLogicalCellAt, cellWithScalar?,
    ReferencePostInvocationNoncallGeometry.laterCollectionCell?, hi]
  cases hen : (c).enabled with
  | false => simp only [Bool.false_eq_true, ite_false, optionalTransitionTest]
  | true =>
    simp only [ite_true, optionalTransitionTest, sourceOptionalEstimate_some,
      sourceCellEstimate, cellWithScalar, cellWithNext, nextSet,
      ReferencePostInvocationNoncallGeometry.laterCollectionCell, hi, hS, hanchor,
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates,
      ReferenceFirstLiveCalendarMarkedTransition.labelZero]
    rfl

/-- A whole original-control, proposal and residual evaluation on the actual
first-COLLECTION source, using the admitted native collection law. The real
first-collection input, full PRE and unit anchor have been identified above.
No incoming-set distribution, integrability or boundedness is an input. -/
theorem firstCollection_source_quantized_test (U : SlowSet p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (hen : (c).enabled = true) (hpre : (S).overflow = false)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) :
    (∫⁻ y, ReferenceGeneratedCalendarQuantizedRoundKernel.outcomeTest rate S
      (ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q
        (firstCollectionSource rate rewards C_star C_h q z)) f 0
      (ReferencePostInvocationCollectionNativeLaw.sourceOutcome rate rewards C_star C_h control0 q
        (firstCollectionSource rate rewards C_star C_h q z) U a y)
      ∂ReferencePostInvocationCollectionNativeLaw.innovationLaw (p := p)) =
      episodeRoundTest rate rewards q (RecordedQueueRun.initialState p.K) S U f := by
  let zc := firstCollectionSource rate rewards C_star C_h q z
  obtain ⟨hi, hS, ha⟩ := firstCollectionSource_fields rate rewards C_star C_h q z
  change ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q zc = c at hi
  change ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q zc = S at hS
  change (ReferencePostInvocationNoncallGeometry.collectionArguments rate rewards C_star C_h q zc).1.anchor =
    RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K) at ha
  have he : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q zc).enabled = true := by
    rw [hi]
    exact hen
  have hc : (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q zc).overflow = false := by
    rw [hS]
    exact hpre
  have ht := ReferenceGeneratedCalendarQuantizedRoundKernel.collection_source_quantized_test
    rate rewards C_star C_h q control0 zc U a he hc f 0
  rw [hS] at ht
  refine ht.trans ?_
  have hround (i : Option (Fin p.K)) :
      ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q zc i =
        episodeRoundInput rate rewards q (RecordedQueueRun.initialState p.K) i := by
    have h := hi.trans (firstCollection_native_input rate rewards C_star C_h q z hen)
    apply roundInput_eq_of_fields
    · change (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q zc).enabled =
        (episodeRoundInput rate rewards q (RecordedQueueRun.initialState p.K) (c).recordedArm).enabled
      exact congrArg RecordedQueueRun.RoundInput.enabled h
    · rfl
    · change (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q zc).reward =
        (episodeRoundInput rate rewards q (RecordedQueueRun.initialState p.K) (c).recordedArm).reward
      exact congrArg RecordedQueueRun.RoundInput.reward h
    · change (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q zc).rate =
        (episodeRoundInput rate rewards q (RecordedQueueRun.initialState p.K) (c).recordedArm).rate
      exact congrArg RecordedQueueRun.RoundInput.rate h
  have hrec (i : Option (Fin p.K)) :
      ReferencePostInvocationCollectionNativeLaw.recorderPMF rate rewards C_star C_h q zc i =
        RecordedRoundMoments.recordingOutcomePMF
          (ReferenceGeneratedCalendarQuantizedRoundKernel.anchorRates rate
            (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.initialState p.K))
            (RecordedSlowRefresh.scoreWeight_pos Q _)) i := by
    simp only [ReferencePostInvocationCollectionNativeLaw.recorderPMF, ha]
    rfl
  have hfalse : ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {false} =
      ENNReal.ofReal (1 - 4 * p.m * rate.eta.val) := by
    have hs : ({false} : Set Bool) = {true}ᶜ := by ext b; cases b <;> decide
    rw [hs, prob_compl_eq_one_sub (measurableSet_singleton true),
      ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw_true]
    change 1 - ENNReal.ofReal (FollowerCutoffScan.proposalHazard p rate.eta.val) =
      ENNReal.ofReal (1 - FollowerCutoffScan.proposalHazard p rate.eta.val)
    rw [ENNReal.ofReal_sub 1
      (ReferenceFirstLivePostUpdateProposalLaw.physicalProposalThreshold_bounds rate).1.le, ENNReal.ofReal_one]
  have haux (i : Option (Fin p.K)) (B : Bool) (V : SlowSet p) :
      ReferencePostInvocationCollectionNativeLaw.auxiliaryMass rate rewards C_star C_h q zc U i B V =
        ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B} *
          episodeNextLaw rate rewards q (RecordedQueueRun.initialState p.K) S U i B {V} := by
    cases B with
    | true =>
      simp only [ReferencePostInvocationCollectionNativeLaw.auxiliaryMass, ite_true, hS, hround, ha,
        episodeNextLaw, hpre, Bool.false_eq_true, ite_false,
        PMF.toMeasure_apply_singleton _ V (measurableSet_singleton V), RecordedSlowRefresh.residualPMF_apply,
        ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw_true, FollowerCutoffScan.proposalHazard]
    | false =>
      simp only [ReferencePostInvocationCollectionNativeLaw.auxiliaryMass, Bool.false_eq_true, ite_false,
        episodeNextLaw, hpre, hfalse, Measure.dirac_apply' _ (measurableSet_singleton V),
        Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, eq_comm]
  unfold episodeRoundTest
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro V _
  rw [hround, hrec, haux]
  simp only [hpre, Bool.not_false, Bool.true_and]
  ac_rfl

end CollectionAuxiliary
end SourceGeometry

section SupportedPrefix

open ReferenceGeneratedCalendarEpisodeSlowLaw
open ReferenceFirstCollectionLogicalPrefixExtension

local instance prefixOptionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

attribute [local instance] ReferenceRankInstallationPostUpdateProposalLaw.optionSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.listMeasurableSingleton

/-- The complete numerical PRE match is produced on the original erased
experiment. Both source gates and the current no-call gate are retained.
The seed and replay equations are conclusions, for raw and every fixed ID. -/
theorem ae_erased_prefix_retained_pre
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) :
    ∀ᵐ v ∂(((ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
        (eraseProposal q)).prod scalarLaw).prod (calendarInnovationLaw p),
      let h := prefixSourceHistory rate control0 s q v.1.1
      noCallAt rate rewards C_star C_h q v.1.1.1 →
      h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s →
      h ∈ sourceHistoryRetained rate rewards C_star C_h s q →
      ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h
          s.castSucc h.1.1 = some (RecordedQueueRun.initialState p.K) ∧
        (prefixCurrentMark rate rewards C_star C_h q (refillProposal q v.1, v.2)).map
          LogicalCell.before = sourceEpisodeReplay rate rewards C_star C_h s q h := by
  let μ := ids.elim Lambda
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)
  let β := ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
    (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)
  let g := fun w => (prefixObservation rate rewards C_star C_h control0 q.castSucc w,
    currentInnovation rate rewards C_star C_h control0 q w)
  let P : Obs × Innovation → Prop := fun v =>
    let h := prefixSourceHistory rate control0 s q v.1
    noCallAt rate rewards C_star C_h q v.1.1 →
    h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s →
    h ∈ sourceHistoryRetained rate rewards C_star C_h s q →
    ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h
        s.castSucc h.1.1 = some (RecordedQueueRun.initialState p.K) ∧
      (prefixCurrentMark rate rewards C_star C_h q v).map LogicalCell.before =
        sourceEpisodeReplay rate rewards C_star C_h s q h
  have hh : Measurable (fun v : Obs × Innovation => prefixSourceHistory rate control0 s q v.1) :=
    (measurable_prefixSourceHistory rate control0 s q).comp measurable_fst
  have hm : Measurable (fun v : Obs × Innovation =>
      (prefixCurrentMark rate rewards C_star C_h q v).map LogicalCell.before) :=
    LaterAssignmentFullOutputMeasurability.measurable_optionMap _ measurable_logicalCell_before _
      (measurable_prefixCurrentMark rate rewards C_star C_h control0 q)
  have hP : MeasurableSet {v | P v} := by
    have he := (measurableSet_eq_fun
      ((ReferencePostInvocationPrefixLocality.measurable_prefixNumerical
        rate rewards C_star C_h s.castSucc).comp hh.fst.fst)
        (measurable_const (a := some (RecordedQueueRun.initialState p.K)))).inter
      (measurableSet_eq_fun hm
        ((measurable_sourceEpisodeReplay rate rewards C_star C_h s q).comp hh))
    have hr := (measurableSet_sourceHistoryRetained rate rewards C_star C_h s q).preimage hh
    have hs := (measurableSet_sourceStartEvent rate rewards C_star C_h control0 s).preimage hh.fst.fst
    have hn : MeasurableSet {v : Obs × Innovation | noCallAt rate rewards C_star C_h q v.1.1} :=
      (measurableSet_noCallAt rate rewards C_star C_h control0 q).preimage measurable_fst.fst
    convert hn.compl.union (hs.compl.union (hr.compl.union he)) using 1
    ext v
    simp only [P, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_preimage, Set.mem_ofPred_eq, Function.comp_apply, imp_iff_not_or]
  have hg : Measurable g :=
    (measurable_prefixObservation rate rewards C_star C_h control0 q.castSucc).prodMk
      (measurable_currentInnovation rate rewards C_star C_h control0 q)
  have hprod : (μ.restrict (beforeFirstCall rate rewards C_star C_h q.castSucc)).map g =
      β.prod (calendarInnovationLaw p) := by
    cases ids with
    | none =>
      exact terminalLaw_restrict_map_prefixObservation_innovation rate rewards C_star C_h control0 q
    | some id =>
      exact fixedIDTerminalLaw_restrict_map_prefixObservation_innovation rate rewards C_star C_h control0 id q
  have hraw : ∀ᵐ v ∂β.prod (calendarInnovationLaw p), P v := by
    rw [← hprod]
    apply (ae_map_iff hg.aemeasurable hP).mpr
    apply (ae_restrict_iff' (measurableSet_beforeFirstCall rate rewards C_star C_h control0 q.castSucc)).mpr
    filter_upwards [ae_retained_source_input rate rewards C_star C_h control0 ids,
      ae_retainedEvent_sourceHistory rate rewards C_star C_h control0 ids] with w hw hr
    intro hpre
    dsimp only [P, g]
    rw [prefixSourceHistory_actual rate rewards C_star C_h control0 s q hsq w hpre]
    intro hno hs hret
    have hsucc : w ∈ beforeFirstCall rate rewards C_star C_h q.succ := by
      apply (noCallBefore_succ rate rewards C_star C_h q _).mpr
      refine ⟨hpre, ?_⟩
      exact (noCallAt_sourcePrefix rate rewards C_star C_h control0 q q.val le_rfl _).mpr hno
    have hstart : w ∈ episodeStartEvent rate rewards C_star C_h control0 s := by
      rw [episodeStartEvent_eq_history_preimage]
      exact hs
    have hret' := (hr s q hstart).mpr hret
    obtain ⟨e, _, _, he, _, _, _, hrep, _⟩ := hw s q hstart hret'
    refine ⟨terminal_beforeFirstCall_seed rate rewards C_star C_h control0 s q hsq w hsucc hstart, ?_⟩
    rw [prefixCurrentMark_actual rate rewards C_star C_h control0 q w hsucc, he, hrep]
    rfl
  let split : Obs → Obs × Scalar := fun o => (eraseProposal q o, currentProposal q o)
  have hsplit : Measurable split := (measurable_eraseProposal q).prodMk (measurable_currentProposal q)
  let r : (Obs × Scalar) × Innovation → Obs × Innovation :=
    fun v => (refillProposal q v.1, v.2)
  have hr : Measurable r :=
    ((measurable_refillProposal q).comp measurable_fst).prodMk measurable_snd
  have hmap : (β.prod (calendarInnovationLaw p)).map (Prod.map split id) =
      ((β.map (eraseProposal q)).prod scalarLaw).prod (calendarInnovationLaw p) := by
    rw [← Measure.map_prod_map β (calendarInnovationLaw p) hsplit measurable_id,
      Measure.map_id, betaPre_currentProposal_erasure_product rate rewards C_star C_h control0 ids q]
  have htransport : ∀ᵐ v ∂((β.map (eraseProposal q)).prod scalarLaw).prod
      (calendarInnovationLaw p), P (r v) := by
    rw [← hmap]
    apply (ae_map_iff (hsplit.prodMap measurable_id).aemeasurable (hP.preimage hr)).mpr
    filter_upwards [hraw] with v hv
    change P (refillProposal q (eraseProposal q v.1, currentProposal q v.1), v.2)
    rw [refillProposal_erase_current]
    exact hv
  exact htransport

/-- Erasure retains a strict chronological past. On the actual first
collection domain, its incoming set is present and is read from that same
past; no coverage or incoming-set certificate is supplied. -/
theorem ae_erased_prefix_collection_incoming
    (ids : Option (CompletePublicTable.IDArray p)) (q : Fin p.T) :
    ∀ᵐ o ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
        (eraseProposal q),
      (∀ e ∈ o.2.2, e.time.val < q.val) ∧
        (o.1 ∈ ReferenceFirstCollectionOneRoundLogicalCell.actualDomain
          (rate := rate) rewards C_star C_h q →
          (incomingFromList rate o.2.2).isSome = true) := by
  let P : Obs → Prop := fun o => (∀ e ∈ o.2.2, e.time.val < q.val) ∧
    (o.1 ∈ ReferenceFirstCollectionOneRoundLogicalCell.actualDomain
      (rate := rate) rewards C_star C_h q → (incomingFromList rate o.2.2).isSome = true)
  have hP : MeasurableSet {o | P o} := by
    have ht : Measurable (fun o : Obs => o.2.2.map LogicalCell.time) :=
      ReferenceActiveHorizonMeasurability.measurable_list_map _ measurable_snd.snd
        _ measurable_logicalCell_time
    have hlist : MeasurableSet {o : Obs | ∀ e ∈ o.2.2, e.time.val < q.val} := by
      have hb := (measurable_of_countable (fun L : List (Fin p.T) =>
        L.all (fun t => decide (t.val < q.val)))).comp ht
      simpa only [List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq] using
        measurableSet_eq_fun hb (measurable_const (a := true))
    have hd : MeasurableSet {o : Obs | o.1 ∈ ReferenceFirstCollectionOneRoundLogicalCell.actualDomain
        (rate := rate) rewards C_star C_h q} :=
      (ReferenceFirstCollectionOneRoundLogicalCell.measurableSet_actualDomain
        rewards C_star C_h q control0).preimage measurable_fst
    have hi : Measurable (fun o : Obs => (incomingFromList rate o.2.2).isSome) :=
      (measurable_of_countable Option.isSome).comp
        ((measurable_incomingFromList rate).comp measurable_snd.snd)
    convert hlist.inter (hd.compl.union (measurableSet_eq_fun hi (measurable_const (a := true)))) using 1
    ext o
    simp only [P, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_ofPred_eq, imp_iff_not_or]
  have horiginal (za : BootstrapPrivateRoundStreams.SourceInput p ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
      P (extendedObservation rate rewards C_star C_h control0 q.castSucc za) := by
    refine ⟨extendedPast_time_lt rate rewards C_star C_h q.castSucc za, ?_⟩
    intro hd
    have hd0 := (actualDomain_sourcePrefix rate rewards C_star C_h control0 q q.val le_rfl za.1).mpr hd
    obtain ⟨U, hU⟩ := generatedIncoming_present rate rewards C_star C_h q za.1 za.2 hd0
    change (incomingFromList rate (extendedPast rate rewards C_star C_h q.castSucc za)).isSome = true
    change (incomingFromList rate (extendedPrefixStateAux rate rewards C_star C_h q.val q.isLt.le za).2).isSome = true
    unfold incomingFromList
    rw [← extendedPrefixStateAux_seed rate rewards C_star C_h q.val q.isLt.le za, hU]
    rfl
  have hraw : ∀ᵐ o ∂betaPre rate rewards C_star C_h control0 q.castSucc, P o := by
    rw [← extendedObservation_map_restrict_eq_betaPre rate rewards C_star C_h control0 q.castSucc]
    apply (ae_map_iff (measurable_extendedObservation rate rewards C_star C_h control0 q.castSucc).aemeasurable hP).mpr
    exact Filter.Eventually.of_forall horiginal
  have hids : ∀ᵐ o ∂ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc), P o := by
    cases ids with
    | none => exact hraw
    | some id =>
      exact Measure.ae_smul_measure (hraw.filter_mono ae_restrict_le) _
  apply (ae_map_iff (measurable_eraseProposal q).aemeasurable hP).mpr
  exact hids

include control0 in
/-- On the supported collection branch the prefix operation reads precisely
the original current source and the incoming set from the unchanged past. -/
theorem prefixCurrentMark_firstCollection (q : Fin p.T) (o : Obs)
    (hd : o.1 ∈ ReferenceFirstCollectionOneRoundLogicalCell.actualDomain
      (rate := rate) rewards C_star C_h q)
    (hpast : ∀ e ∈ o.2.2, e.time.val < q.val)
    (U : SlowSet p) (hU : incomingFromList rate o.2.2 = some U)
    (x : Scalar) (ux : Innovation) :
    prefixCurrentMark rate rewards C_star C_h q (refillProposal q (o, x), ux) =
      collectionCellAt rate rewards C_star C_h q U
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q o.1 ux.1,
          roundAuxiliary q ((refillProposal q (o, x)).2.1, ux.2)) := by
  let z := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q o.1 ux.1
  let a := roundAuxiliary q ((refillProposal q (o, x)).2.1, ux.2)
  have hdz : z ∈ ReferenceFirstCollectionOneRoundLogicalCell.actualDomain
      (rate := rate) rewards C_star C_h q := by
    apply (ReferenceFirstCollectionOneRoundLogicalCell.actualDomain_iff_oldSelector
      rewards C_star C_h q z).mpr
    exact (ReferenceFirstCollectionOldSelectorRecordingLaw.oldSelector_replaceCurrent
      rate rewards C_star C_h control0 q o.1 ux.1).mpr
        ((ReferenceFirstCollectionOneRoundLogicalCell.actualDomain_iff_oldSelector
          rewards C_star C_h q o.1).mp hd)
  have htag := currentCellTag_absent_of_actualDomain rate rewards C_star C_h q z a hdz
  have hp : o.2.2.find? (fun e => e.time == q) = none := by
    apply List.find?_eq_none.mpr
    intro e he h
    exact (hpast e he).ne (congrArg Fin.val (beq_iff_eq.mp h))
  have htime (e : LogicalCell p rate)
      (he : collectionCellAt rate rewards C_star C_h q U (z, a) = some e) : e.time = q := by
    unfold collectionCellAt ReferenceFirstCollectionOneRoundLogicalCell.sourceCell? at he
    rw [dite_eq_left hdz] at he
    dsimp only at he
    unfold ReferenceFirstCollectionOneRoundLogicalCell.cellWithScalar? at he
    split at he
    · cases Option.some.inj he
      rfl
    · cases he
  change ((extendedPrefixStep rate rewards C_star C_h q (z, a)
    (incomingFromList rate o.2.2, o.2.2)).2.find? (fun e => e.time == q)) = _
  rw [hU]
  unfold extendedPrefixStep prefixStep prefixCandidate
  rw [htag]
  dsimp only
  cases hc : collectionCellAt rate rewards C_star C_h q U (z, a) with
  | none => exact hp
  | some e =>
    simp only [List.find?_append, hp, Option.none_or, List.find?_cons,
      htime e hc, beq_self_eq_true]

/-- The actual retained erased history produces the enabled collection
input, clear complete native PRE and strict seed internally. Current control,
proposal and residual draws are used only to read an almost-everywhere
supported original mark; no desired numerical match is an input. -/
theorem ae_erased_prefix_firstCollection_pre
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T) (hsq : s.val ≤ q.val) :
    ∀ᵐ o ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
        (eraseProposal q),
      ∀ hd : o.1 ∈ ReferenceFirstCollectionOneRoundLogicalCell.actualDomain
        (rate := rate) rewards C_star C_h q,
      let z : ReferenceFirstCollectionOneRoundLogicalCell.ActualSource
        (rate := rate) rewards C_star C_h q := ⟨o.1, hd⟩
      let r := ReferenceFirstCollectionOneRoundLogicalCell.domainRecord rewards C_star C_h q z
      let hr := ReferenceFirstCollectionOneRoundLogicalCell.domainRecord_spec rewards C_star C_h q z
      let hm := ReferenceFirstCollectionOneRoundLogicalCell.domainRecord_mem rewards C_star C_h q z
      let h := prefixSourceHistory rate control0 s q o
      noCallAt rate rewards C_star C_h q o.1 →
      h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s →
      h ∈ sourceHistoryRetained rate rewards C_star C_h s q →
      (ReferenceFirstCollectionOneRoundLogicalCell.actualInput rewards C_star C_h z.val q r hr hm).enabled = true ∧
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstCollectionOneRoundLogicalCell.actualPast rewards C_star C_h z.val q r hr hm)).overflow = false ∧
        ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h
          s.castSucc h.1.1 = some (RecordedQueueRun.initialState p.K) ∧
        sourceEpisodeReplay rate rewards C_star C_h s q h =
          some (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (ReferenceFirstCollectionOneRoundLogicalCell.actualPast rewards C_star C_h z.val q r hr hm)) := by
  have hpre := Measure.ae_ae_of_ae_prod (Measure.ae_ae_of_ae_prod
    (ae_erased_prefix_retained_pre rate rewards C_star C_h control0 ids s q hsq))
  filter_upwards [ae_erased_prefix_collection_incoming rate rewards C_star C_h control0 ids q,
    hpre] with o ho hsupport
  intro hd z r hr hm h hn hs hret
  obtain ⟨U, hU⟩ := Option.isSome_iff_exists.mp (ho.2 hd)
  obtain ⟨x, hx⟩ := hsupport.exists
  obtain ⟨ux, hux⟩ := hx.exists
  obtain ⟨hseed, hmatch⟩ := hux hn hs hret
  rw [prefixCurrentMark_firstCollection rate rewards C_star C_h control0 q o hd ho.1 U hU x ux] at hmatch
  let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q o.1 ux.1
  have hd' : z' ∈ ReferenceFirstCollectionOneRoundLogicalCell.actualDomain
      (rate := rate) rewards C_star C_h q := by
    exact (ReferenceFirstCollectionOneRoundLogicalCell.actualDomain_iff_oldSelector
      rewards C_star C_h q z').mpr
      ((ReferenceFirstCollectionOldSelectorRecordingLaw.oldSelector_replaceCurrent
        rate rewards C_star C_h control0 q o.1 ux.1).mpr
        ((ReferenceFirstCollectionOneRoundLogicalCell.actualDomain_iff_oldSelector
          rewards C_star C_h q o.1).mp hd))
  let d : ReferenceFirstCollectionOneRoundLogicalCell.ActualSource
    (rate := rate) rewards C_star C_h q := ⟨z', hd'⟩
  let rd := ReferenceFirstCollectionOneRoundLogicalCell.domainRecord rewards C_star C_h q d
  let hrd := ReferenceFirstCollectionOneRoundLogicalCell.domainRecord_spec rewards C_star C_h q d
  let hmd := ReferenceFirstCollectionOneRoundLogicalCell.domainRecord_mem rewards C_star C_h q d
  let cd := ReferenceFirstCollectionOneRoundLogicalCell.actualInput rewards C_star C_h d.val q rd hrd hmd
  let Sd := RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (ReferenceFirstCollectionOneRoundLogicalCell.actualPast rewards C_star C_h d.val q rd hrd hmd)
  let zc := firstCollectionSource rate rewards C_star C_h q z
  have hdnative : firstCollectionSource rate rewards C_star C_h q d =
      ReferencePostInvocationCollectionNativeLaw.replaceCollectionSource rate rewards C_star C_h control0 q zc ux.1 :=
    Subtype.ext rfl
  have hbefore := (firstCollectionSource_fields rate rewards C_star C_h q d).2.1.symm.trans
    ((congrArg (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q) hdnative).trans
      ((ReferencePostInvocationCollectionNativeLaw.collectionBefore_replace_control
        rate rewards C_star C_h control0 q zc ux.1).trans
        (firstCollectionSource_fields rate rewards C_star C_h q z).2.1))
  have henabled := congrArg RecordedQueueRun.RoundInput.enabled
    (firstCollectionSource_fields rate rewards C_star C_h q d).1.symm
  rw [hdnative, ReferencePostInvocationCollectionNativeLaw.collectionEnabled_replace_control,
    (firstCollectionSource_fields rate rewards C_star C_h q z).1] at henabled
  unfold collectionCellAt ReferenceFirstCollectionOneRoundLogicalCell.sourceCell? at hmatch
  rw [dite_eq_left hd'] at hmatch
  change (if cd.enabled then some (ReferenceFirstCollectionOneRoundLogicalCell.cellWithScalar
    rewards C_star C_h d.val q rd hrd hmd U _ _ _) else none).map LogicalCell.before =
      sourceEpisodeReplay rate rewards C_star C_h s q h at hmatch
  have hclear := hret.2.2
  cases he : cd.enabled with
  | false =>
    simp only [he, Bool.false_eq_true, ite_false, Option.map_none] at hmatch
    rw [← hmatch] at hclear
    cases hclear
  | true =>
    simp only [he, ite_true, Option.map_some] at hmatch
    change some Sd = sourceEpisodeReplay rate rewards C_star C_h s q h at hmatch
    rw [← hmatch] at hclear
    have hSd : Sd.overflow = false := by
      cases hf : Sd.overflow
      · rfl
      · simp only [Option.any_some, hf, Bool.not_true, Bool.false_eq_true] at hclear
    exact ⟨henabled.symm.trans he, (congrArg RecordedQueueRun.RunState.overflow hbefore).symm.trans hSd,
      hseed, hmatch.symm.trans (congrArg some hbefore)⟩

private theorem prefixSourceJoint_firstCollection_outcomeTest
    (s q : Fin p.T) (o : Obs)
    (hd : o.1 ∈ ReferenceFirstCollectionOneRoundLogicalCell.actualDomain
      (rate := rate) rewards C_star C_h q)
    (hpast : ∀ e ∈ o.2.2, e.time.val < q.val)
    (U : SlowSet p) (hU : incomingFromList rate o.2.2 = some U) :
    let z : ReferenceFirstCollectionOneRoundLogicalCell.ActualSource
      (rate := rate) rewards C_star C_h q := ⟨o.1, hd⟩
    let zc := firstCollectionSource rate rewards C_star C_h q z
    let S := ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q zc
    (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q zc).enabled = true →
    S.overflow = false → ∀ (F : TransitionData rate s q → ℝ≥0∞) (y : ContinuousLearningRows.TimeControl p × Scalar × Scalar),
    optionalTransitionTest rate s q F (prefixSourceJoint rate rewards C_star C_h control0 s q
      (refillProposal q (o, y.2.1), (y.1, y.2.2))) =
      ReferenceGeneratedCalendarQuantizedRoundKernel.outcomeTest rate S
        (ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q zc)
        (fun x B V => F (prefixSourceHistory rate control0 s q o, (U, (x, (B, V))))) 0
        (ReferencePostInvocationCollectionNativeLaw.sourceOutcome rate rewards C_star C_h control0 q zc U
          (roundAuxiliary q (o.2.1, ReferenceFirstLiveActualRefreshTestLaw.scalarZero)) y) := by
  intro z zc S hen hpre F y
  let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q o.1 y.1
  have hd' : z' ∈ ReferenceFirstCollectionOneRoundLogicalCell.actualDomain
      (rate := rate) rewards C_star C_h q := by
    exact (ReferenceFirstCollectionOneRoundLogicalCell.actualDomain_iff_oldSelector
      rewards C_star C_h q z').mpr
      ((ReferenceFirstCollectionOldSelectorRecordingLaw.oldSelector_replaceCurrent
        rate rewards C_star C_h control0 q o.1 y.1).mpr
        ((ReferenceFirstCollectionOneRoundLogicalCell.actualDomain_iff_oldSelector
          rewards C_star C_h q o.1).mp hd))
  let d : ReferenceFirstCollectionOneRoundLogicalCell.ActualSource
    (rate := rate) rewards C_star C_h q := ⟨z', hd'⟩
  let a := roundAuxiliary q ((refillProposal q (o, y.2.1)).2.1, y.2.2)
  have ha : a = ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q
      (roundAuxiliary q (o.2.1, ReferenceFirstLiveActualRefreshTestLaw.scalarZero)) y.2 := by
    funext tl
    rcases tl with ⟨t, l⟩
    fin_cases l <;> by_cases ht : t = q <;>
      simp [a, roundAuxiliary, refillProposal,
        ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair, ht]
  have hz : firstCollectionSource rate rewards C_star C_h q d =
      ReferencePostInvocationCollectionNativeLaw.replaceCollectionSource rate rewards C_star C_h control0 q zc y.1 :=
    Subtype.ext rfl
  have hmark := prefixCurrentMark_firstCollection rate rewards C_star C_h control0 q o hd hpast U hU y.2.1 (y.1, y.2.2)
  change optionalTransitionTest rate s q F
    (prefixSourceHistory rate control0 s q o,
      (sourceOptionalEstimate rate (prefixCurrentMark rate rewards C_star C_h q _),
        prefixCurrentMark rate rewards C_star C_h q _)) = _
  rw [hmark]
  unfold collectionCellAt ReferenceFirstCollectionOneRoundLogicalCell.sourceCell?
  rw [dite_eq_left hd']
  dsimp only
  refine (firstCollection_optionalTransitionTest_eq_native rate rewards C_star C_h q d s F
    (prefixSourceHistory rate control0 s q o) U a).trans ?_
  rw [hz, ha]
  let dc := ReferencePostInvocationCollectionNativeLaw.replaceCollectionSource
    rate rewards C_star C_h control0 q zc y.1
  let ea := ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q
    (roundAuxiliary q (o.2.1, ReferenceFirstLiveActualRefreshTestLaw.scalarZero)) y.2
  have hx : sourceCellEstimate rate
      (ReferencePostInvocationNoncallGeometry.laterCollectionCell rate rewards C_star C_h q dc U ea) =
      RecordedRoundMoments.rawEstimate (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q dc)
        (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q dc) := by
    funext i
    exact sourceCellEstimate_eq_rawEstimate rate _ _ rfl i
  simp only [ReferencePostInvocationCollectionNativeLaw.sourceOutcome,
    ReferencePostInvocationNoncallGeometry.laterCollectionCell?,
    ReferencePostInvocationCollectionNativeLaw.collectionEnabled_replace_control, hen, ite_true,
    optionalTransitionTest, sourceOptionalEstimate_some,
    ReferencePostInvocationCollectionNativeLaw.optionalOutcome]
  rw [hx]
  dsimp only [dc]
  change (ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q zc).overflow = false at hpre
  simp only [ReferencePostInvocationCollectionNativeLaw.cellOutcome,
    ReferencePostInvocationNoncallGeometry.laterCollectionCell,
    ReferencePostInvocationCollectionNativeLaw.collectionBefore_replace_control,
    ReferencePostInvocationCollectionNativeLaw.collectionInput_replace_control,
    ReferenceGeneratedCalendarQuantizedRoundKernel.outcomeTest,
    ReferencePostInvocationCollectionNativeLaw.markerRound,
    ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates,
    hpre, Bool.false_eq_true, ite_false, Sum.elim_inr]
  rfl

/-- The actual first-collection branch has the same retained transition test
as the common kernel, jointly with its original erased history and incoming
set. All native matches and branch conditions are produced internally.
The current no-call gate remains inside both original experiments. -/
theorem ae_erased_prefix_firstCollection_transition_test
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T) (hsq : s.val ≤ q.val) :
    ∀ᵐ o ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
        (eraseProposal q),
      ∀ _ : o.1 ∈ ReferenceFirstCollectionOneRoundLogicalCell.actualDomain
        (rate := rate) rewards C_star C_h q,
      ∀ F : TransitionData rate s q → ℝ≥0∞,
        (∫⁻ x, ∫⁻ ux, if noCallAt rate rewards C_star C_h q o.1 then
          retainedSourceTest rate rewards C_star C_h s q F
            (prefixSourceJoint rate rewards C_star C_h control0 s q (refillProposal q (o, x), ux))
          else 0 ∂calendarInnovationLaw p ∂scalarLaw) =
        ∫⁻ x, ∫⁻ ux, if noCallAt rate rewards C_star C_h q o.1 then
          retainedKernelTest rate rewards C_star C_h s q F
            (prefixSourceJoint rate rewards C_star C_h control0 s q (refillProposal q (o, x), ux))
          else 0 ∂calendarInnovationLaw p ∂scalarLaw := by
  filter_upwards [ae_erased_prefix_collection_incoming rate rewards C_star C_h control0 ids q,
    ae_erased_prefix_firstCollection_pre rate rewards C_star C_h control0 ids s q hsq] with o ho hp
  intro hd F
  let z : ReferenceFirstCollectionOneRoundLogicalCell.ActualSource
    (rate := rate) rewards C_star C_h q := ⟨o.1, hd⟩
  let zc := firstCollectionSource rate rewards C_star C_h q z
  let S := ReferencePostInvocationNoncallGeometry.collectionBefore rate rewards C_star C_h q zc
  let h := prefixSourceHistory rate control0 s q o
  obtain ⟨U, hU⟩ := Option.isSome_iff_exists.mp (ho.2 hd)
  by_cases hn : noCallAt rate rewards C_star C_h q o.1
  · by_cases hs : h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s
    · by_cases hret : h ∈ sourceHistoryRetained rate rewards C_star C_h s q
      · obtain ⟨hen0, hclear0, hseed, hrep⟩ := hp hd hn hs hret
        have hfields := firstCollectionSource_fields rate rewards C_star C_h q z
        have hen : (ReferencePostInvocationNoncallGeometry.collectionInput rate rewards C_star C_h q zc).enabled = true := by
          rw [hfields.1]; exact hen0
        have hclear : S.overflow = false := by
          dsimp only [S, zc]
          rw [hfields.2.1]
          exact hclear0
        let a := roundAuxiliary q (o.2.1, ReferenceFirstLiveActualRefreshTestLaw.scalarZero)
        let G := fun y => ReferenceGeneratedCalendarQuantizedRoundKernel.outcomeTest rate S
          (ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q zc)
          (fun x B V => F (h, (U, (x, (B, V))))) 0
          (ReferencePostInvocationCollectionNativeLaw.sourceOutcome rate rewards C_star C_h control0 q zc U a y)
        have hG : Measurable G := (measurable_of_countable _).comp
          (ReferencePostInvocationCollectionNativeLaw.measurable_sourceOutcome rate rewards C_star C_h control0 q zc U a)
        have hsource (x : Scalar) (ux : Innovation) :
            retainedSourceTest rate rewards C_star C_h s q F
              (prefixSourceJoint rate rewards C_star C_h control0 s q (refillProposal q (o, x), ux)) =
              G (ux.1, (x, ux.2)) := by
          unfold retainedSourceTest
          rw [ite_eq_left (show _ from ⟨hs, hret⟩)]
          exact prefixSourceJoint_firstCollection_outcomeTest rate rewards C_star C_h control0
            s q o hd ho.1 U hU hen hclear F (ux.1, (x, ux.2))
        have hkernel (x : Scalar) (ux : Innovation) :
            retainedKernelTest rate rewards C_star C_h s q F
              (prefixSourceJoint rate rewards C_star C_h control0 s q (refillProposal q (o, x), ux)) =
              episodeTransitionTest rate rewards C_star C_h s q F h U := by
          unfold retainedKernelTest retainedSourceTest
          rw [ite_eq_left (show _ from ⟨hs, hret⟩)]
          refine (prefixSourceJoint_firstCollection_outcomeTest rate rewards C_star C_h control0
            s q o hd ho.1 U hU hen hclear
            (kernelLiftTest rate rewards C_star C_h s q F) (ux.1, (x, ux.2))).trans ?_
          rw [ReferencePostInvocationCollectionNativeLaw.sourceOutcome_clear rate rewards C_star C_h control0 q zc U a hen hclear]
          rfl
        simp only [hn, ite_true, hsource, hkernel, lintegral_const, measure_univ, mul_one]
        have hthree : Measurable (fun v : (Scalar × ContinuousLearningRows.TimeControl p) × Scalar =>
            G (v.1.2, (v.1.1, v.2))) :=
          hG.comp (measurable_fst.snd.prodMk (measurable_fst.fst.prodMk measurable_snd))
        calc
          _ = ∫⁻ x, ∫⁻ c, ∫⁻ r, G (c, (x, r)) ∂scalarLaw
              ∂ContinuousLearningRows.timeControlLaw p ∂scalarLaw := by
            apply lintegral_congr
            intro x
            exact lintegral_prod _ ((hG.comp (measurable_fst.prodMk
              (measurable_const.prodMk measurable_snd))).aemeasurable)
          _ = ∫⁻ c, ∫⁻ x, ∫⁻ r, G (c, (x, r)) ∂scalarLaw ∂scalarLaw
              ∂ContinuousLearningRows.timeControlLaw p :=
            lintegral_lintegral_swap hthree.lintegral_prod_right'.aemeasurable
          _ = ∫⁻ y, G y ∂ReferencePostInvocationCollectionNativeLaw.innovationLaw (p := p) := by
            rw [ReferencePostInvocationCollectionNativeLaw.innovationLaw, lintegral_prod G hG.aemeasurable]
            apply lintegral_congr
            intro c
            exact (lintegral_prod _ (hG.comp measurable_prodMk_left).aemeasurable).symm
          _ = _ := by
            have ht := firstCollection_source_quantized_test rate rewards C_star C_h control0 q z U a hen0 hclear0
              (fun x B V => F (h, (U, (x, (B, V)))))
            dsimp only [G, S, zc]
            rw [hfields.2.1, episodeTransitionTest, hseed, hrep]
            exact ht
      · dsimp only [h] at hret
        simp only [hn, ite_true, retainedKernelTest, retainedSourceTest, prefixSourceJoint,
          prefixSourceHistory_refillProposal, hret, and_false, ite_false, lintegral_zero]
    · dsimp only [h] at hs
      simp only [hn, ite_true, retainedKernelTest, retainedSourceTest, prefixSourceJoint,
        prefixSourceHistory_refillProposal, hs, false_and, ite_false, lintegral_zero]
  · simp only [hn, ite_false, lintegral_zero]

end SupportedPrefix
end Bandits.Support.ReferenceGeneratedCalendarErasedCollectionTransition
