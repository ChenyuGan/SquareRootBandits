/-
Copyright (c) 2026 Bandits formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarRoundLaw
public import Bandits.Support.RecordedRoundMoments

/-!
# Quantized local recorder/proposal/refresh tests

Sources: ZIP4 `04_slow_fast_learner.tex:140-180,182-215,329-362` and
`06_interruptions.tex:391-426`.

These are internal laws at fixed native local inputs. Recorder labels are
summed before quantization; a zero estimate never identifies its recorder.
The old set is retained literally, with no assumed distribution. The
marker-specific complete UPDATE determines the existing fixed-anchor residual.
There is no POST-clear gate, so the first detecting UPDATE retains its refresh.
No episode-history conditional law or chronological transport is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferencePostInvocationNoncallGeometry

namespace Bandits.Support.ReferenceGeneratedCalendarQuantizedRoundKernel

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance
local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) := LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩
local instance sumSingleton {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y] : MeasurableSingletonClass (X ⊕ Y) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (measurableSet_singleton a).inl_image
    | inr b => simpa only [Set.image_singleton] using (measurableSet_singleton b).inr_image
local instance optionSingleton {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] : MeasurableSingletonClass (Option X) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit X))
      (measurableSet_singleton ((Equiv.optionEquivSumPUnit X) x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact (Equiv.optionEquivSumPUnit X).injective.eq_iff.symm
local instance outcomeMeasurableSpace :
    MeasurableSpace (ReferencePostInvocationLiveNativeLaw.Outcome p) := ⊤
local instance outcomeDiscrete :
    DiscreteMeasurableSpace (ReferencePostInvocationLiveNativeLaw.Outcome p) :=
  ⟨fun _ => trivial⟩

variable (rate : ReferenceActivePhysicalStep.RateInput p)

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- The single canonical recorder law, evaluated at the actual frozen anchor. -/
def anchorRates (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i) :=
  SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
    rate.sourceCap anchor hanchor

/-- One common estimate test law. It uses the accepted raw estimate and
the original recorder PMF, including bottom and all zero-valued markers. -/
def sourceEstimateTest (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (reward : Fin p.K → ℝ) (hreward : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (before : RecordedQueueRun.RunState p.K) (enabled : Bool)
    (f : (Fin p.K → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i : Option (Fin p.K),
    f (RecordedRoundMoments.rawEstimate Q before
      (RecordedRoundMoments.fixedRoundInput Q (anchorRates rate anchor hanchor)
        reward hreward enabled i)) *
      RecordedRoundMoments.recordingOutcomePMF (anchorRates rate anchor hanchor) i

/-- Literal source marker formula, gated by incoming overflow and enablement.
The quantizer is the existing `quantizedValue`, not a reconstructed marker. -/
theorem source_rawEstimate_formula
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (reward : Fin p.K → ℝ) (hreward : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (before : RecordedQueueRun.RunState p.K) (enabled : Bool)
    (i : Option (Fin p.K)) (a : Fin p.K) :
    RecordedRoundMoments.rawEstimate Q before
        (RecordedRoundMoments.fixedRoundInput Q (anchorRates rate anchor hanchor)
          reward hreward enabled i) a =
      if before.overflow then 0 else if enabled then
        if i = some a then QuantizedRecordingMoments.quantizedValue
          (Q).D (Q).eta ((anchorRates rate anchor hanchor).rate a) (reward a)
        else 0
      else 0 := by
  cases ho : before.overflow
  · cases enabled
    · exact RecordedRoundMoments.rawEstimate_eq_zero_of_disabled Q before _ a rfl
    · exact RecordedRoundMoments.rawEstimate_eq_quantizedValue_of_enabled
        Q before _ reward hreward i a ho
  · exact RecordedRoundMoments.rawEstimate_eq_zero_after_overflow Q before _ a ho

/-- Scores, queues, records and the old slow set are not inputs to the common
estimate law once the incoming overflow flag is fixed. -/
theorem sourceEstimateTest_eq_of_overflow_eq
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (reward : Fin p.K → ℝ) (hreward : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (S T : RecordedQueueRun.RunState p.K) (hST : S.overflow = T.overflow)
    (enabled : Bool) (f : (Fin p.K → ℝ) → ℝ≥0∞) :
    sourceEstimateTest rate anchor hanchor reward hreward S enabled f =
      sourceEstimateTest rate anchor hanchor reward hreward T enabled f := by
  apply Finset.sum_congr rfl
  intro i _hi
  congr 2
  funext a
  rw [source_rawEstimate_formula, source_rawEstimate_formula, hST]

/-- Disabled learning has the zero estimate, irrespective of the physical
recorder labels that are still summed by the common test law. -/
theorem sourceEstimateTest_disabled
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (reward : Fin p.K → ℝ) (hreward : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (S : RecordedQueueRun.RunState p.K) (f : (Fin p.K → ℝ) → ℝ≥0∞) :
    sourceEstimateTest rate anchor hanchor reward hreward S false f = f (fun _ => 0) := by
  have he (i : Option (Fin p.K)) : RecordedRoundMoments.rawEstimate Q S
      (RecordedRoundMoments.fixedRoundInput Q (anchorRates rate anchor hanchor) reward hreward false i) =
      fun _ => 0 := by
    funext j
    exact RecordedRoundMoments.rawEstimate_eq_zero_of_disabled Q S _ j rfl
  simp only [sourceEstimateTest, he, ← Finset.mul_sum]
  have hs := (RecordedRoundMoments.recordingOutcomePMF (anchorRates rate anchor hanchor)).tsum_coe
  rw [tsum_fintype] at hs
  rw [hs, mul_one]

/-- PRE overflow has the same zero estimate without erasing the physical
recorder PMF. This does not stop the first detecting POST update. -/
theorem sourceEstimateTest_overflow
    (anchor : Fin p.K → ℝ) (hanchor : ∀ i, 0 < anchor i)
    (reward : Fin p.K → ℝ) (hreward : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (S : RecordedQueueRun.RunState p.K) (hS : S.overflow = true)
    (enabled : Bool) (f : (Fin p.K → ℝ) → ℝ≥0∞) :
    sourceEstimateTest rate anchor hanchor reward hreward S enabled f = f (fun _ => 0) := by
  have he (i : Option (Fin p.K)) : RecordedRoundMoments.rawEstimate Q S
      (RecordedRoundMoments.fixedRoundInput Q (anchorRates rate anchor hanchor) reward hreward enabled i) =
      fun _ => 0 := by
    funext j
    exact RecordedRoundMoments.rawEstimate_eq_zero_after_overflow Q S _ j hS
  simp only [sourceEstimateTest, he, ← Finset.mul_sum]
  have hs := (RecordedRoundMoments.recordingOutcomePMF (anchorRates rate anchor hanchor)).tsum_coe
  rw [tsum_fintype] at hs
  rw [hs, mul_one]

private theorem sum_fast_eliminate {I J B V : Type*}
    [Fintype I] [Fintype J] [Fintype B] [Fintype V]
    (f : I → B → V → ℝ≥0∞) (mass : I → J → ℝ≥0∞)
    (aux : I → B → V → ℝ≥0∞) :
    (∑ i, ∑ j, ∑ b, ∑ v, f i b v * (mass i j * aux i b v)) =
      ∑ i, ∑ b, ∑ v, f i b v * ((∑ j, mass i j) * aux i b v) := by
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _hv
  rw [← Finset.mul_sum, ← Finset.sum_mul]

/-- Discard FAST only in the test, retaining physical recorder labels. An
absent cell has a separate value; it is not a present bottom marker. -/
def outcomeTest
    (before : RecordedQueueRun.RunState p.K)
    (round : Option (Fin p.K) → RecordedQueueRun.RoundInput p.K)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞)
    (absent : ℝ≥0∞) : ReferencePostInvocationLiveNativeLaw.Outcome p → ℝ≥0∞ :=
  Sum.elim (fun _ => absent) (fun z =>
    f (RecordedRoundMoments.rawEstimate Q before (round z.1)) z.2.2.1 z.2.2.2)

private theorem outcome_lintegral
    (mu : Measure (ReferencePostInvocationLiveNativeLaw.Outcome p))
    (g : Option (Fin p.K) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    (∫⁻ o, Sum.elim (fun _ => absent)
      (fun z : Option (Fin p.K) × Fin p.K × Bool × SlowSet p => g z.1 z.2.2.1 z.2.2.2) o ∂mu) =
      absent * mu {Sum.inl ()} +
        ∑ i, ∑ j : Fin p.K, ∑ B, ∑ V, g i B V * mu {Sum.inr (i, j, B, V)} := by
  rw [lintegral_fintype, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, Sum.elim_inl, Sum.elim_inr]

variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (q : Fin p.T)

local notation "LiveSource" => ContinuingLiveSource rate rewards C_star C_h q
local notation "liveCell" => continuingSourceCell rate rewards C_star C_h q
local notation "liveBefore" => continuingBefore rate rewards C_star C_h q
local notation "liveRound" => ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q
local notation "livePair" => ReferencePostInvocationLiveNativeLaw.nativePairLaw rate rewards C_star C_h q

private theorem roundInput_ext {x y : RecordedQueueRun.RoundInput p.K}
    (he : x.enabled = y.enabled) (hi : x.recordedArm = y.recordedArm)
    (hr : x.reward = y.reward) (hx : x.rate = y.rate) : x = y := by
  cases x
  cases y
  cases he
  cases hi
  cases hr
  cases hx
  rfl

/-- The actual LIVE numerical input uses the canonical frozen-anchor rates.
Its whole reward row and enabled service flag are preserved. -/
theorem liveRound_eq_fixedRoundInput (z : LiveSource) (i : Option (Fin p.K)) :
    liveRound z i = RecordedRoundMoments.fixedRoundInput Q
      (anchorRates rate (liveCell z).selected.view.payload.anchor
        (liveCell z).selected.view.payload.anchor_pos)
      (liveCell z).input.reward
      (fun j => ⟨(liveCell z).input.reward_nonneg j, (liveCell z).input.reward_le_one j⟩)
      true i := by
  apply roundInput_ext
  · exact (liveCell z).enabled
  · rfl
  · rfl
  · change (liveCell z).input.rate = _
    rw [(liveCell z).input_eq]
    rfl

/-- The actual reward vector is the original entire row at this date. -/
theorem liveRound_reward (z : LiveSource) (i : Option (Fin p.K)) :
    (liveRound z i).reward = fun j => ((rewards q j).val : ℝ) / (D p : ℝ) := by
  change (liveCell z).input.reward = _
  rw [(liveCell z).input_eq]
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z.val _
    (continuingSourceCell_spec rate rewards C_star C_h q z).1
  change (fun j => (((continuingRecord rate rewards C_star C_h q z).input.rewards
    (continuingRecord rate rewards C_star C_h q z).input.time j).val : ℝ) / (D p : ℝ)) = _
  rw [hf.2.2.1, hf.2.2.2]

/-- The actual correlated LIVE pair has precisely the recorder PMF at its
own payload anchor. This proves the rates rather than assuming a match. -/
theorem livePair_recorder_map (z : LiveSource) :
    (livePair z).map Prod.fst =
      (RecordedRoundMoments.recordingOutcomePMF
        (anchorRates rate (liveCell z).selected.view.payload.anchor
          (liveCell z).selected.view.payload.anchor_pos)).toMeasure := by
  unfold ReferencePostInvocationLiveNativeLaw.nativePairLaw
  have he : Measurable (fun v : Option (Fin p.K) × CanonicalFastSampling.FastArm
      (SnapshotRecordingKernel.assignmentSlowSet p (liveCell z).selected.view.payload.assignment) =>
        (v.1, v.2.val)) := measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
  rw [Measure.map_map measurable_fst he]
  exact FastRewardSliceLaw.liveRecordingFastPushforward_fst p rate.eta.val
    rate.eta.property rate.sourceCap _ _ _ _ _ _ _ _

/-- Summing FAST includes every bottom and null recorder mass. -/
theorem livePair_recorder_sum (z : LiveSource) (i : Option (Fin p.K)) :
    (∑ j : Fin p.K, livePair z {(i, j)}) =
      RecordedRoundMoments.recordingOutcomePMF
        (anchorRates rate (liveCell z).selected.view.payload.anchor
          (liveCell z).selected.view.payload.anchor_pos) i := by
  have htest : Measurable (fun k : Option (Fin p.K) => if k = i then (1 : ℝ≥0∞) else 0) :=
    measurable_of_countable _
  have h := lintegral_map htest measurable_fst (μ := livePair z)
  rw [livePair_recorder_map, lintegral_fintype, lintegral_fintype] at h
  simp only [Fintype.sum_prod_type] at h
  rw [Finset.sum_comm] at h
  simpa only [ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] using h.symm

/-- The source estimate marginal is the common frozen-anchor law, independent
of FAST and the current old set at fixed anchor, reward row and PRE flags. -/
theorem live_estimate_marginal (z : LiveSource)
    (f : (Fin p.K → ℝ) → ℝ≥0∞) :
    (∫⁻ v, f (RecordedRoundMoments.rawEstimate Q (liveBefore z) (liveRound z v.1))
      ∂livePair z) =
      sourceEstimateTest rate (liveCell z).selected.view.payload.anchor
        (liveCell z).selected.view.payload.anchor_pos (liveCell z).input.reward
        (fun j => ⟨(liveCell z).input.reward_nonneg j, (liveCell z).input.reward_le_one j⟩)
        (liveBefore z) true f := by
  rw [← lintegral_map (measurable_of_countable
    (fun i => f (RecordedRoundMoments.rawEstimate Q (liveBefore z) (liveRound z i))))
    measurable_fst, livePair_recorder_map, lintegral_fintype]
  simp only [sourceEstimateTest, liveRound_eq_fixedRoundInput,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

/-- The clear incoming LIVE kernel evaluated on arbitrary nonnegative tests
of the quantized estimate, proposal and next set. FAST is eliminated using
its actual marginal, without asserting recorder/FAST independence. -/
theorem live_quantized_test (z : LiveSource)
    (hpre : (liveBefore z).overflow = false)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    (∫⁻ o, outcomeTest rate (liveBefore z) (liveRound z) f absent o
      ∂ReferencePostInvocationLiveNativeLaw.nativeLaw rate rewards C_star C_h q z) =
      ∑ i : Option (Fin p.K), ∑ B : Bool, ∑ V : SlowSet p,
        f (RecordedRoundMoments.rawEstimate Q (liveBefore z) (liveRound z i)) B V *
          (RecordedRoundMoments.recordingOutcomePMF
            (anchorRates rate (liveCell z).selected.view.payload.anchor
              (liveCell z).selected.view.payload.anchor_pos) i *
            (if B then ENNReal.ofReal (4 * (p.m : ℝ) * rate.eta.val) *
              ReferencePostInvocationLiveNativeLaw.residualLaw rate rewards C_star C_h q z i {V}
            else ENNReal.ofReal (1 - 4 * (p.m : ℝ) * rate.eta.val) *
              if V = (liveCell z).selected.view.payload.slowSet then 1 else 0)) := by
  change (∫⁻ o, Sum.elim (fun _ => absent)
    (fun x : Option (Fin p.K) × Fin p.K × Bool × SlowSet p =>
      f (RecordedRoundMoments.rawEstimate Q (liveBefore z) (liveRound z x.1)) x.2.2.1 x.2.2.2) o ∂_) = _
  rw [outcome_lintegral _
    (fun i B V => f (RecordedRoundMoments.rawEstimate Q (liveBefore z) (liveRound z i)) B V) absent,
    ReferencePostInvocationLiveNativeLaw.nativeLaw_absent,
    mul_zero, zero_add]
  simp_rw [ReferencePostInvocationLiveNativeLaw.nativeLaw_atom_clear
    rate rewards C_star C_h q z hpre]
  rw [sum_fast_eliminate]
  simp_rw [livePair_recorder_sum]

/-- The same formula is a whole-original-control/two-auxiliary-label test,
not a replacement physical experiment. -/
theorem live_source_quantized_test
    (control0 : ContinuousLearningRows.TimeControl p) (z : LiveSource)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (hpre : (liveBefore z).overflow = false)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    (∫⁻ y, outcomeTest rate (liveBefore z) (liveRound z) f absent
      (ReferencePostInvocationLiveNativeLaw.sourceOutcome
        rate rewards C_star C_h control0 q z a y)
      ∂(ContinuousLearningRows.timeControlLaw p).prod
        (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)) =
      ∑ i : Option (Fin p.K), ∑ B : Bool, ∑ V : SlowSet p,
        f (RecordedRoundMoments.rawEstimate Q (liveBefore z) (liveRound z i)) B V *
          (RecordedRoundMoments.recordingOutcomePMF
            (anchorRates rate (liveCell z).selected.view.payload.anchor
              (liveCell z).selected.view.payload.anchor_pos) i *
            (if B then ENNReal.ofReal (4 * (p.m : ℝ) * rate.eta.val) *
              ReferencePostInvocationLiveNativeLaw.residualLaw rate rewards C_star C_h q z i {V}
            else ENNReal.ofReal (1 - 4 * (p.m : ℝ) * rate.eta.val) *
              if V = (liveCell z).selected.view.payload.slowSet then 1 else 0)) := by
  rw [← lintegral_map (measurable_of_countable _)
    (ReferencePostInvocationLiveNativeLaw.sourceOutcome_law rate rewards C_star C_h control0 q z a).1,
    (ReferencePostInvocationLiveNativeLaw.sourceOutcome_law rate rewards C_star C_h control0 q z a).2]
  exact live_quantized_test rate rewards C_star C_h q z hpre f absent

/-- Incoming overflow freezes only the effective coordinates. The physical
pair remains in `livePair`; no Bernoulli effective proposal is claimed. -/
theorem live_overflow_quantized_test (z : LiveSource)
    (hpre : (liveBefore z).overflow = true)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    (∫⁻ o, outcomeTest rate (liveBefore z) (liveRound z) f absent o
      ∂ReferencePostInvocationLiveNativeLaw.nativeLaw rate rewards C_star C_h q z) =
      f (fun _ => 0) false (frozenSlowSet p) := by
  rw [ReferencePostInvocationLiveNativeLaw.nativeLaw_overflow rate rewards C_star C_h q z hpre,
    lintegral_dirac']
  · change f (RecordedRoundMoments.rawEstimate Q (liveBefore z) (liveRound z none)) false _ = _
    congr 1
    funext j
    exact RecordedRoundMoments.rawEstimate_eq_zero_after_overflow Q _ _ j hpre
  · exact measurable_of_countable _

local notation "CollectionSource" => CollectionDateSource rate rewards C_star C_h q
local notation "collectionPre" => collectionBefore rate rewards C_star C_h q
local notation "collectionP" => collectionArguments rate rewards C_star C_h q
local notation "collectionRound" => ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q

/-- Actual collection input rates are identified from its admitted constructor
and the SAME retained payload, rather than a rate-matching premise. -/
theorem collectionRound_eq_fixedRoundInput (z : CollectionSource) (i : Option (Fin p.K)) :
    collectionRound z i = RecordedRoundMoments.fixedRoundInput Q
      (anchorRates rate (collectionP z).1.anchor (collectionP z).1.anchor_pos)
      (collectionInput rate rewards C_star C_h q z).reward
      (fun j => ⟨(collectionInput rate rewards C_star C_h q z).reward_nonneg j,
        (collectionInput rate rewards C_star C_h q z).reward_le_one j⟩)
      (collectionInput rate rewards C_star C_h q z).enabled i := by
  obtain ⟨P, ledger, started, weights, out, hcall, _, _, _, _, hrate, _, _, _, _⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 _ _
      (ReferencePostInvocationPrefixLocality.collectionInput_spec rate rewards C_star C_h q z)
  have hP : P = (collectionP z).1 := congrArg Sigma.fst (Option.some.inj
    (hcall.symm.trans (collectionArguments_spec rate rewards C_star C_h q z)))
  apply roundInput_ext
  · rfl
  · rfl
  · rfl
  · change (collectionInput rate rewards C_star C_h q z).rate = _
    rw [hrate, hP]
    rfl

/-- Collection retains the original entire reward row, including zero rewards. -/
theorem collectionRound_reward (z : CollectionSource) (i : Option (Fin p.K)) :
    (collectionRound z i).reward = fun j => ((rewards q j).val : ℝ) / (D p : ℝ) := by
  have hr := (collectionRecord_spec rate rewards C_star C_h q z).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hw, _⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 _ _
      (ReferencePostInvocationPrefixLocality.collectionInput_spec rate rewards C_star C_h q z)
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z.val _ hr
  exact hw.trans (by rw [hf.2.2.1, hf.2.2.2])

/-- The actual collection recorder uses exactly the common source-estimate
law, for every incoming old set (which is absent from this expression). -/
theorem collection_estimate_marginal (z : CollectionSource)
    (f : (Fin p.K → ℝ) → ℝ≥0∞) :
    (∑ i : Option (Fin p.K),
      f (RecordedRoundMoments.rawEstimate Q (collectionPre z) (collectionRound z i)) *
        ReferencePostInvocationCollectionNativeLaw.recorderPMF rate rewards C_star C_h q z i) =
      sourceEstimateTest rate (collectionP z).1.anchor (collectionP z).1.anchor_pos
        (collectionInput rate rewards C_star C_h q z).reward
        (fun j => ⟨(collectionInput rate rewards C_star C_h q z).reward_nonneg j,
          (collectionInput rate rewards C_star C_h q z).reward_le_one j⟩)
        (collectionPre z) (collectionInput rate rewards C_star C_h q z).enabled f := by
  simp only [sourceEstimateTest, collectionRound_eq_fixedRoundInput,
    ReferencePostInvocationCollectionNativeLaw.recorderPMF, anchorRates]

/-- The common estimate law on the ORIGINAL whole-control collection source.
The arbitrary incoming hidden set affects FAST but does not affect this law. -/
theorem collection_source_estimate_marginal (z : CollectionSource) (U : SlowSet p)
    (hen : (collectionInput rate rewards C_star C_h q z).enabled = true)
    (f : (Fin p.K → ℝ) → ℝ≥0∞) :
    (∫⁻ c, f (RecordedRoundMoments.rawEstimate Q (collectionPre z)
      (collectionRound z (ReferencePostInvocationCollectionNativeLaw.nativePair
        rate rewards C_star C_h q z U c).1)) ∂ContinuousLearningRows.timeControlLaw p) =
      sourceEstimateTest rate (collectionP z).1.anchor (collectionP z).1.anchor_pos
        (collectionInput rate rewards C_star C_h q z).reward
        (fun j => ⟨(collectionInput rate rewards C_star C_h q z).reward_nonneg j,
          (collectionInput rate rewards C_star C_h q z).reward_le_one j⟩)
        (collectionPre z) (collectionInput rate rewards C_star C_h q z).enabled f := by
  change (∫⁻ c, f (RecordedRoundMoments.rawEstimate Q (collectionPre z)
    (collectionRound z (ReferencePostInvocationCollectionNativeLaw.nativeRecorder
      rate rewards C_star C_h q z c))) ∂ContinuousLearningRows.timeControlLaw p) = _
  rw [← lintegral_map (measurable_of_countable
    (fun i => f (RecordedRoundMoments.rawEstimate Q (collectionPre z) (collectionRound z i))))
    (ReferencePostInvocationCollectionNativeLaw.measurable_nativeRecorder rate rewards C_star C_h q z),
    ReferencePostInvocationCollectionNativeLaw.nativeRecorder_map rate rewards C_star C_h q z hen,
    lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact collection_estimate_marginal rate rewards C_star C_h q z f

private def collectionPairMass (z : CollectionSource) (U : SlowSet p)
    (i : Option (Fin p.K)) (j : Fin p.K) : ℝ≥0∞ :=
  if hj : j ∈ CanonicalFastSampling.fastArmFinset U then
    ReferencePostInvocationCollectionNativeLaw.recorderPMF rate rewards C_star C_h q z i *
      ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate (collectionP z).1.anchor
        (RecordedQueueRun.scoreWeight Q (collectionPre z)) (collectionP z).1.anchor_pos
        (RecordedSlowRefresh.scoreWeight_pos Q _) U ⟨j, hj⟩
  else 0

private theorem collectionPairMass_sum (z : CollectionSource) (U : SlowSet p)
    (i : Option (Fin p.K)) :
    (∑ j : Fin p.K, collectionPairMass rate rewards C_star C_h q z U i j) =
      ReferencePostInvocationCollectionNativeLaw.recorderPMF rate rewards C_star C_h q z i := by
  unfold collectionPairMass
  let fast := ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate (collectionP z).1.anchor
    (RecordedQueueRun.scoreWeight Q (collectionPre z)) (collectionP z).1.anchor_pos
    (RecordedSlowRefresh.scoreWeight_pos Q _) U
  rw [← Finset.sum_attach_eq_sum_dite (CanonicalFastSampling.fastArmFinset U)
    (fun j => ReferencePostInvocationCollectionNativeLaw.recorderPMF rate rewards C_star C_h q z i * fast j),
    ← Finset.univ_eq_attach, ← Finset.mul_sum]
  have hs := (ReferencePostInvocationCollectionNativeLaw.collectionFastPMF rate (collectionP z).1.anchor
    (RecordedQueueRun.scoreWeight Q (collectionPre z)) (collectionP z).1.anchor_pos
    (RecordedSlowRefresh.scoreWeight_pos Q _) U).tsum_coe
  rw [tsum_fintype] at hs
  rw [hs, mul_one]

/-- Enabled clear-PRE collection kernel at the actual native source. The
original incoming set `U` is retained on no-proposal, and the existing
`auxiliaryMass` uses this marker's actual step and retained old anchor. -/
theorem collection_source_quantized_test
    (control0 : ContinuousLearningRows.TimeControl p) (z : CollectionSource)
    (U : SlowSet p) (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (hen : (collectionInput rate rewards C_star C_h q z).enabled = true)
    (hpre : (collectionPre z).overflow = false)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    (∫⁻ y, outcomeTest rate (collectionPre z) (collectionRound z) f absent
      (ReferencePostInvocationCollectionNativeLaw.sourceOutcome
        rate rewards C_star C_h control0 q z U a y)
      ∂ReferencePostInvocationCollectionNativeLaw.innovationLaw (p := p)) =
      ∑ i : Option (Fin p.K), ∑ B : Bool, ∑ V : SlowSet p,
        f (RecordedRoundMoments.rawEstimate Q (collectionPre z) (collectionRound z i)) B V *
          (ReferencePostInvocationCollectionNativeLaw.recorderPMF rate rewards C_star C_h q z i *
            ReferencePostInvocationCollectionNativeLaw.auxiliaryMass
              rate rewards C_star C_h q z U i B V) := by
  let mu := (ReferencePostInvocationCollectionNativeLaw.innovationLaw (p := p)).map
    (ReferencePostInvocationCollectionNativeLaw.sourceOutcome rate rewards C_star C_h control0 q z U a)
  rw [← lintegral_map (measurable_of_countable _)
    (ReferencePostInvocationCollectionNativeLaw.measurable_sourceOutcome
      rate rewards C_star C_h control0 q z U a)]
  change (∫⁻ o, Sum.elim (fun _ => absent)
    (fun x => f (RecordedRoundMoments.rawEstimate Q (collectionPre z) (collectionRound z x.1))
      x.2.2.1 x.2.2.2) o ∂mu) = _
  rw [outcome_lintegral mu
    (fun i B V => f (RecordedRoundMoments.rawEstimate Q (collectionPre z) (collectionRound z i)) B V) absent]
  have hunit : mu {Sum.inl ()} = 0 :=
    ReferencePostInvocationCollectionNativeLaw.sourceOutcome_clear_unit
      rate rewards C_star C_h control0 q z U a hen hpre
  rw [hunit, mul_zero, zero_add]
  have hatom (i : Option (Fin p.K)) (j : Fin p.K) (B : Bool) (V : SlowSet p) :
      mu {Sum.inr (i, j, B, V)} =
        collectionPairMass rate rewards C_star C_h q z U i j *
          ReferencePostInvocationCollectionNativeLaw.auxiliaryMass rate rewards C_star C_h q z U i B V := by
    rw [ReferencePostInvocationCollectionNativeLaw.sourceOutcome_mass]
    unfold ReferencePostInvocationCollectionNativeLaw.nativeMass collectionPairMass
    rw [hen, hpre]
    by_cases hj : j ∈ CanonicalFastSampling.fastArmFinset U <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, hj, dite_true, dite_false,
        ReferencePostInvocationCollectionNativeLaw.collectionFastPMF_apply, zero_mul]
  simp_rw [hatom]
  rw [sum_fast_eliminate]
  simp_rw [collectionPairMass_sum]

/-- Disabled collection has the prescribed absent effective cell. Its
continuation is not assigned an effective Bernoulli proposal. -/
theorem collection_disabled_quantized_test
    (control0 : ContinuousLearningRows.TimeControl p) (z : CollectionSource)
    (U : SlowSet p) (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (hen : (collectionInput rate rewards C_star C_h q z).enabled = false)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    (∫⁻ y, outcomeTest rate (collectionPre z) (collectionRound z) f absent
      (ReferencePostInvocationCollectionNativeLaw.sourceOutcome
        rate rewards C_star C_h control0 q z U a y)
      ∂ReferencePostInvocationCollectionNativeLaw.innovationLaw (p := p)) = absent := by
  rw [← lintegral_map (measurable_of_countable _)
    (ReferencePostInvocationCollectionNativeLaw.measurable_sourceOutcome
      rate rewards C_star C_h control0 q z U a),
    ReferencePostInvocationCollectionNativeLaw.sourceOutcome_disabled_law
      rate rewards C_star C_h control0 q z U a hen,
    lintegral_dirac' _ (measurable_of_countable _)]
  rfl

/-- Enabled PRE overflow preserves the original physical continuation and
freezes the effective tuple. Only the effective estimate is zeroed. -/
theorem collection_overflow_quantized_test
    (control0 : ContinuousLearningRows.TimeControl p) (z : CollectionSource)
    (U : SlowSet p) (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (hen : (collectionInput rate rewards C_star C_h q z).enabled = true)
    (hpre : (collectionPre z).overflow = true)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    (∫⁻ y, outcomeTest rate (collectionPre z) (collectionRound z) f absent
      (ReferencePostInvocationCollectionNativeLaw.sourceOutcome
        rate rewards C_star C_h control0 q z U a y)
      ∂ReferencePostInvocationCollectionNativeLaw.innovationLaw (p := p)) =
        f (fun _ => 0) false (frozenSlowSet p) := by
  rw [← lintegral_map (measurable_of_countable _)
    (ReferencePostInvocationCollectionNativeLaw.measurable_sourceOutcome
      rate rewards C_star C_h control0 q z U a),
    ReferencePostInvocationCollectionNativeLaw.sourceOutcome_overflow_law
      rate rewards C_star C_h control0 q z U a hen hpre,
    lintegral_dirac' _ (measurable_of_countable _)]
  change f (RecordedRoundMoments.rawEstimate Q (collectionPre z) (collectionRound z none)) false _ = _
  congr 1
  funext j
  exact RecordedRoundMoments.rawEstimate_eq_zero_after_overflow Q _ _ j hpre

attribute [-instance] slowSetMeasurableSpace slowSetDiscrete

/-- The original rounded reward row has the required closed-interval bounds. -/
theorem gridReward_mem (j : Fin p.K) :
    ((rewards q j).val : ℝ) / (D p : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply (div_le_one (Nat.cast_pos.mpr (D_pos p))).2
    exact_mod_cast Nat.le_of_lt_succ (rewards q j).isLt

/-- The existing fixed input, at the actual choice view's literal anchor and
the original entire reward row. This introduces no new numerical update. -/
def installationRound (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (i : Option (Fin p.K)) : RecordedQueueRun.RoundInput p.K :=
  RecordedRoundMoments.fixedRoundInput Q
    (anchorRates rate v.payload.anchor v.payload.anchor_pos)
    (fun j => ((rewards q j).val : ℝ) / (D p : ℝ))
    (gridReward_mem rewards q) true i

/-- The actual installation's raw all-arm arrivals, before any PRE gate,
are those of the SAME existing numerical input. -/
theorem installation_rawArrivals (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (i : Option (Fin p.K)) (j : Fin p.K) :
    ReferenceRankInstallationCommonUpdateJointLaw.rawArrivalsFromPair
      rate rewards q v (some i, some j) =
      some (RecordedQueueRun.quantizedArrival Q (installationRound rate rewards q v i)) := by
  apply congrArg some
  funext a
  change (if i = some a then Nat.floor ((D p : ℝ) * rate.eta.val *
    (((rewards q a).val : ℝ) / (D p : ℝ)) / v.payload.rate a) else 0) = _
  unfold RecordedQueueRun.quantizedArrival installationRound RecordedRoundMoments.fixedRoundInput
  by_cases hi : i = some a
  · simp only [hi, ite_true]
    congr 1
    rw [show ((Q).n : ℝ) = (D p : ℝ) * rate.eta.val by
      rw [(Q).n_eq_eta_mul_D]; exact mul_comm _ _]
    rfl
  · simp only [hi, ite_false]

/-- The common-update kernel's numerical output is the actual complete
enabled step, including service at bottom and its detecting POST overflow. -/
theorem installation_updateFromPair
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (S : RecordedQueueRun.RunState p.K) (i : Option (Fin p.K)) (j : Fin p.K) :
    ReferenceRankInstallationCommonUpdateJointLaw.updateFromPair rate rewards q v
      (some (S.registers, S.overflow, S.records)) (some i, some j) =
      some (ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields rate
        (S.registers, S.overflow, S.records)
        (RecordedQueueRun.quantizedArrival Q (installationRound rate rewards q v i))) := by
  unfold ReferenceRankInstallationCommonUpdateJointLaw.updateFromPair
  rw [installation_rawArrivals]
  rfl

/-- Normalized accepted arrivals read literally from the full native UPDATE. -/
def updateEstimate (u : ReferenceFirstLivePostUpdateProposalLaw.NumericalUpdateFields p)
    (a : Fin p.K) : ℝ :=
  (RecordedQueueRun.acceptedArrival (u.accepted a) : ℝ) / ((Q).n : ℝ)

theorem installation_updateEstimate
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (S : RecordedQueueRun.RunState p.K) (i : Option (Fin p.K)) :
    updateEstimate rate (ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields rate
      (S.registers, S.overflow, S.records)
      (RecordedQueueRun.quantizedArrival Q (installationRound rate rewards q v i))) =
      RecordedRoundMoments.rawEstimate Q S (installationRound rate rewards q v i) := by
  rw [ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields_eq_step rate S _ rfl]
  rfl

/-- Literal residual/retention expression used in the installation projection.
The following theorem identifies it with the accepted actual-cell law. -/
def installationNextLaw (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (S : RecordedQueueRun.RunState p.K) (i : Option (Fin p.K)) (B : Bool) :
    Measure (SlowSet p) :=
  if S.overflow then Measure.dirac (frozenSlowSet p) else if B then
    (RecordedSlowRefresh.residualPMF p Q S (installationRound rate rewards q v i)
      v.payload.anchor v.payload.anchor_pos).toMeasure
  else Measure.dirac v.payload.slowSet

/-- The accepted actual source cell has this exact canonical input. The
record's source identity is used to identify its time and entire reward table. -/
theorem actualSourceCell_input
    (source : BootstrapPrivateRoundStreams.SourceInput p) (r : Record rate)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h q source = some r) :
    cell.input = installationRound rate rewards q cell.selected.view cell.input.recordedArm := by
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q source r hr
  apply roundInput_ext
  · exact cell.enabled
  · rfl
  · rw [cell.input_eq]
    change (fun j => ((r.input.rewards r.input.time j).val : ℝ) / (D p : ℝ)) = _
    rw [hf.2.2.1, hf.2.2.2]
    rfl
  · rw [cell.input_eq]
    rfl

/-- This is the SAME actual fixed-anchor residual law, including PRE-overflow
and retention of the actual old set. No refresh-kernel equality is deferred. -/
theorem actualSourceCell_nextLaw
    (source : BootstrapPrivateRoundStreams.SourceInput p) (r : Record rate)
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h q source = some r)
    (S : RecordedQueueRun.RunState p.K) :
    ReferenceFirstLiveCalendarMarkedTransition.logicalCellResidualLaw rate r cell S =
      installationNextLaw rate rewards q cell.selected.view S cell.input.recordedArm
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time) := by
  unfold ReferenceFirstLiveCalendarMarkedTransition.logicalCellResidualLaw installationNextLaw
  rw [← actualSourceCell_input rate rewards C_star C_h q source r cell hr]

/-- Test the estimate read from the actual common UPDATE and its actual
marker-specific next-set law. Outer absence remains separately tagged. -/
def commonUpdateTest (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (S : RecordedQueueRun.RunState p.K)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞)
    (y : ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p × Bool) : ℝ≥0∞ :=
  match y.1.1.1, y.1.2 with
  | some i, some u => ∫⁻ V, f (updateEstimate rate u) (!S.overflow && y.2) V
      ∂installationNextLaw rate rewards q v S i y.2
  | _, _ => absent

/-- Explicit recorder/proposal sum for the common ROOT/CALL projection.
`installationNextLaw` is identified with the actual residual above. -/
def installationTestSum (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (S : RecordedQueueRun.RunState p.K)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i : Option (Fin p.K), ∑ B : Bool,
    (∫⁻ V, f (RecordedRoundMoments.rawEstimate Q S (installationRound rate rewards q v i))
      (!S.overflow && B) V ∂installationNextLaw rate rewards q v S i B) *
      (RecordedRoundMoments.recordingOutcomePMF
        (anchorRates rate v.payload.anchor v.payload.anchor_pos) i *
        ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B})

/-- Project the accepted ROOT/CALL common-update/proposal kernel. The only
local parameters are a valid actual choice view and a concrete PRE. FAST is
summed through its proved recorder marginal, with no old-set distribution. -/
theorem installation_quantized_test
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff q v.complementWeights)
    (S : RecordedQueueRun.RunState p.K)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    (∫⁻ y, commonUpdateTest rate rewards q v S f absent y
      ∂(ReferenceRankInstallationCommonUpdateJointLaw.commonUpdateKernel rate rewards q v valid
        (some (S.registers, S.overflow, S.records))).prod
          (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate)) =
      installationTestSum rate rewards q v S f := by
  unfold installationTestSum
  let g : Option (Fin p.K) → ℝ≥0∞ := fun i =>
    ∫⁻ B, (∫⁻ V, f (RecordedRoundMoments.rawEstimate Q S (installationRound rate rewards q v i))
      (!S.overflow && B) V ∂installationNextLaw rate rewards q v S i B)
      ∂ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate
  rw [lintegral_prod _ (measurable_of_countable
    (commonUpdateTest rate rewards q v S f absent)).aemeasurable]
  unfold ReferenceRankInstallationCommonUpdateJointLaw.commonUpdateKernel
  rw [lintegral_map (measurable_of_countable _)
    (ReferenceRankInstallationCommonUpdateJointLaw.measurable_commonUpdateKernelMap rate rewards q v _)]
  unfold ReferenceRankInstallationSourceKernelComposition.installationRecorderFastOutputKernel
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  have hread (x : Option (Fin p.K) × Fin p.K) :
      (∫⁻ B, commonUpdateTest rate rewards q v S f absent
        ((ReferenceRankInstallationSourceKernelComposition.optionalRecorderFastLift x,
          ReferenceRankInstallationCommonUpdateJointLaw.updateFromPair rate rewards q v
            (some (S.registers, S.overflow, S.records))
            (ReferenceRankInstallationSourceKernelComposition.optionalRecorderFastLift x)), B)
        ∂ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate) = g x.1 := by
    apply lintegral_congr
    intro B
    simp only [ReferenceRankInstallationSourceKernelComposition.optionalRecorderFastLift,
      installation_updateFromPair, commonUpdateTest, installation_updateEstimate]
  simp_rw [hread]
  rw [← lintegral_map (measurable_of_countable g) measurable_fst,
    (ReferenceRankInstallationSourceKernelComposition.installationRecorderFastRawKernel_marginals
      rate q v valid).1, lintegral_fintype]
  apply Finset.sum_congr rfl
  intro i _hi
  dsimp only [g]
  rw [lintegral_fintype, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro B _hB
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  ac_rfl

/-- The physical proposal factor has the source Bernoulli masses, including
the no-proposal coefficient. Effective stopping is separately PRE-gated. -/
theorem proposalBitLaw_mass (B : Bool) :
    ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B} =
      if B then ENNReal.ofReal (4 * (p.m : ℝ) * rate.eta.val)
      else ENNReal.ofReal (1 - 4 * (p.m : ℝ) * rate.eta.val) := by
  cases B
  · have he : ({false} : Set Bool) = {true}ᶜ := by
      ext B
      cases B <;> simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Bool.false_eq_true,
        Bool.true_eq_false, not_false_eq_true, not_true_eq_false]
    rw [he, prob_compl_eq_one_sub (measurableSet_singleton true),
      ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw_true,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _
        (ReferenceFirstLivePostUpdateProposalLaw.physicalProposalThreshold_bounds rate).1.le]
    rfl
  · exact ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw_true rate

/-- Estimate marginal read directly from the accepted common UPDATE. It is
the common source law and has no old-set or FAST input beyond the fixed anchor. -/
theorem installation_estimate_marginal
    (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff q v.complementWeights)
    (S : RecordedQueueRun.RunState p.K)
    (f : (Fin p.K → ℝ) → ℝ≥0∞) (absent : ℝ≥0∞) :
    (∫⁻ y, (match y.2 with | none => absent | some u => f (updateEstimate rate u))
      ∂ReferenceRankInstallationCommonUpdateJointLaw.commonUpdateKernel rate rewards q v valid
        (some (S.registers, S.overflow, S.records))) =
      sourceEstimateTest rate v.payload.anchor v.payload.anchor_pos
        (fun j => ((rewards q j).val : ℝ) / (D p : ℝ)) (gridReward_mem rewards q) S true f := by
  unfold ReferenceRankInstallationCommonUpdateJointLaw.commonUpdateKernel
  rw [lintegral_map (measurable_of_countable _)
    (ReferenceRankInstallationCommonUpdateJointLaw.measurable_commonUpdateKernelMap rate rewards q v _)]
  unfold ReferenceRankInstallationSourceKernelComposition.installationRecorderFastOutputKernel
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp only [ReferenceRankInstallationSourceKernelComposition.optionalRecorderFastLift,
    installation_updateFromPair, installation_updateEstimate]
  rw [← lintegral_map (measurable_of_countable
    (fun i => f (RecordedRoundMoments.rawEstimate Q S (installationRound rate rewards q v i))))
    measurable_fst,
    (ReferenceRankInstallationSourceKernelComposition.installationRecorderFastRawKernel_marginals
      rate q v valid).1, lintegral_fintype]
  simp only [sourceEstimateTest, installationRound, anchorRates,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

private theorem actualMarker_of_liveReadout
    (source : BootstrapPrivateRoundStreams.SourceInput p) (r : Record rate)
    (c : RecordedQueueRun.RoundInput p.K)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q source = some r)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c) :
    ReferenceRankInstallationRecorderFoundation.actualMarker rate rewards C_star C_h q source =
      some c.recordedArm := by
  simp only [ReferenceRankInstallationRecorderFoundation.actualMarker, hr, Option.bind_some,
    ReferenceFirstCollectionCurrentRetainedGate.cell0, hc, Option.some_or, Option.map_some]

/-- On every actual native invocation, the common-kernel test reads exactly
the estimate and proposal of that source's whole UPDATE and integrates its
accepted actual residual. This also includes incoming and detecting overflow. -/
theorem native_quantized_readout (control0 : ContinuousLearningRows.TimeControl p)
    (z : ReferenceGeneratedInvocationCallSplice.InvocationSource rate rewards C_star C_h q)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    let r := ReferenceGeneratedInvocationCallSplice.nativeRecord rate rewards C_star C_h q z
    let cell := ReferenceGeneratedInvocationCallSplice.nativeSourceCell rate rewards C_star C_h q z
    let S := ReferenceGeneratedInvocationCallSplice.nativeBefore rate rewards C_star C_h control0 q z
    let B := ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
      (ReferenceSourceCurrentControlFreshness.u_t p q z.val)
    commonUpdateTest rate rewards q cell.selected.view S f absent
      ((ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h q z.val,
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
          rate rewards C_star C_h control0 q z.val), B) =
      ∫⁻ V, f (RecordedRoundMoments.rawEstimate Q S cell.input) (!S.overflow && B) V
        ∂ReferenceFirstLiveCalendarMarkedTransition.logicalCellResidualLaw rate r cell S := by
  dsimp only
  let r := ReferenceGeneratedInvocationCallSplice.nativeRecord rate rewards C_star C_h q z
  let cell := ReferenceGeneratedInvocationCallSplice.nativeSourceCell rate rewards C_star C_h q z
  have hs := ReferenceGeneratedInvocationCallSplice.nativeSourceCell_spec rate rewards C_star C_h q z
  have hm := actualMarker_of_liveReadout rate rewards C_star C_h q z.val r cell.input hs.1 hs.2.2
  have hB : FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time =
      ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
        (ReferenceSourceCurrentControlFreshness.u_t p q z.val) := by
    rw [ReferenceFirstLivePostUpdateProposalLaw.completeRowProposalBit_eq_physicalProposalBit rate _ _ _ rfl,
      ReferenceGeneratedInvocationCallSplice.nativeRecord_control]
  rw [ReferenceGeneratedInvocationCallSplice.nativeCell_wholeUpdate rate rewards C_star C_h control0 q z
    ReferenceFirstLiveActualRefreshTestLaw.scalarZero]
  unfold commonUpdateTest ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast
  rw [hm]
  change (∫⁻ V, f (RecordedRoundMoments.rawEstimate Q _ cell.input) _ V
    ∂installationNextLaw rate rewards q cell.selected.view _ cell.input.recordedArm _) = _
  rw [actualSourceCell_nextLaw rate rewards C_star C_h q z.val r cell hs.1, hB]

section Root

open ReferenceFirstNextInstallationCellFactors ReferenceFirstNextInstallationTransitionLaw

variable (control0 : ContinuousLearningRows.TimeControl p)

local notation "RootSource" => FirstInvocationSource rate rewards C_star C_h q
local notation "rootCell" => firstSourceCell rate rewards C_star C_h q
local notation "rootPre" => firstBefore rate rewards C_star C_h control0 q

/-- The accepted ROOT law, with its actual strict PRE, satisfies the common
quantized joint-kernel formula. Initialization is not redrawn here. -/
theorem root_quantized_test (z : RootSource)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    (∫⁻ y, commonUpdateTest rate rewards q (rootCell z).selected.view (rootPre z) f absent y
      ∂ReferenceGeneratedCalendarRootRoundLaw.rootControlLaw rate rewards C_star C_h control0 q z) =
      installationTestSum rate rewards q (rootCell z).selected.view (rootPre z) f := by
  unfold ReferenceGeneratedCalendarRootRoundLaw.rootControlLaw
  rw [firstBefore_spec]
  exact installation_quantized_test rate rewards q _ _ _ f absent

/-- ROOT projection on the original complete current-control law, through
the accepted root draw. The initializer and UPDATE coordinates stay distinct. -/
theorem root_source_quantized_test (z : RootSource)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    (∫⁻ c, commonUpdateTest rate rewards q (rootCell z).selected.view (rootPre z) f absent
      (ReferenceGeneratedCalendarRootRoundLaw.rootControlDraw rate rewards C_star C_h control0 q z c)
      ∂ContinuousLearningRows.timeControlLaw p) =
      installationTestSum rate rewards q (rootCell z).selected.view (rootPre z) f := by
  rw [← lintegral_map (measurable_of_countable _)
    (ReferenceGeneratedCalendarRootRoundLaw.measurable_rootControlDraw rate rewards C_star C_h control0 q z),
    ReferenceGeneratedCalendarRootRoundLaw.rootControlDraw_law]
  exact root_quantized_test rate rewards C_star C_h q control0 z f absent

/-- At the actual root source, the local next-set factor is precisely the
accepted residual law, including retained old set and incoming overflow. -/
theorem root_actual_nextLaw (z : RootSource) :
    firstResidualLaw rate rewards C_star C_h control0 q z =
      installationNextLaw rate rewards q (rootCell z).selected.view (rootPre z)
        (rootCell z).input.recordedArm
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (firstRecord rate rewards C_star C_h q z).input.row
          (firstRecord rate rewards C_star C_h q z).input.time) := by
  exact actualSourceCell_nextLaw rate rewards C_star C_h q z.val _ _
    (firstSourceCell_spec rate rewards C_star C_h q z).1 _

/-- The root's actual pair/whole UPDATE/proposal readout gives its accepted
quantized-estimate/residual test on the SAME original source. -/
theorem root_quantized_readout (z : RootSource)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    let B := ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
      (ReferenceSourceCurrentControlFreshness.u_t p q z.val)
    commonUpdateTest rate rewards q (rootCell z).selected.view (rootPre z) f absent
      ((ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h q z.val,
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalUpdate
          rate rewards C_star C_h control0 q z.val), B) =
      ∫⁻ V, f (RecordedRoundMoments.rawEstimate Q (rootPre z) (rootCell z).input)
        (!(rootPre z).overflow && B) V ∂firstResidualLaw rate rewards C_star C_h control0 q z := by
  dsimp only
  have hs := firstSourceCell_spec rate rewards C_star C_h q z
  have hm := actualMarker_of_liveReadout rate rewards C_star C_h q z.val
    (firstRecord rate rewards C_star C_h q z) (rootCell z).input hs.1 hs.2.2
  have hB : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (firstRecord rate rewards C_star C_h q z).input.row
      (firstRecord rate rewards C_star C_h q z).input.time =
      ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
        (ReferenceSourceCurrentControlFreshness.u_t p q z.val) := by
    rw [ReferenceFirstLivePostUpdateProposalLaw.completeRowProposalBit_eq_physicalProposalBit rate _ _ _ rfl,
      firstRecord_control]
  rw [actualFirstCell_wholeUpdate rate rewards C_star C_h control0 q z
    ReferenceFirstLiveActualRefreshTestLaw.scalarZero]
  unfold commonUpdateTest ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast
  rw [hm]
  change (∫⁻ V, f (RecordedRoundMoments.rawEstimate Q (rootPre z) (rootCell z).input) _ V
    ∂installationNextLaw rate rewards q (rootCell z).selected.view (rootPre z) (rootCell z).input.recordedArm _) = _
  rw [root_actual_nextLaw rate rewards C_star C_h q control0 z, hB]

end Root

section Call

open ReferenceGeneratedRankCalendarFoundation ReferenceGeneratedCalendarRoundInnovation
open ReferenceGeneratedInvocationCallSplice ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarNoncallRoundLaw

variable (control0 : ContinuousLearningRows.TimeControl p) (b0 : Bool) (u0 t0 : Fin p.T)
  (k : ℕ) (hk : t0.val + 1 + k < p.T)

local notation "date" => (Fin.mk (t0.val + 1 + k) hk)
local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0 k
local notation "invoke" => calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk
local notation "flag" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega)

/-- The existing generated CALL kernel has the same recorder/proposal sum
at its actual source, actual PRE, installed view and frozen episode anchor. -/
theorem calendarCall_quantized_test (w : Sample)
    (av : AssignmentParameterFibreKernel.AssignmentVector p) (hc : flag w = true)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    let z := invoke w av hc
    let v := (nativeSourceCell rate rewards C_star C_h date z).selected.view
    let S := nativeBefore rate rewards C_star C_h control0 date z
    (∫⁻ y, commonUpdateTest rate rewards date v S f absent y
      ∂ReferenceGeneratedCalendarRoundLaw.calendarCallControlLaw
        rate rewards C_star C_h control0 b0 u0 t0 k hk w av hc) =
      installationTestSum rate rewards date v S f := by
  dsimp only
  exact installation_quantized_test rate rewards date _ _ _ f absent

/-- The actual generated refresh uses this marker's actual native input and
PRE. This equality retains the physical current proposal and the old set. -/
theorem calendarCall_actual_nextLaw (w : Sample)
    (av : AssignmentParameterFibreKernel.AssignmentVector p) (hc : flag w = true)
    (c : ContinuousLearningRows.TimeControl p) :
    let z := ReferenceGeneratedCalendarRoundLaw.calendarCallSourceAt
      rate rewards C_star C_h control0 b0 u0 t0 k hk w av hc c
    let r := nativeRecord rate rewards C_star C_h date z
    let cell := nativeSourceCell rate rewards C_star C_h date z
    ReferenceGeneratedCalendarRoundLaw.calendarCallRefreshLaw
      rate rewards C_star C_h control0 b0 u0 t0 k hk w av hc c =
      installationNextLaw rate rewards date cell.selected.view
        (nativeBefore rate rewards C_star C_h control0 date z) cell.input.recordedArm
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time) := by
  dsimp only
  exact actualSourceCell_nextLaw rate rewards C_star C_h date _ _ _
    (nativeSourceCell_spec rate rewards C_star C_h date _).1 _

private theorem call_history (w : Sample)
    (av : AssignmentParameterFibreKernel.AssignmentVector p) (hc : flag w = true) :
    ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0
      (nativeRank rate rewards C_star C_h date (invoke w av hc).val) date (invoke w av hc).val =
      ReferenceRankInstallationRecorderFoundation.prefixVectorHistory rate rewards C_star C_h control0 date
        ((calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1, av) := by
  rw [ReferenceRankInstallationRecorderFoundation.history_eq_prefixVectorHistory_of_installation
    rate rewards C_star C_h control0 _ _ _ (native_installation rate rewards C_star C_h _ _)]
  congr 1
  apply Prod.ext
  · exact ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 date _ le_rfl _ _
  · exact ReferenceFirstCollectionRenewalVectorInsertion.av_insert _ _ av

/-- Replacing the actual current control preserves the installed view and
numerical PRE of this call. Neither equality is a consumer hypothesis. -/
theorem calendarCall_fixed_parameters (w : Sample)
    (av : AssignmentParameterFibreKernel.AssignmentVector p) (hc : flag w = true)
    (c : ContinuousLearningRows.TimeControl p) :
    let z := invoke w av hc
    let zc := ReferenceGeneratedCalendarRoundLaw.calendarCallSourceAt
      rate rewards C_star C_h control0 b0 u0 t0 k hk w av hc c
    (nativeSourceCell rate rewards C_star C_h date zc).selected.view =
        (nativeSourceCell rate rewards C_star C_h date z).selected.view ∧
      nativeBefore rate rewards C_star C_h control0 date zc =
        nativeBefore rate rewards C_star C_h control0 date z := by
  dsimp only
  let z := invoke w av hc
  let zc := ReferenceGeneratedCalendarRoundLaw.calendarCallSourceAt
    rate rewards C_star C_h control0 b0 u0 t0 k hk w av hc c
  let wc := calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 date
    (noncallDate_after t0 k) k (w, c)
  have hcc : flag wc = true := (calendarCallFlag_replaceControl
    rate rewards C_star C_h control0 b0 u0 t0 date (noncallDate_after t0 k) k hk le_rfl w c).trans hc
  have hH := call_history rate rewards C_star C_h control0 b0 u0 t0 k hk wc av hcc
  rw [calendarRoundPast_replaceControl rate rewards C_star C_h control0 b0 u0 t0 date
    (noncallDate_after t0 k) k hk.le le_rfl] at hH
  have hH0 := call_history rate rewards C_star C_h control0 b0 u0 t0 k hk w av hc
  have hhist : ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0
      (nativeRank rate rewards C_star C_h date zc.val) date zc.val =
      ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h control0
        (nativeRank rate rewards C_star C_h date z.val) date z.val := hH.trans hH0.symm
  have hp : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (date).val zc.val =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (date).val z.val := congrArg Prod.fst hhist
  constructor
  · apply Option.some.inj
    rw [← nativeCell_view rate rewards C_star C_h control0 date zc,
      ← nativeCell_view rate rewards C_star C_h control0 date z,
      ReferenceRankInstallationRecorderFoundation.actualInstallationView_eq_history
        rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h date zc.val) date zc.val,
      ReferenceRankInstallationRecorderFoundation.actualInstallationView_eq_history
        rate rewards C_star C_h control0 (nativeRank rate rewards C_star C_h date z.val) date z.val,
      hhist]
  · have hbefore : ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
        rate rewards C_star C_h control0 date zc.val =
        ReferenceRankInstallationPostUpdateProposalLaw.actualInstallationNumericalBefore
          rate rewards C_star C_h control0 date z.val := by
      change ReferenceFirstCollectionCurrentRetainedGate.prefixReadout? rate rewards C_star C_h date
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (date).val zc.val) = _
      rw [hp]
      rfl
    have he := Option.some.inj ((nativeBefore_spec rate rewards C_star C_h control0 date zc).symm.trans
      (hbefore.trans (nativeBefore_spec rate rewards C_star C_h control0 date z)))
    exact congrArg (fun s : ReferenceRankInstallationPostUpdateProposalLaw.NumericalState p =>
      (⟨s.1, s.2.1, s.2.2⟩ : RecordedQueueRun.RunState p.K)) he

/-- On each positive physical control fibre, the projected kernel uses the
same actual source estimate, effective proposal and actual refresh law.
The unconditional finite kernel formula retains all zero coefficients. -/
theorem calendarCall_quantized_fibre_readout (w : Sample)
    (av : AssignmentParameterFibreKernel.AssignmentVector p) (hc : flag w = true)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞)
    (y : ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p × Bool)
    (hy : ReferenceGeneratedCalendarRoundLaw.calendarCallControlLaw
      rate rewards C_star C_h control0 b0 u0 t0 k hk w av hc {y} ≠ 0) :
    let z := invoke w av hc
    ∀ᵐ c ∂ReferenceGeneratedCalendarRoundLaw.calendarCallControlFibre
      rate rewards C_star C_h control0 b0 u0 t0 k hk w av hc y,
      let zc := ReferenceGeneratedCalendarRoundLaw.calendarCallSourceAt
        rate rewards C_star C_h control0 b0 u0 t0 k hk w av hc c
      let S := nativeBefore rate rewards C_star C_h control0 date zc
      let cell := nativeSourceCell rate rewards C_star C_h date zc
      commonUpdateTest rate rewards date (nativeSourceCell rate rewards C_star C_h date z).selected.view
          (nativeBefore rate rewards C_star C_h control0 date z) f absent y =
        ∫⁻ V, f (RecordedRoundMoments.rawEstimate Q S cell.input)
          (!S.overflow && ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
            (ReferenceSourceCurrentControlFreshness.u_t p date zc.val)) V
          ∂ReferenceGeneratedCalendarRoundLaw.calendarCallRefreshLaw
            rate rewards C_star C_h control0 b0 u0 t0 k hk w av hc c := by
  dsimp only
  filter_upwards [ReferenceGeneratedCalendarRoundLaw.calendarCallControlFibre_support
    rate rewards C_star C_h control0 b0 u0 t0 k hk w av hc y hy] with c hc'
  rw [← hc', ReferenceGeneratedCalendarRoundLaw.calendarCallControlDraw_readout]
  obtain ⟨hv, hS⟩ := calendarCall_fixed_parameters rate rewards C_star C_h control0 b0 u0 t0 k hk w av hc c
  rw [← hv, ← hS]
  exact native_quantized_readout rate rewards C_star C_h date control0 _ f absent

end Call

/-- Quantized observer of the existing optional noncall numerical UPDATE.
The update still contains the entire PRE/POST, accepted arrivals and service;
the original physical recorder is retained separately by `calendarNoncallRawMass`. -/
def noncallUpdateTest
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞)
    (x : Option (ReferenceGeneratedCalendarNoncallRoundLaw.NumericalUpdate p) ×
      ReferencePostInvocationCollectionNativeLaw.Outcome p) : ℝ≥0∞ :=
  match x with
  | (some u, .inr (_, _, B, V)) =>
      f (fun j => (RecordedQueueRun.acceptedArrival (u.2.2.1 j) : ℝ) / ((Q).n : ℝ)) B V
  | _ => absent

/-- This observer is precisely the existing rawEstimate of the actual step.
This is a local readout equality, without any estimate-to-marker inversion. -/
theorem noncallUpdateTest_numericalUpdate
    (S : RecordedQueueRun.RunState p.K) (c : RecordedQueueRun.RoundInput p.K)
    (i : Option (Fin p.K)) (j : Fin p.K) (B : Bool) (V : SlowSet p)
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    noncallUpdateTest rate f absent
      (some (ReferenceGeneratedCalendarNoncallRoundLaw.numericalUpdate rate S c),
        .inr (i, j, B, V)) = f (RecordedRoundMoments.rawEstimate Q S c) B V := rfl

section Noncall

attribute [local instance] slowSetMeasurableSpace slowSetDiscrete

open ReferenceGeneratedRankCalendarFoundation ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarRoundInnovation ReferenceGeneratedCalendarNoncallRoundLaw

variable (control0 : ContinuousLearningRows.TimeControl p) (b0 : Bool) (u0 t0 : Fin p.T)
  (k : ℕ) (hk : t0.val + 1 + k < p.T)

local notation "date" => (Fin.mk (t0.val + 1 + k) hk)
local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0 k
local notation "flag" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega)
local notation "update" => calendarNoncallUpdate rate rewards C_star C_h control0 b0 u0 t0 k hk
local notation "outcome" => calendarNoncallOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk
local notation "updateFor" => calendarNoncallUpdateForOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk
local notation "rawMass" => calendarNoncallRawMass rate rewards C_star C_h control0 b0 u0 t0 k hk

/-- Specialization of the accepted SAME-source numerical noncall law. Raw
recorder atoms are summed even when the effective outcome freezes. The
enabled/disabled/PRE-overflow branches are those of the existing raw mass. -/
theorem calendarNoncall_quantized_test
    (f : (Fin p.K → ℝ) → Bool → SlowSet p → ℝ≥0∞) (absent : ℝ≥0∞) :
    (∫⁻ wv : Sample × AssignmentParameterFibreKernel.AssignmentVector p,
      if flag wv.1 = false then noncallUpdateTest rate f absent (update wv.1, outcome wv.1) else 0
      ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)) =
      ∫⁻ w, if flag w = false then
        ∑ i : Option (Fin p.K), ∑ o : ReferencePostInvocationCollectionNativeLaw.Outcome p,
          noncallUpdateTest rate f absent (updateFor w o, o) * rawMass w i o else 0
        ∂(calendarLaw rate rewards C_star C_h control0 b0 u0 t0 k hk.le).map
          (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 date
            (noncallDate_after t0 k) k) := by
  let F : (BootstrapPrivateRoundStreams.SourceInput p ×
      (SlowSet p × List (LogicalCell p rate))) ×
      (Option (ReferenceFirstLiveOverflowReadout.NumericalCellReadout p) ×
        (Option (NumericalUpdate p) × ReferencePostInvocationCollectionNativeLaw.Outcome p)) → ℝ≥0∞ :=
    fun x => noncallUpdateTest rate f absent x.2.2
  have hF : Measurable F := (measurable_of_countable (noncallUpdateTest rate f absent)).comp
    measurable_snd.snd
  exact calendarLaw_noncall_numerical_test rate rewards C_star C_h control0 b0 u0 t0 k hk F hF

end Noncall

end Bandits.Support.ReferenceGeneratedCalendarQuantizedRoundKernel
