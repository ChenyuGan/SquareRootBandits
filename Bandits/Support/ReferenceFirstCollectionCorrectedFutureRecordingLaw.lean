/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedFutureRecordingView

/-!
# Original-source strict-future corrected recording law

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-290`,
`05_binary_transport.tex:354-431`, and `06_interruptions.tex:355-426`.

The optional observation is on the original corrected first-call cell E(u,t).
Its strict-future gate retains the first cutoff update. Outside that gate the
observation is absent, which differs from a present bottom marker. The whole
current continuous control is integrated with its original independent law.

These are internal recording identities, with unrestricted constants and the
whole reward table. Retained moments and overflow estimates are later consumers.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ContinuousLearningRows (TimeControl)
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
  (sourcePrefix sourcePrefixFiltration)
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCorrectedFutureRecordingLaw

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p

/-- The existing scalar coefficient evaluated at the actual optional parameters. -/
def futureCoefficient (u t q : Fin p.T) (o : Option (Option (Fin p.K))) (x : X) : ℝ :=
  ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o (ReferenceFirstCollectionCorrectedFutureRecordingView.futureParameters rate rewards C_star C_h u t q x)

/-- Real indicator of the actual optional marker on the original source. -/
def futureTest (u t q : Fin p.T) (o : Option (Option (Fin p.K))) (x : X) : ℝ :=
  if ReferenceFirstCollectionCorrectedFutureRecordingView.futureMarker rate rewards C_star C_h u t q x = o then 1 else 0

private theorem recording_control_mass
    (regime : SnapshotRecordingKernel.Regime p) (enabled : Bool)
    (anchor weights : Fin p.K → ℝ) (ha : ∀ j, 0 < anchor j)
    (hw : ∀ j, 0 < weights j) (hal : ∀ j, anchor j ≤ weights j)
    (hau : ∀ j, weights j ≤ 2 * anchor j) (o : Option (Option (Fin p.K))) :
    (ContinuousLearningRows.timeControlLaw p)
      {c | some (SnapshotRecordingKernel.recordingMap p regime enabled
        rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau c.1) = o} =
      ENNReal.ofReal (ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
        (some (enabled, CanonicalRecordingRates.xi p rate.eta.val anchor))) := by
  let f := SnapshotRecordingKernel.recordingMap p regime enabled
    rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau
  have hf : Measurable f := SnapshotRecordingKernel.measurable_recordingMap
    p regime rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau enabled
  have hm (a : Option (Fin p.K)) :
      (ContinuousLearningRows.timeControlLaw p) {c | f c.1 = a} =
      (ContinuousControlSlice.sliceLaw p.m p.K) {x | f x = a} := by
    rw [← ContinuousLearningRows.map_slice p,
      Measure.map_apply measurable_fst
        (show MeasurableSet {x | f x = a} from (measurableSet_singleton a).preimage hf)]
    rfl
  cases o with
  | none => simp only [reduceCtorEq, Set.ofPred_false, measure_empty,
      ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters,
      ENNReal.ofReal_zero]
  | some a =>
    simp only [Option.some.injEq]
    rw [show {c : TimeControl p | _ = a} = {c | f c.1 = a} from rfl, hm]
    cases enabled with
    | false =>
        cases a <;> simp only [f, SnapshotRecordingKernel.recordingMap_disabled,
          ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters,
          Set.ofPred_true, measure_univ, ENNReal.ofReal_one,
          reduceCtorEq, Set.ofPred_false, measure_empty, ENNReal.ofReal_zero]
    | true =>
        have hmap := SnapshotRecordingKernel.map_recordingMap
          p regime rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau
        have hsingle := congrArg (fun μ : Measure (Option (Fin p.K)) => μ {a}) hmap
        rw [Measure.map_apply hf (measurableSet_singleton a),
          PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a)] at hsingle
        cases a with
        | none => simpa only [Set.preimage, Set.mem_singleton_iff,
            RecordedRoundMoments.recordingOutcomePMF_none,
            SnapshotRecordingKernel.recordingRates,
            ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters] using hsingle
        | some j => simpa only [Set.preimage, Set.mem_singleton_iff,
            RecordedRoundMoments.recordingOutcomePMF_some,
            SnapshotRecordingKernel.recordingRates,
            ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters] using hsingle

/-- Every original source point has the exact whole-control optional atom mass.
No survival, positive event mass, or supplied validity premise is required. -/
theorem futureMarker_control_mass (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (x : X) (o : Option (Option (Fin p.K))) :
    (ContinuousLearningRows.timeControlLaw p)
      {control | ReferenceFirstCollectionCorrectedFutureRecordingView.futureMarker rate rewards C_star C_h u t q
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q x control) = o} =
      ENNReal.ofReal (futureCoefficient rate rewards C_star C_h u t q o x) := by
  have hk := ReferenceFirstCollectionCorrectedFutureRecordingView.corrected_future_marker_section
    rate rewards C_star C_h control0 u t q hfuture x
  have hp := (ReferenceFirstCollectionCorrectedFutureRecordingView.corrected_future_recordingView_presence
    rate rewards C_star C_h u t q hfuture x).2.2
  unfold futureCoefficient
  rw [hp]
  cases hv : ReferenceFirstCollectionCorrectedFutureRecordingView.futureRecordingView rate rewards C_star C_h u t q x with
  | none =>
    rw [hv] at hk
    simp only [Option.bind_none, hk]
    rcases o with _ | (_ | j) <;> simp only [ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters,
      Set.ofPred_true, measure_univ, ENNReal.ofReal_one, reduceCtorEq,
      Set.ofPred_false, measure_empty, ENNReal.ofReal_zero]
  | some v =>
    rcases v with ⟨parameters, view, code⟩
    rw [hv] at hk
    obtain ⟨enabled, snapshot, valid, hparameters, _hcode, hm⟩ := hk
    have hcanonical : view.payload.rate =
        CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor :=
      funext view.payload.rate_eq_canonical
    simp only [Option.bind_some, hm, hparameters, hcanonical]
    exact recording_control_mass rate _ enabled _ _ view.payload.anchor_pos
      (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid) o

/-- Actual present parameters are canonical rates, including disabled cells. -/
theorem futureParameters_bounds (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (x : X) (enabled : Bool) (xi : Fin p.K → ℝ)
    (hp : ReferenceFirstCollectionCorrectedFutureRecordingView.futureParameters rate rewards C_star C_h u t q x = some (enabled, xi)) :
    (∀ j, 0 ≤ xi j) ∧ (∑ j, xi j) ≤ 1 := by
  have hpres := (ReferenceFirstCollectionCorrectedFutureRecordingView.corrected_future_recordingView_presence
    rate rewards C_star C_h u t q hfuture x).2.2
  have hk := ReferenceFirstCollectionCorrectedFutureRecordingView.corrected_future_marker_section
    rate rewards C_star C_h control0 u t q hfuture x
  rw [hpres] at hp
  cases hv : ReferenceFirstCollectionCorrectedFutureRecordingView.futureRecordingView rate rewards C_star C_h u t q x with
  | none => simp only [hv, Option.bind_none, reduceCtorEq] at hp
  | some v =>
    rcases v with ⟨parameters, view, code⟩
    rw [hv] at hk
    obtain ⟨enabled', snapshot, valid, hparameters, _hcode, _hm⟩ := hk
    simp only [hv, Option.bind_some, hparameters, Option.some.injEq, Prod.mk.injEq] at hp
    have hxi : xi = CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor :=
      hp.2.symm.trans (funext view.payload.rate_eq_canonical)
    rw [hxi]
    exact ⟨fun j => (CanonicalRecordingRates.xi_pos p rate.eta.property _ j).le,
      CanonicalRecordingRates.sum_xi_le_one p rate.eta.property rate.sourceCap
        view.payload.anchor view.payload.anchor_pos⟩

/-- Every optional atom coefficient lies in [0,1], on all original sources. -/
theorem futureCoefficient_bounds (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) (x : X) :
    0 ≤ futureCoefficient rate rewards C_star C_h u t q o x ∧
      futureCoefficient rate rewards C_star C_h u t q o x ≤ 1 := by
  cases hp : ReferenceFirstCollectionCorrectedFutureRecordingView.futureParameters rate rewards C_star C_h u t q x with
  | none =>
    rcases o with _ | (_ | j) <;> simp only [futureCoefficient, hp,
      ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters, le_refl, zero_le_one, and_self]
  | some parameters =>
    rcases parameters with ⟨enabled, xi⟩
    obtain ⟨hpos, hsum⟩ := futureParameters_bounds
      rate rewards C_star C_h control0 u t q hfuture x enabled xi hp
    have hn : 0 ≤ ∑ j, xi j := Finset.sum_nonneg (fun j _ => hpos j)
    have hu (j : Fin p.K) : xi j ≤ 1 :=
      (Finset.single_le_sum (fun a _ => hpos a) (Finset.mem_univ j)).trans hsum
    rcases o with _ | (_ | j) <;> cases enabled <;>
      simp only [futureCoefficient, hp, ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
    all_goals first
      | exact ⟨zero_le_one, le_refl 1⟩
      | exact ⟨le_refl 0, zero_le_one⟩
      | exact ⟨sub_nonneg.mpr hsum, sub_le_self 1 hn⟩
      | exact ⟨hpos j, hu j⟩

/-- Predictability in the exact strict-prior source field at q. -/
theorem futureCoefficient_prior_measurable (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)]
      (futureCoefficient rate rewards C_star C_h u t q o) :=
  (ReferenceFirstCollectionRenewalNextRecordingLaw.measurable_coefficientOfParameters o).comp
    (ReferenceFirstCollectionCorrectedFutureRecordingView.futureParameters_prior_measurable rate rewards C_star C_h control0 u t q hfuture)

/-- Ambient Borelness follows from the prior field's inclusion in the source. -/
theorem futureCoefficient_measurable (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    Measurable (futureCoefficient rate rewards C_star C_h u t q o) :=
  (futureCoefficient_prior_measurable rate rewards C_star C_h control0 u t q hfuture o).mono
    ((sourcePrefixFiltration control0).le' (q.val + 1)) le_rfl

/-- The actual marker indicator is Borel, with no measurable-marker premise. -/
theorem futureTest_measurable (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    Measurable (futureTest rate rewards C_star C_h u t q o) :=
  (measurable_of_countable (fun a : Option (Option (Fin p.K)) =>
    if a = o then (1 : ℝ) else 0)).comp
      (ReferenceFirstCollectionCorrectedFutureRecordingView.futureMarker_measurable rate rewards C_star C_h control0 u t q hfuture)

/-- Every optional atom test is integrable under the original source law. -/
theorem futureTest_integrable (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    Integrable (futureTest rate rewards C_star C_h u t q o) (sourceInputLaw p) := by
  apply (integrable_const (1 : ℝ)).mono'
    (futureTest_measurable rate rewards C_star C_h control0 u t q hfuture o).aestronglyMeasurable
  filter_upwards [] with x
  unfold futureTest
  split <;> norm_num

/-- The predictable coefficient is integrable without restricting the source law. -/
theorem futureCoefficient_integrable (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    Integrable (futureCoefficient rate rewards C_star C_h u t q o) (sourceInputLaw p) := by
  apply (integrable_const (1 : ℝ)).mono'
    (futureCoefficient_measurable rate rewards C_star C_h control0 u t q hfuture o).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg
    (futureCoefficient_bounds rate rewards C_star C_h control0 u t q hfuture o x).1]
  exact (futureCoefficient_bounds rate rewards C_star C_h control0 u t q hfuture o x).2

private theorem integral_test_eq_of_mass {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass B] [DecidableEq B]
    (μ : Measure A) (f : A → B) (hf : Measurable f) (o : B)
    (c : ℝ) (hc : 0 ≤ c) (hmass : μ {a | f a = o} = ENNReal.ofReal c) :
    (∫ a, if f a = o then (1 : ℝ) else 0 ∂μ) = c := by
  have heq : (fun a => if f a = o then (1 : ℝ) else 0) =
      {a | f a = o}.indicator (fun _ => (1 : ℝ)) := by
    funext a
    by_cases h : f a = o <;> simp [Set.indicator, h]
  have hs : MeasurableSet {a | f a = o} := (measurableSet_singleton o).preimage hf
  rw [heq, integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one,
    measureReal_def, hmass, ENNReal.toReal_ofReal hc]

/-- The real atom indicator integrates over the complete current TimeControl.
This holds pointwise, including zero-mass and all absent/disabled branches. -/
theorem futureTest_control_integral (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (x : X) (o : Option (Option (Fin p.K))) :
    (∫ control, futureTest rate rewards C_star C_h u t q o
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q x control)
      ∂ContinuousLearningRows.timeControlLaw p) =
      futureCoefficient rate rewards C_star C_h u t q o x := by
  have hm := (ReferenceFirstCollectionCorrectedFutureRecordingView.futureMarker_replaceControl_measurable
    rate rewards C_star C_h control0 u t q hfuture).comp
      (measurable_const.prodMk measurable_id :
        Measurable (fun control : TimeControl p => (x, control)))
  exact integral_test_eq_of_mass (ContinuousLearningRows.timeControlLaw p)
    (fun control => ReferenceFirstCollectionCorrectedFutureRecordingView.futureMarker rate rewards C_star C_h u t q
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q x control))
    hm o _ (futureCoefficient_bounds rate rewards C_star C_h control0 u t q hfuture o x).1
    (futureMarker_control_mass rate rewards C_star C_h control0 u t q hfuture x o)

/-- The coefficient factors through the same strict prefix as the complete view. -/
theorem futureCoefficient_factor (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) (x : X) :
    futureCoefficient rate rewards C_star C_h u t q o x =
      futureCoefficient rate rewards C_star C_h u t q o (sourcePrefix control0 q.val x) := by
  unfold futureCoefficient
  rw [ReferenceFirstCollectionCorrectedFutureRecordingView.corrected_future_parameters_factor rate rewards C_star C_h control0 u t q hfuture x]

private def markerTestSet (u t q : Fin p.T) (o : Option (Option (Fin p.K))) :
    Set (X × TimeControl p) :=
  {v | ReferenceFirstCollectionCorrectedFutureRecordingView.futureMarker rate rewards C_star C_h u t q
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q v.1 v.2) = o}

private theorem markerTestSet_measurable (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    MeasurableSet (markerTestSet rate rewards C_star C_h u t q o) :=
  (measurableSet_singleton o).preimage
    (ReferenceFirstCollectionCorrectedFutureRecordingView.futureMarker_replaceControl_measurable rate rewards C_star C_h control0 u t q hfuture)

private theorem marker_sourceControlTest (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 q
      (markerTestSet rate rewards C_star C_h u t q o) =
      futureTest rate rewards C_star C_h u t q o := by
  funext x
  have hr := ReferenceFirstCollectionCorrectedFutureRecordingView.corrected_future_marker_reconstruct
    rate rewards C_star C_h control0 u t q hfuture x
  simp only [ReferenceSourceCurrentControlFreshness.sourceControlTest,
    Set.indicator_apply, markerTestSet, Set.mem_ofPred_eq,
    ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix,
    ReferenceSourceCurrentControlFreshness.u_t, ← hr, futureTest]

private theorem marker_sourceControlSection (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) (x : X) :
    (∫ control, (markerTestSet rate rewards C_star C_h u t q o).indicator
      (fun _ => (1 : ℝ))
      (ReferenceSourceCurrentControlFreshness.c_t p control0 q x, control)
      ∂ContinuousLearningRows.timeControlLaw p) =
      futureCoefficient rate rewards C_star C_h u t q o x := by
  simp only [markerTestSet, Set.indicator_apply, Set.mem_ofPred_eq,
    ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
  change (∫ control, futureTest rate rewards C_star C_h u t q o
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q
      (sourcePrefix control0 q.val x) control)
    ∂ContinuousLearningRows.timeControlLaw p) = _
  rw [futureTest_control_integral rate rewards C_star C_h control0 u t q hfuture,
    ← futureCoefficient_factor rate rewards C_star C_h control0 u t q hfuture o x]

private theorem marker_condExp_from_source_control (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    (sourceInputLaw p)[futureTest rate rewards C_star C_h u t q o |
      sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[sourceInputLaw p]
      futureCoefficient rate rewards C_star C_h u t q o := by
  have h := ReferenceSourceCurrentControlFreshness.source_control_test_condExp
    control0 q (markerTestSet rate rewards C_star C_h u t q o)
    (markerTestSet_measurable rate rewards C_star C_h control0 u t q hfuture o)
  rw [marker_sourceControlTest rate rewards C_star C_h control0 u t q hfuture o,
    ← ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t control0 q] at h
  filter_upwards [h] with x hx
  exact hx.trans (marker_sourceControlSection rate rewards C_star C_h control0 u t q hfuture o x)

/-- Unnormalized equality on every event of the existing prior field Fq.
Outer absence is included, so no division by the corrected event's mass occurs. -/
theorem futureTest_setIntegral (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) (A : Set X)
    (hA : MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)] A) :
    (∫ x in A, futureTest rate rewards C_star C_h u t q o x ∂sourceInputLaw p) =
      ∫ x in A, futureCoefficient rate rewards C_star C_h u t q o x ∂sourceInputLaw p := by
  have hle := (sourcePrefixFiltration control0).le' (q.val + 1)
  have hce := marker_condExp_from_source_control
    rate rewards C_star C_h control0 u t q hfuture o
  calc
    _ = ∫ x in A, ((sourceInputLaw p)[futureTest rate rewards C_star C_h u t q o |
        sourcePrefixFiltration control0 (q.val + 1)]) x ∂sourceInputLaw p :=
      (setIntegral_condExp hle
        (futureTest_integrable rate rewards C_star C_h control0 u t q hfuture o) hA).symm
    _ = _ := setIntegral_congr_ae (hle A hA) (hce.mono (fun _ hx _ => hx))

/-- The strict-future optional conditional recording law on the original source.
The only logical input is the strict-future index inequality. -/
theorem futureMarker_condExp (control0 : TimeControl p)
    (u t q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (o : Option (Option (Fin p.K))) :
    (sourceInputLaw p)[futureTest rate rewards C_star C_h u t q o |
      sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[sourceInputLaw p]
      futureCoefficient rate rewards C_star C_h u t q o := by
  have hf := futureTest_integrable rate rewards C_star C_h control0 u t q hfuture o
  have hg := futureCoefficient_integrable rate rewards C_star C_h control0 u t q hfuture o
  have hm := futureCoefficient_prior_measurable rate rewards C_star C_h control0 u t q hfuture o
  exact (ae_eq_condExp_of_forall_setIntegral_eq
    ((sourcePrefixFiltration control0).le' (q.val + 1)) hf
    (fun _ _ _ => hg.integrableOn)
    (fun A hA _ => (futureTest_setIntegral
      rate rewards C_star C_h control0 u t q hfuture o A hA).symm)
    hm.stronglyMeasurable.aestronglyMeasurable).symm

end Bandits.Support.ReferenceFirstCollectionCorrectedFutureRecordingLaw
