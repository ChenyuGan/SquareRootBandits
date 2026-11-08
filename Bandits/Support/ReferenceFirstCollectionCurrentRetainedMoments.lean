/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentRetainedGate

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Tactic

/-!
# Original-law retained first-call raw moments

The retained arrival is localized to the original first collection call and
the predictable no-earlier-overflow test. Its moment coefficients are the
existing quantized coefficients, localized by that same retained test.

Sources: `04_slow_fast_learner.tex:140-188,245-274`,
`05_binary_transport.tex:352-431`, and
`06_interruptions.tex:355-426` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCurrentRetainedMoments

open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)
open ReferenceFirstCollectionCurrentRetainedGate (H G acceptedCurrent?)
open ReferenceFirstCollectionCurrentRawMoments
  (currentRaw currentMomentOne currentMomentTwo
    currentRaw_indicator_sq_eq currentRaw_measurable currentRaw_integrable
    currentRaw_indicator_sq_integrable currentRaw_condExp currentRaw_sq_condExp
    currentMomentOne_measurable currentMomentTwo_measurable
    currentMomentOne_integrable currentMomentTwo_integrable
    currentMoment_coefficients_on_firstCell currentMoment_bounds_on_firstCell
    currentRaw_bounds_on_firstCell)

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

/-- The original raw arrival, localized to the actual retained first-call
event on the same source space and under the same source law. -/
def retainedRaw (u t : Fin p.T) (a : Fin p.K) : SourceInput p → ℝ :=
  (G rate rewards C_star C_h u t).indicator
    (currentRaw rate rewards C_star C_h t a)

/-- The original first-moment coefficient with the predictable retained test
applied once. -/
def retainedMomentOne (u t : Fin p.T) (a : Fin p.K) : SourceInput p → ℝ :=
  (H rate rewards C_star C_h t).indicator
    (currentMomentOne rate rewards C_star C_h u t a)

/-- The original square-moment coefficient with the same predictable retained
test applied once. -/
def retainedMomentTwo (u t : Fin p.T) (a : Fin p.K) : SourceInput p → ℝ :=
  (H rate rewards C_star C_h t).indicator
    (currentMomentTwo rate rewards C_star C_h u t a)

/-- Intersecting the first-call event with the retained test is exactly the
literal nested indicator used by conditional expectation. -/
theorem retainedRaw_eq_H_indicator_firstCell (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) :
    retainedRaw rate rewards C_star C_h u t a z =
      (H rate rewards C_star C_h t).indicator
        ((firstCell rate rewards C_star C_h u t).indicator
          (currentRaw rate rewards C_star C_h t a)) z := by
  by_cases hE : z ∈ firstCell rate rewards C_star C_h u t
  · by_cases hH : z ∈ H rate rewards C_star C_h t
    · simp [retainedRaw, G, hE, hH]
    · simp [retainedRaw, G, hE, hH]
  · simp [retainedRaw, G, Set.indicator, hE]

/-- Squaring the retained raw scalar gives the retained square of the
first-call-localized scalar. -/
theorem retainedRaw_sq_eq_H_indicator_firstCell_sq (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p) :
    (retainedRaw rate rewards C_star C_h u t a z) ^ 2 =
      (H rate rewards C_star C_h t).indicator
        (fun z => ((firstCell rate rewards C_star C_h u t).indicator
          (currentRaw rate rewards C_star C_h t a) z) ^ 2) z := by
  rw [retainedRaw_eq_H_indicator_firstCell rate rewards C_star C_h u t a z]
  by_cases hH : z ∈ H rate rewards C_star C_h t
  · simp [hH]
  · simp [hH]

/-- The existing square-indicator identity rewrites the inner expression as
the first-call indicator of the literal raw square. -/
theorem retainedRaw_sq_eq_H_indicator_firstCell_raw_sq (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p) :
    (retainedRaw rate rewards C_star C_h u t a z) ^ 2 =
      (H rate rewards C_star C_h t).indicator
        ((firstCell rate rewards C_star C_h u t).indicator
          (fun z => (currentRaw rate rewards C_star C_h t a z) ^ 2)) z := by
  rw [retainedRaw_sq_eq_H_indicator_firstCell_sq]
  by_cases hH : z ∈ H rate rewards C_star C_h t
  · simpa only [Set.indicator_of_mem hH] using
      currentRaw_indicator_sq_eq rate rewards C_star C_h u t a z
  · simp [Set.indicator, hH]

/-- The retained scalar is explicitly zero away from the first-call event. -/
theorem retainedRaw_eq_zero_of_not_mem_firstCell (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p)
    (hz : z ∉ firstCell rate rewards C_star C_h u t) :
    retainedRaw rate rewards C_star C_h u t a z = 0 := by
  have hG : z ∉ G rate rewards C_star C_h u t := fun h => hz h.1
  simp [retainedRaw, hG]

/-- The first coefficient vanishes away from the retained first-call event. -/
theorem retainedMomentOne_eq_zero_of_not_mem_G (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p)
    (hz : z ∉ G rate rewards C_star C_h u t) :
    retainedMomentOne rate rewards C_star C_h u t a z = 0 := by
  by_cases hH : z ∈ H rate rewards C_star C_h t
  · have hE : z ∉ firstCell rate rewards C_star C_h u t := by
      intro hE
      exact hz ⟨hE, hH⟩
    simp [retainedMomentOne, currentMomentOne, hH, hE]
  · simp [retainedMomentOne, hH]

/-- The square coefficient vanishes away from the retained first-call event. -/
theorem retainedMomentTwo_eq_zero_of_not_mem_G (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p)
    (hz : z ∉ G rate rewards C_star C_h u t) :
    retainedMomentTwo rate rewards C_star C_h u t a z = 0 := by
  by_cases hH : z ∈ H rate rewards C_star C_h t
  · have hE : z ∉ firstCell rate rewards C_star C_h u t := by
      intro hE
      exact hz ⟨hE, hH⟩
    simp [retainedMomentTwo, currentMomentTwo, hH, hE]
  · simp [retainedMomentTwo, hH]

/-- On either original first invocation, the accepted observer and retained
arrival use one and the same strict-past source prefix and current cell. The
prefix test is the all-prefix overflow criterion, so a later drained queue
cannot erase an earlier crossing. -/
theorem retainedRaw_eq_acceptedArrival_on_firstCell (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
          rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
          rate rewards C_star C_h t z = some c ∧
      c.enabled = true ∧
      (z ∈ H rate rewards C_star C_h t ↔
        ∀ h ≤ L.length, ∀ j : Fin p.K,
          32 * (UnstoppedRecordedQueueComparison.unstoppedReplay
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L h j).2 ≤
              (ReferenceFirstLaunchNumericalCell.queueParameters rate).D) ∧
      acceptedCurrent? rate rewards C_star C_h t a z =
        some (RecordedQueueRun.acceptedRecord
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) c a) ∧
      retainedRaw rate rewards C_star C_h u t a z =
        ((RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) c a) : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) ∧
      (retainedRaw rate rewards C_star C_h u t a z) ^ 2 =
        ((RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) c a) : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) ^ 2 := by
  obtain ⟨L, c, hL, hc, henabled, haccepted, hrecorded, harrival⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_acceptedRecord
      rate rewards C_star C_h u t a z hz
  obtain ⟨L', hL', _hlen, hall⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_allPrefixes
      rate rewards C_star C_h u t z hz
  have hsame : L = L' := Option.some.inj (hL.symm.trans hL')
  subst L'
  have hretained : retainedRaw rate rewards C_star C_h u t a z =
      (H rate rewards C_star C_h t).indicator
        (currentRaw rate rewards C_star C_h t a) z := by
    by_cases hH : z ∈ H rate rewards C_star C_h t
    · simp [retainedRaw, G, hz, hH]
    · simp [retainedRaw, G, hz, hH]
  refine ⟨L, c, hL, hc, henabled, ?_, haccepted, ?_, ?_⟩
  · simpa using hall
  · calc
      retainedRaw rate rewards C_star C_h u t a z =
          (H rate rewards C_star C_h t).indicator
            (currentRaw rate rewards C_star C_h t a) z := hretained
      _ = ((RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) c a) : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) :=
        harrival.symm
  · calc
      (retainedRaw rate rewards C_star C_h u t a z) ^ 2 =
          ((H rate rewards C_star C_h t).indicator
            (currentRaw rate rewards C_star C_h t a) z) ^ 2 := by rw [hretained]
      _ = ((RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) c a) : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) ^ 2 := by
        rw [← harrival]

/-- The retained raw scalar is measurable on the ambient original source. -/
theorem retainedRaw_measurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Measurable (retainedRaw rate rewards C_star C_h u t a) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hG := ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
    rate rewards C_star C_h control0 u t
  exact (currentRaw_measurable rate rewards C_star C_h t a).indicator (hle _ hG)

/-- The square of the retained raw scalar is ambient measurable. -/
theorem retainedRaw_sq_measurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Measurable (fun z => (retainedRaw rate rewards C_star C_h u t a z) ^ 2) :=
  (retainedRaw_measurable rate rewards C_star C_h control0 u t a).pow_const 2

/-- The retained raw scalar is integrable under the original source law,
including when the first-call event has zero mass. -/
theorem retainedRaw_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (retainedRaw rate rewards C_star C_h u t a) (sourceInputLaw p) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hH := ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
    rate rewards C_star C_h control0 t
  have hHambient : MeasurableSet (H rate rewards C_star C_h t) := hle _ hH
  have hrepr : retainedRaw rate rewards C_star C_h u t a = fun z =>
      (H rate rewards C_star C_h t).indicator
        ((firstCell rate rewards C_star C_h u t).indicator
          (currentRaw rate rewards C_star C_h t a)) z := by
    funext z
    exact retainedRaw_eq_H_indicator_firstCell rate rewards C_star C_h u t a z
  rw [hrepr]
  exact (currentRaw_integrable rate rewards C_star C_h control0 u t a).indicator hHambient

/-- The square of the retained raw scalar is integrable under the same
original source law. -/
theorem retainedRaw_sq_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (fun z => (retainedRaw rate rewards C_star C_h u t a z) ^ 2)
      (sourceInputLaw p) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hH := ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
    rate rewards C_star C_h control0 t
  have hHambient : MeasurableSet (H rate rewards C_star C_h t) := hle _ hH
  have hrepr : (fun z => (retainedRaw rate rewards C_star C_h u t a z) ^ 2) =
      fun z => (H rate rewards C_star C_h t).indicator
        (fun z => ((firstCell rate rewards C_star C_h u t).indicator
          (currentRaw rate rewards C_star C_h t a) z) ^ 2) z := by
    funext z
    exact retainedRaw_sq_eq_H_indicator_firstCell_sq rate rewards C_star C_h u t a z
  rw [hrepr]
  exact (currentRaw_indicator_sq_integrable
    rate rewards C_star C_h control0 u t a).indicator hHambient

/-- The first retained coefficient is measurable in the exact original
pre-choice source-prefix field. -/
theorem retainedMomentOne_measurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (retainedMomentOne rate rewards C_star C_h u t a) := by
  exact (currentMomentOne_measurable
    rate rewards C_star C_h control0 u t a).indicator
      (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
        rate rewards C_star C_h control0 t)

/-- The square coefficient is measurable in the same original
pre-choice source-prefix field. -/
theorem retainedMomentTwo_measurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (retainedMomentTwo rate rewards C_star C_h u t a) := by
  exact (currentMomentTwo_measurable
    rate rewards C_star C_h control0 u t a).indicator
      (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
        rate rewards C_star C_h control0 t)

/-- The first retained coefficient is integrable under the ambient original
source law. -/
theorem retainedMomentOne_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (retainedMomentOne rate rewards C_star C_h u t a)
      (sourceInputLaw p) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hH := ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
    rate rewards C_star C_h control0 t
  exact (currentMomentOne_integrable
    rate rewards C_star C_h control0 u t a).indicator (hle _ hH)

/-- The square coefficient is integrable under the same ambient original
source law. -/
theorem retainedMomentTwo_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (retainedMomentTwo rate rewards C_star C_h u t a)
      (sourceInputLaw p) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hH := ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
    rate rewards C_star C_h control0 t
  exact (currentMomentTwo_integrable
    rate rewards C_star C_h control0 u t a).indicator (hle _ hH)

/-- Original-law conditional expectation of the retained raw arrival. The
predictable indicator is applied to the existing first-call conditional law,
without an event-mass factor or a change of measure. -/
theorem retainedRaw_condExp (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    (sourceInputLaw p)[retainedRaw rate rewards C_star C_h u t a |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      retainedMomentOne rate rewards C_star C_h u t a := by
  let μ := sourceInputLaw p
  let F := sourcePrefixFiltration control0 (t.val + 1)
  let f := (firstCell rate rewards C_star C_h u t).indicator
    (currentRaw rate rewards C_star C_h t a)
  have hrepr : retainedRaw rate rewards C_star C_h u t a =
      fun z => (H rate rewards C_star C_h t).indicator f z := by
    funext z
    exact retainedRaw_eq_H_indicator_firstCell rate rewards C_star C_h u t a z
  have hH : MeasurableSet[F] (H rate rewards C_star C_h t) := by
    simpa [F] using ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
      rate rewards C_star C_h control0 t
  have hbase := currentRaw_integrable rate rewards C_star C_h control0 u t a
  have hcut := condExp_indicator hbase hH
  have hraw := currentRaw_condExp rate rewards C_star C_h control0 u t a
  calc
    μ[retainedRaw rate rewards C_star C_h u t a | F] =ᵐ[μ]
        μ[fun z => (H rate rewards C_star C_h t).indicator f z | F] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hrepr z)
    _ =ᵐ[μ] (H rate rewards C_star C_h t).indicator (μ[f | F]) := hcut
    _ =ᵐ[μ] retainedMomentOne rate rewards C_star C_h u t a := by
      filter_upwards [hraw] with z hz
      have hpoint : μ[f | F] z =
          currentMomentOne rate rewards C_star C_h u t a z := by
        simpa [μ, F, f] using hz
      by_cases hH' : z ∈ H rate rewards C_star C_h t
      · simp [retainedMomentOne, hH', hpoint]
      · simp [retainedMomentOne, hH']

/-- Original-law conditional expectation of the square of the retained raw
arrival, using the existing first-call square conditional law. -/
theorem retainedRaw_sq_condExp (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    (sourceInputLaw p)[
      (fun z => (retainedRaw rate rewards C_star C_h u t a z) ^ 2) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      retainedMomentTwo rate rewards C_star C_h u t a := by
  let μ := sourceInputLaw p
  let F := sourcePrefixFiltration control0 (t.val + 1)
  let f := fun z => ((firstCell rate rewards C_star C_h u t).indicator
    (currentRaw rate rewards C_star C_h t a) z) ^ 2
  have hrepr : (fun z => (retainedRaw rate rewards C_star C_h u t a z) ^ 2) =
      fun z => (H rate rewards C_star C_h t).indicator f z := by
    funext z
    exact retainedRaw_sq_eq_H_indicator_firstCell_sq rate rewards C_star C_h u t a z
  have hH : MeasurableSet[F] (H rate rewards C_star C_h t) := by
    simpa [F] using ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
      rate rewards C_star C_h control0 t
  have hbase := currentRaw_indicator_sq_integrable rate rewards C_star C_h control0 u t a
  have hcut := condExp_indicator hbase hH
  have hraw := currentRaw_sq_condExp rate rewards C_star C_h control0 u t a
  calc
    μ[(fun z => (retainedRaw rate rewards C_star C_h u t a z) ^ 2) | F] =ᵐ[μ]
        μ[fun z => (H rate rewards C_star C_h t).indicator f z | F] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hrepr z)
    _ =ᵐ[μ] (H rate rewards C_star C_h t).indicator (μ[f | F]) := hcut
    _ =ᵐ[μ] retainedMomentTwo rate rewards C_star C_h u t a := by
      filter_upwards [hraw] with z hz
      have hpoint : μ[f | F] z =
          currentMomentTwo rate rewards C_star C_h u t a z := by
        simpa [μ, F, f] using hz
      by_cases hH' : z ∈ H rate rewards C_star C_h t
      · simp [retainedMomentTwo, hH', hpoint]
      · simp [retainedMomentTwo, hH']

/-- Exact first and square moment coefficients on the retained event, using
the existing quantized coefficient identities. -/
theorem retainedMoment_coefficients_on_G (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p)
    (hz : z ∈ G rate rewards C_star C_h u t) :
    ∃ theta : AssignmentParameterFibreKernel.Theta p,
      ReferenceCalendarLaterSamplerPredictability.calendarParameters
          rate rewards C_star C_h t z = some theta ∧
      retainedMomentOne rate rewards C_star C_h u t a z =
        CanonicalRecordingRates.xi p rate.eta.val theta.2 a *
          QuantizedRecordingMoments.quantizedValue
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
            (CanonicalRecordingRates.xi p rate.eta.val theta.2 a)
            (((rewards t a).val : ℝ) / (D p : ℝ)) ∧
      retainedMomentTwo rate rewards C_star C_h u t a z =
        CanonicalRecordingRates.xi p rate.eta.val theta.2 a *
          (QuantizedRecordingMoments.quantizedValue
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
            (CanonicalRecordingRates.xi p rate.eta.val theta.2 a)
            (((rewards t a).val : ℝ) / (D p : ℝ))) ^ 2 := by
  obtain ⟨theta, htheta, hone, htwo⟩ :=
    currentMoment_coefficients_on_firstCell rate rewards C_star C_h u t a z hz.1
  have hB1 : retainedMomentOne rate rewards C_star C_h u t a z =
      currentMomentOne rate rewards C_star C_h u t a z :=
    Set.indicator_of_mem hz.2 (currentMomentOne rate rewards C_star C_h u t a)
  have hB2 : retainedMomentTwo rate rewards C_star C_h u t a z =
      currentMomentTwo rate rewards C_star C_h u t a z :=
    Set.indicator_of_mem hz.2 (currentMomentTwo rate rewards C_star C_h u t a)
  exact ⟨theta, htheta, hB1.trans hone, hB2.trans htwo⟩

/-- The manuscript's rounding and moment bounds on the retained event: the
first coefficient lies between the rounded reward minus one quantization step
and the rounded reward, while the square coefficient has the sharp inverse
rate bound and the global beta envelope. -/
theorem retainedMoment_bounds_on_G (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p)
    (hz : z ∈ G rate rewards C_star C_h u t) :
    ∃ theta : AssignmentParameterFibreKernel.Theta p,
      ReferenceCalendarLaterSamplerPredictability.calendarParameters
          rate rewards C_star C_h t z = some theta ∧
      (((rewards t a).val : ℝ) / (D p : ℝ)) -
          CanonicalRecordingRates.xi p rate.eta.val theta.2 a /
            (rate.eta.val * (D p : ℝ)) ≤
        retainedMomentOne rate rewards C_star C_h u t a z ∧
      0 ≤ retainedMomentOne rate rewards C_star C_h u t a z ∧
      retainedMomentOne rate rewards C_star C_h u t a z ≤
        ((rewards t a).val : ℝ) / (D p : ℝ) ∧
      retainedMomentOne rate rewards C_star C_h u t a z ≤ 1 ∧
      0 ≤ retainedMomentTwo rate rewards C_star C_h u t a z ∧
      retainedMomentTwo rate rewards C_star C_h u t a z ≤
        (((rewards t a).val : ℝ) / (D p : ℝ)) ^ 2 /
          CanonicalRecordingRates.xi p rate.eta.val theta.2 a ∧
      retainedMomentTwo rate rewards C_star C_h u t a z ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  obtain ⟨theta, htheta, hlower, hone, honeReward, honeOne,
    htwo, htwoSharp, htwoBeta⟩ :=
    currentMoment_bounds_on_firstCell rate rewards C_star C_h u t a z hz.1
  have hB1 : retainedMomentOne rate rewards C_star C_h u t a z =
      currentMomentOne rate rewards C_star C_h u t a z :=
    Set.indicator_of_mem hz.2 (currentMomentOne rate rewards C_star C_h u t a)
  have hB2 : retainedMomentTwo rate rewards C_star C_h u t a z =
      currentMomentTwo rate rewards C_star C_h u t a z :=
    Set.indicator_of_mem hz.2 (currentMomentTwo rate rewards C_star C_h u t a)
  refine ⟨theta, htheta, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hB1]
    exact hlower
  · rw [hB1]
    exact hone
  · rw [hB1]
    exact honeReward
  · rw [hB1]
    exact honeOne
  · rw [hB2]
    exact htwo
  · rw [hB2]
    exact htwoSharp
  · rw [hB2]
    exact htwoBeta

/-- Globally, the retained scalar is nonnegative and bounded by the
normalization envelope. -/
theorem retainedRaw_bounds (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) :
    0 ≤ retainedRaw rate rewards C_star C_h u t a z ∧
      retainedRaw rate rewards C_star C_h u t a z ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  by_cases hz : z ∈ G rate rewards C_star C_h u t
  · have hA : retainedRaw rate rewards C_star C_h u t a z =
        currentRaw rate rewards C_star C_h t a z := by
      simp [retainedRaw, hz]
    rw [hA]
    exact currentRaw_bounds_on_firstCell rate rewards C_star C_h u t a z hz.1
  · have hzero : retainedRaw rate rewards C_star C_h u t a z = 0 := by
      simp [retainedRaw, hz]
    rw [hzero]
    exact ⟨le_rfl, div_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
      (CanonicalRecordingRates.beta_pos p rate.eta.property).le⟩

/-- The first retained coefficient is globally nonnegative and is bounded by
the retained indicator of the rounded reward, itself at most one. -/
theorem retainedMomentOne_roundedReward_bounds (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p) :
    0 ≤ retainedMomentOne rate rewards C_star C_h u t a z ∧
      retainedMomentOne rate rewards C_star C_h u t a z ≤
        (G rate rewards C_star C_h u t).indicator
          (fun _ : SourceInput p => ((rewards t a).val : ℝ) / (D p : ℝ)) z ∧
      (G rate rewards C_star C_h u t).indicator
          (fun _ : SourceInput p => ((rewards t a).val : ℝ) / (D p : ℝ)) z ≤ 1 := by
  by_cases hz : z ∈ G rate rewards C_star C_h u t
  · obtain ⟨_theta, _htheta, _hlower, hnonneg, hupper, _hone,
      _htwoNonneg, _htwoUpper, _htwoBeta⟩ :=
        currentMoment_bounds_on_firstCell rate rewards C_star C_h u t a z hz.1
    have hB1 : retainedMomentOne rate rewards C_star C_h u t a z =
        currentMomentOne rate rewards C_star C_h u t a z :=
      Set.indicator_of_mem hz.2 (currentMomentOne rate rewards C_star C_h u t a)
    have hrounded : (G rate rewards C_star C_h u t).indicator
        (fun _ : SourceInput p => ((rewards t a).val : ℝ) / (D p : ℝ)) z =
          ((rewards t a).val : ℝ) / (D p : ℝ) :=
      Set.indicator_of_mem hz
        (fun _ : SourceInput p => ((rewards t a).val : ℝ) / (D p : ℝ))
    have hrewardOne : ((rewards t a).val : ℝ) / (D p : ℝ) ≤ 1 := by
      apply (div_le_one (Nat.cast_pos.mpr (D_pos p))).2
      exact_mod_cast (Nat.le_of_lt_succ (rewards t a).isLt)
    rw [hB1, hrounded]
    exact ⟨hnonneg, hupper, hrewardOne⟩
  · have hzero := retainedMomentOne_eq_zero_of_not_mem_G
      rate rewards C_star C_h u t a z hz
    have hrounded : (G rate rewards C_star C_h u t).indicator
        (fun _ : SourceInput p => ((rewards t a).val : ℝ) / (D p : ℝ)) z = 0 := by
      simp [Set.indicator_of_notMem hz]
    rw [hzero, hrounded]
    norm_num

/-- Both retained coefficients are globally nonnegative, with the square
coefficient bounded by the original inverse-beta envelope. -/
theorem retainedMomentTwo_bounds (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) :
    0 ≤ retainedMomentTwo rate rewards C_star C_h u t a z ∧
      retainedMomentTwo rate rewards C_star C_h u t a z ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  by_cases hz : z ∈ G rate rewards C_star C_h u t
  · obtain ⟨_, _, _, _, _, _, hnonneg, _, hbeta⟩ :=
      retainedMoment_bounds_on_G rate rewards C_star C_h u t a z hz
    exact ⟨hnonneg, hbeta⟩
  · have hzero := retainedMomentTwo_eq_zero_of_not_mem_G
      rate rewards C_star C_h u t a z hz
    rw [hzero]
    exact ⟨le_rfl, div_nonneg (by norm_num)
      (CanonicalRecordingRates.beta_pos p rate.eta.property).le⟩

/-- For every set measurable in the original pre-choice field, integrating the
retained raw arrival equals integrating its first coefficient. -/
theorem retainedRaw_setIntegral (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) (A : Set (SourceInput p))
    (hA : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] A) :
    (∫ z in A, retainedRaw rate rewards C_star C_h u t a z ∂sourceInputLaw p) =
      ∫ z in A, retainedMomentOne rate rewards C_star C_h u t a z
        ∂sourceInputLaw p := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hce := retainedRaw_condExp rate rewards C_star C_h control0 u t a
  have hceOnA : ∀ᵐ z ∂sourceInputLaw p, z ∈ A →
      (sourceInputLaw p)[retainedRaw rate rewards C_star C_h u t a |
        sourcePrefixFiltration control0 (t.val + 1)] z =
        retainedMomentOne rate rewards C_star C_h u t a z :=
    hce.mono fun z hz _ => hz
  calc
    _ = ∫ z in A,
        (sourceInputLaw p)[retainedRaw rate rewards C_star C_h u t a |
          sourcePrefixFiltration control0 (t.val + 1)] z ∂sourceInputLaw p :=
      (setIntegral_condExp hle
        (retainedRaw_integrable rate rewards C_star C_h control0 u t a) hA).symm
    _ = _ := setIntegral_congr_ae (hle _ hA) hceOnA

/-- The same arbitrary-field-set identity for the square raw moment. -/
theorem retainedRaw_sq_setIntegral (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) (A : Set (SourceInput p))
    (hA : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] A) :
    (∫ z in A, (retainedRaw rate rewards C_star C_h u t a z) ^ 2
        ∂sourceInputLaw p) =
      ∫ z in A, retainedMomentTwo rate rewards C_star C_h u t a z
        ∂sourceInputLaw p := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hce := retainedRaw_sq_condExp rate rewards C_star C_h control0 u t a
  have hceOnA : ∀ᵐ z ∂sourceInputLaw p, z ∈ A →
      (sourceInputLaw p)[(fun z =>
        (retainedRaw rate rewards C_star C_h u t a z) ^ 2) |
        sourcePrefixFiltration control0 (t.val + 1)] z =
        retainedMomentTwo rate rewards C_star C_h u t a z :=
    hce.mono fun z hz _ => hz
  calc
    _ = ∫ z in A,
        (sourceInputLaw p)[(fun z =>
          (retainedRaw rate rewards C_star C_h u t a z) ^ 2) |
          sourcePrefixFiltration control0 (t.val + 1)] z ∂sourceInputLaw p :=
      (setIntegral_condExp hle
        (retainedRaw_sq_integrable rate rewards C_star C_h control0 u t a) hA).symm
    _ = _ := setIntegral_congr_ae (hle _ hA) hceOnA

end Bandits.Support.ReferenceFirstCollectionCurrentRetainedMoments

end
