/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionOriginalSourceFibreTransport

/-!
# Original-source transport to the actual physical continuation

Sources: `sources/zip4/manuscript/06_interruptions.tex:391-426` and
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`.

The suffix and fixed-calendar observations below are projections of the same
actual complete physical execution. Fibre integrals replace only the current
control and retain the original source and every later control.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Bandits.Support.ReferenceFirstCollectionPhysicalContinuationFibreLaw

open ReferenceFirstCollectionOriginalSourceFibreTransport
  (SourceInput Outcome AssignmentVector JointY)
open ReferenceFirstCollectionPastSamplerFibreLaw (PastFibreY pastFibreOutput)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceCalendarLaterSamplerPredictability (calendarParameters)
open AssignmentParameterFibreKernel (fibreMass fibreMeasure)
open ReferenceFixedTimeSourceControlCoupling (replaceSourceControl)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)
open ReferenceLaterOptionalControlResampling (controlRemainderLaw)
open LaunchAssignmentCoordinateSplit (controlAssignmentSplitEquiv)
open ReferenceGeneratedCompleteCalendarObservation (completeSuffixCode)
open ReferenceCalendarActualControlCallbackSections (codeAt)
open ReferenceActiveHorizonMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RoundRecordCode (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)
abbrev PathOutputY (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  List (RoundRecordCode p rate) × PastFibreY p
abbrev CalendarOutputY (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Option (RoundRecordCode p rate) × PastFibreY p

local instance outcomeMeasurableSpace (p : Parameters) :
    MeasurableSpace (Outcome p) := ⊤
local instance outcomeDiscreteMeasurableSpace (p : Parameters) :
    DiscreteMeasurableSpace (Outcome p) := ⟨fun _ => trivial⟩
local instance outcomeOptionMeasurableSpace (p : Parameters) :
    MeasurableSpace (Option (Outcome p)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) :=
  ReferenceFirstCollectionOriginalSourceFibreTransport.sourceInputMeasurableSpace p

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The literal complete physical suffix together with the existing first-call
past/fibre output. -/
def pathOutput (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceInput p) : PathOutputY p rate :=
  (completeSuffixCode (rate := rate) rewards C_star C_h z,
    pastFibreOutput rate rewards C_star C_h control0 z)

/-- A Borel indicator of the literal suffix and first-call mark. -/
def pathTest (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (PathOutputY p rate)) (z : SourceInput p) : ℝ :=
  B.indicator (fun _ => (1 : ℝ)) (pathOutput rate rewards C_star C_h control0 z)

/-- The unnormalised fixed-cell fibre section for the actual complete suffix.
The source is always the original source with only the current control
replaced; the `none` parameter branch is the analytical off-cell zero. -/
def pathSection (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (a : Outcome p) (B : Set (PathOutputY p rate))
    (z : SourceInput p) : ℝ :=
  match calendarParameters rate rewards C_star C_h t z with
  | none => 0
  | some theta => (fibreMass p theta a).toReal *
      ∫ vw, B.indicator (fun _ => (1 : ℝ))
        (completeSuffixCode (rate := rate) rewards C_star C_h
            (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw)),
          some (u, (t, (sourcePrefix control0 t.val z, (some a, vw.1)))))
        ∂(fibreMeasure p theta a).prod (controlRemainderLaw p)

/-- The literal calendar-date code paired with the same first-call mark. -/
def calendarOutput (control0 : ContinuousLearningRows.TimeControl p)
    (b : Fin p.T) (z : SourceInput p) : CalendarOutputY p rate :=
  (codeAt rate rewards C_star C_h b z,
    pastFibreOutput rate rewards C_star C_h control0 z)

/-- A Borel indicator of the literal fixed-calendar observation. -/
def calendarTest (control0 : ContinuousLearningRows.TimeControl p) (b : Fin p.T)
    (B : Set (CalendarOutputY p rate)) (z : SourceInput p) : ℝ :=
  B.indicator (fun _ => (1 : ℝ))
    (calendarOutput rate rewards C_star C_h control0 b z)

/-- The fixed-date fibre section uses the original date `b` on every cell,
including when the current invocation date lies after `b`. -/
def calendarSection (control0 : ContinuousLearningRows.TimeControl p)
    (b u t : Fin p.T) (a : Outcome p) (B : Set (CalendarOutputY p rate))
    (z : SourceInput p) : ℝ :=
  match calendarParameters rate rewards C_star C_h t z with
  | none => 0
  | some theta => (fibreMass p theta a).toReal *
      ∫ vw, B.indicator (fun _ => (1 : ℝ))
        (codeAt rate rewards C_star C_h b
            (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw)),
          some (u, (t, (sourcePrefix control0 t.val z, (some a, vw.1)))))
        ∂(fibreMeasure p theta a).prod (controlRemainderLaw p)

private def pathObservationMap (x : JointY p) : PathOutputY p rate :=
  (completeSuffixCode (rate := rate) rewards C_star C_h x.1, x.2)

private def calendarObservationMap (b : Fin p.T) (x : JointY p) :
    CalendarOutputY p rate :=
  (codeAt rate rewards C_star C_h b x.1, x.2)

private def pathPullbackSet (B : Set (PathOutputY p rate)) : Set (JointY p) :=
  {x | (completeSuffixCode (rate := rate) rewards C_star C_h x.1, x.2) ∈ B}

private def calendarPullbackSet (b : Fin p.T) (B : Set (CalendarOutputY p rate)) :
    Set (JointY p) :=
  {x | (codeAt rate rewards C_star C_h b x.1, x.2) ∈ B}

private theorem pathObservationMap_measurable :
    Measurable (pathObservationMap rate rewards C_star C_h) := by
  exact (ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
    (rate := rate) rewards C_star C_h).comp measurable_fst |>.prodMk measurable_snd

private theorem calendarObservationMap_measurable (b : Fin p.T) :
    Measurable (calendarObservationMap rate rewards C_star C_h b) := by
  exact (ReferenceCalendarActualControlCallbackSections.measurable_codeAt
    rate rewards C_star C_h b).comp measurable_fst |>.prodMk measurable_snd

private theorem pathPullbackSet_measurable (B : Set (PathOutputY p rate))
    (hB : MeasurableSet B) : MeasurableSet (pathPullbackSet rate rewards C_star C_h B) :=
  pathObservationMap_measurable rate rewards C_star C_h hB

private theorem calendarPullbackSet_measurable (b : Fin p.T)
    (B : Set (CalendarOutputY p rate)) (hB : MeasurableSet B) :
    MeasurableSet (calendarPullbackSet rate rewards C_star C_h b B) :=
  calendarObservationMap_measurable rate rewards C_star C_h b hB

theorem pathOutput_measurable (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (pathOutput rate rewards C_star C_h control0) := by
  exact (ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
    (rate := rate) rewards C_star C_h).prodMk
      (ReferenceFirstCollectionPastSamplerFibreLaw.pastFibreOutput_measurable
        rate rewards C_star C_h control0)

theorem pathTest_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (PathOutputY p rate)) (hB : MeasurableSet B) :
    Measurable (pathTest rate rewards C_star C_h control0 B) :=
  (measurable_const.indicator hB).comp
    (pathOutput_measurable rate rewards C_star C_h control0)

theorem pathTest_integrable (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (PathOutputY p rate)) (hB : MeasurableSet B) :
    Integrable (pathTest rate rewards C_star C_h control0 B)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hB' := pathPullbackSet_measurable rate rewards C_star C_h B hB
  have hEq (z : SourceInput p) :
      pathTest rate rewards C_star C_h control0 B z =
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceTest
          rate rewards C_star C_h control0
          (pathPullbackSet rate rewards C_star C_h B) z := by
    change (if (completeSuffixCode (rate := rate) rewards C_star C_h z,
        pastFibreOutput rate rewards C_star C_h control0 z) ∈ B then (1 : ℝ) else 0) = _
    rfl
  exact (ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceTest_integrable
    rate rewards C_star C_h control0 _ hB').congr
      (Filter.Eventually.of_forall fun z => (hEq z).symm)

private theorem pathSection_eq_originalSourceSection
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T)
    (a : Outcome p) (B : Set (PathOutputY p rate)) :
    pathSection rate rewards C_star C_h control0 u t a B =
      ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
        rate rewards C_star C_h control0 u t a
        (pathPullbackSet rate rewards C_star C_h B) := by
  funext z
  cases htheta : calendarParameters rate rewards C_star C_h t z with
  | none => simp [pathSection,
      ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection, htheta]
  | some theta =>
      simp only [pathSection,
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection, htheta]
      congr 1

theorem pathSection_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (a : Outcome p) (B : Set (PathOutputY p rate))
    (hB : MeasurableSet B) :
    Measurable (pathSection rate rewards C_star C_h control0 u t a B) := by
  rw [pathSection_eq_originalSourceSection (control0 := control0) (u := u) (t := t)
    (a := a) (B := B)]
  exact ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection_measurable
    rate rewards C_star C_h control0 u t a _
      (pathPullbackSet_measurable rate rewards C_star C_h B hB)

theorem pathSection_bounds (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (a : Outcome p) (B : Set (PathOutputY p rate))
    (hB : MeasurableSet B) (z : SourceInput p) :
    0 ≤ pathSection rate rewards C_star C_h control0 u t a B z ∧
      pathSection rate rewards C_star C_h control0 u t a B z ≤ 1 := by
  rw [pathSection_eq_originalSourceSection (control0 := control0) (u := u) (t := t)
    (a := a) (B := B)]
  exact ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection_bounds
    rate rewards C_star C_h control0 u t a _
      (pathPullbackSet_measurable rate rewards C_star C_h B hB) z

theorem pathSection_integrable (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (a : Outcome p) (B : Set (PathOutputY p rate))
    (hB : MeasurableSet B) :
    Integrable (pathSection rate rewards C_star C_h control0 u t a B)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  rw [pathSection_eq_originalSourceSection (control0 := control0) (u := u) (t := t)
    (a := a) (B := B)]
  exact ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection_integrable
    rate rewards C_star C_h control0 u t a _
      (pathPullbackSet_measurable rate rewards C_star C_h B hB)

theorem calendarOutput_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (b : Fin p.T) : Measurable (calendarOutput rate rewards C_star C_h control0 b) := by
  exact (ReferenceCalendarActualControlCallbackSections.measurable_codeAt
    rate rewards C_star C_h b).prodMk
      (ReferenceFirstCollectionPastSamplerFibreLaw.pastFibreOutput_measurable
        rate rewards C_star C_h control0)

theorem calendarTest_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (b : Fin p.T) (B : Set (CalendarOutputY p rate)) (hB : MeasurableSet B) :
    Measurable (calendarTest rate rewards C_star C_h control0 b B) :=
  (measurable_const.indicator hB).comp
    (calendarOutput_measurable rate rewards C_star C_h control0 b)

theorem calendarTest_integrable (control0 : ContinuousLearningRows.TimeControl p)
    (b : Fin p.T) (B : Set (CalendarOutputY p rate)) (hB : MeasurableSet B) :
    Integrable (calendarTest rate rewards C_star C_h control0 b B)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hB' := calendarPullbackSet_measurable rate rewards C_star C_h b B hB
  have hEq (z : SourceInput p) :
      calendarTest rate rewards C_star C_h control0 b B z =
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceTest
          rate rewards C_star C_h control0
          (calendarPullbackSet rate rewards C_star C_h b B) z := by
    change (if (codeAt rate rewards C_star C_h b z,
        pastFibreOutput rate rewards C_star C_h control0 z) ∈ B then (1 : ℝ) else 0) = _
    rfl
  exact (ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceTest_integrable
    rate rewards C_star C_h control0 _ hB').congr
      (Filter.Eventually.of_forall fun z => (hEq z).symm)

private theorem calendarSection_eq_originalSourceSection
    (control0 : ContinuousLearningRows.TimeControl p) (b u t : Fin p.T)
    (a : Outcome p) (B : Set (CalendarOutputY p rate)) :
    calendarSection rate rewards C_star C_h control0 b u t a B =
      ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
        rate rewards C_star C_h control0 u t a
        (calendarPullbackSet rate rewards C_star C_h b B) := by
  funext z
  cases htheta : calendarParameters rate rewards C_star C_h t z with
  | none => simp [calendarSection,
      ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection, htheta]
  | some theta =>
      simp only [calendarSection,
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection, htheta]
      congr 1

theorem calendarSection_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (b u t : Fin p.T) (a : Outcome p) (B : Set (CalendarOutputY p rate))
    (hB : MeasurableSet B) :
    Measurable (calendarSection rate rewards C_star C_h control0 b u t a B) := by
  rw [calendarSection_eq_originalSourceSection (control0 := control0) (b := b)
    (u := u) (t := t) (a := a) (B := B)]
  exact ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection_measurable
    rate rewards C_star C_h control0 u t a _
      (calendarPullbackSet_measurable rate rewards C_star C_h b B hB)

theorem calendarSection_bounds (control0 : ContinuousLearningRows.TimeControl p)
    (b u t : Fin p.T) (a : Outcome p) (B : Set (CalendarOutputY p rate))
    (hB : MeasurableSet B) (z : SourceInput p) :
    0 ≤ calendarSection rate rewards C_star C_h control0 b u t a B z ∧
      calendarSection rate rewards C_star C_h control0 b u t a B z ≤ 1 := by
  rw [calendarSection_eq_originalSourceSection (control0 := control0) (b := b)
    (u := u) (t := t) (a := a) (B := B)]
  exact ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection_bounds
    rate rewards C_star C_h control0 u t a _
      (calendarPullbackSet_measurable rate rewards C_star C_h b B hB) z

theorem calendarSection_integrable (control0 : ContinuousLearningRows.TimeControl p)
    (b u t : Fin p.T) (a : Outcome p) (B : Set (CalendarOutputY p rate))
    (hB : MeasurableSet B) :
    Integrable (calendarSection rate rewards C_star C_h control0 b u t a B)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  rw [calendarSection_eq_originalSourceSection (control0 := control0) (b := b)
    (u := u) (t := t) (a := a) (B := B)]
  exact ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection_integrable
    rate rewards C_star C_h control0 u t a _
      (calendarPullbackSet_measurable rate rewards C_star C_h b B hB)

/-- The single-cell law for the actual suffix and the original marked fibre.
Every outcome, including `none` and zero-mass fibres, remains in the sum. -/
theorem path_cell_integral (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (B : Set (PathOutputY p rate)) (hB : MeasurableSet B) :
    (∫ z in firstCell rate rewards C_star C_h u t,
      pathTest rate rewards C_star C_h control0 B z
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
      ∑ a : Outcome p, ∫ z in firstCell rate rewards C_star C_h u t,
        pathSection rate rewards C_star C_h control0 u t a B z
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let B' := pathPullbackSet rate rewards C_star C_h B
  have hB' := pathPullbackSet_measurable rate rewards C_star C_h B hB
  have htest (z : SourceInput p) :
      pathTest rate rewards C_star C_h control0 B z =
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceTest
          rate rewards C_star C_h control0 B' z := by
    change (if (completeSuffixCode (rate := rate) rewards C_star C_h z,
        pastFibreOutput rate rewards C_star C_h control0 z) ∈ B then (1 : ℝ) else 0) = _
    rfl
  have hsection (a : Outcome p) (z : SourceInput p) :
      pathSection rate rewards C_star C_h control0 u t a B z =
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
          rate rewards C_star C_h control0 u t a B' z := by
    exact congrFun (pathSection_eq_originalSourceSection (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0)
      (u := u) (t := t) (a := a) (B := B)) z
  calc
    _ = ∫ z in firstCell rate rewards C_star C_h u t,
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceTest
          rate rewards C_star C_h control0 B' z
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall htest
    _ = ∑ a : Outcome p, ∫ z in firstCell rate rewards C_star C_h u t,
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
          rate rewards C_star C_h control0 u t a B' z
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p :=
      ReferenceFirstCollectionOriginalSourceFibreTransport.originalSource_cell_integral
        rate rewards C_star C_h control0 u t B' hB'
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => (hsection a z).symm

/-- Full Borel test law. The no-call term is the actual restricted integral;
all original first-call cells and all outcomes are retained. -/
theorem path_borel_test_law (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (PathOutputY p rate)) (hB : MeasurableSet B) :
    (∫ z, pathTest rate rewards C_star C_h control0 B z
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
      (∫ z in ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h,
        B.indicator (fun _ => (1 : ℝ))
          (completeSuffixCode (rate := rate) rewards C_star C_h z, none)
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p) +
      ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
        ∫ z in firstCell rate rewards C_star C_h u t,
          pathSection rate rewards C_star C_h control0 u t a B z
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let B' := pathPullbackSet rate rewards C_star C_h B
  have hB' := pathPullbackSet_measurable rate rewards C_star C_h B hB
  have htest (z : SourceInput p) :
      pathTest rate rewards C_star C_h control0 B z =
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceTest
          rate rewards C_star C_h control0 B' z := by
    change (if (completeSuffixCode (rate := rate) rewards C_star C_h z,
        pastFibreOutput rate rewards C_star C_h control0 z) ∈ B then (1 : ℝ) else 0) = _
    rfl
  have hnone (z : SourceInput p) :
      B'.indicator (fun _ => (1 : ℝ)) (z, none) =
        B.indicator (fun _ => (1 : ℝ))
          (completeSuffixCode (rate := rate) rewards C_star C_h z, none) := by
    change (if (completeSuffixCode (rate := rate) rewards C_star C_h z, none) ∈ B
      then (1 : ℝ) else 0) = _
    rfl
  have hsection (u t : Fin p.T) (a : Outcome p) (z : SourceInput p) :
      pathSection rate rewards C_star C_h control0 u t a B z =
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
          rate rewards C_star C_h control0 u t a B' z := by
    exact congrFun (pathSection_eq_originalSourceSection (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0)
      (u := u) (t := t) (a := a) (B := B)) z
  calc
    _ = ∫ z, ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceTest
        rate rewards C_star C_h control0 B' z
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall htest
    _ = (∫ z in ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h,
        B'.indicator (fun _ => (1 : ℝ)) (z, none)
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p) +
        ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
          ∫ z in firstCell rate rewards C_star C_h u t,
            ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
              rate rewards C_star C_h control0 u t a B' z
            ∂BootstrapPrivateRoundStreams.sourceInputLaw p :=
      ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceOutput_borel_test_law
        rate rewards C_star C_h control0 B' hB'
    _ = _ := by
      have hnoneInt :
          (∫ z in ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
              rate rewards C_star C_h,
            B'.indicator (fun _ => (1 : ℝ)) (z, none)
            ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
            ∫ z in ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
              rate rewards C_star C_h,
              B.indicator (fun _ => (1 : ℝ))
                (completeSuffixCode (rate := rate) rewards C_star C_h z, none)
              ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hnone
      have hsum :
          (∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
            ∫ z in firstCell rate rewards C_star C_h u t,
              ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
                rate rewards C_star C_h control0 u t a B' z
              ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
          ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
            ∫ z in firstCell rate rewards C_star C_h u t,
              pathSection rate rewards C_star C_h control0 u t a B z
              ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro t ht
        apply Finset.sum_congr rfl
        intro a ha
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => (hsection u t a z).symm
      rw [hnoneInt, hsum]

/-- The fixed-calendar single-cell law, at the same date `b` on every
invocation cell. -/
theorem calendar_cell_integral (control0 : ContinuousLearningRows.TimeControl p)
    (b u t : Fin p.T) (B : Set (CalendarOutputY p rate)) (hB : MeasurableSet B) :
    (∫ z in firstCell rate rewards C_star C_h u t,
      calendarTest rate rewards C_star C_h control0 b B z
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
      ∑ a : Outcome p, ∫ z in firstCell rate rewards C_star C_h u t,
        calendarSection rate rewards C_star C_h control0 b u t a B z
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let B' := calendarPullbackSet rate rewards C_star C_h b B
  have hB' := calendarPullbackSet_measurable rate rewards C_star C_h b B hB
  have htest (z : SourceInput p) :
      calendarTest rate rewards C_star C_h control0 b B z =
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceTest
          rate rewards C_star C_h control0 B' z := by
    change (if (codeAt rate rewards C_star C_h b z,
        pastFibreOutput rate rewards C_star C_h control0 z) ∈ B then (1 : ℝ) else 0) = _
    rfl
  have hsection (a : Outcome p) (z : SourceInput p) :
      calendarSection rate rewards C_star C_h control0 b u t a B z =
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
          rate rewards C_star C_h control0 u t a B' z := by
    exact congrFun (calendarSection_eq_originalSourceSection (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0) (b := b)
      (u := u) (t := t) (a := a) (B := B)) z
  calc
    _ = ∫ z in firstCell rate rewards C_star C_h u t,
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceTest
          rate rewards C_star C_h control0 B' z
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall htest
    _ = ∑ a : Outcome p, ∫ z in firstCell rate rewards C_star C_h u t,
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
          rate rewards C_star C_h control0 u t a B' z
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p :=
      ReferenceFirstCollectionOriginalSourceFibreTransport.originalSource_cell_integral
        rate rewards C_star C_h control0 u t B' hB'
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => (hsection a z).symm

/-- Full fixed-calendar Borel test law with the original no-call restriction
and complete sum over the original invocation tags and sampler outcomes. -/
theorem calendar_borel_test_law (control0 : ContinuousLearningRows.TimeControl p)
    (b : Fin p.T) (B : Set (CalendarOutputY p rate)) (hB : MeasurableSet B) :
    (∫ z, calendarTest rate rewards C_star C_h control0 b B z
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
      (∫ z in ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h,
        B.indicator (fun _ => (1 : ℝ))
          (codeAt rate rewards C_star C_h b z, none)
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p) +
      ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
        ∫ z in firstCell rate rewards C_star C_h u t,
          calendarSection rate rewards C_star C_h control0 b u t a B z
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let B' := calendarPullbackSet rate rewards C_star C_h b B
  have hB' := calendarPullbackSet_measurable rate rewards C_star C_h b B hB
  have htest (z : SourceInput p) :
      calendarTest rate rewards C_star C_h control0 b B z =
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceTest
          rate rewards C_star C_h control0 B' z := by
    change (if (codeAt rate rewards C_star C_h b z,
        pastFibreOutput rate rewards C_star C_h control0 z) ∈ B then (1 : ℝ) else 0) = _
    rfl
  have hnone (z : SourceInput p) :
      B'.indicator (fun _ => (1 : ℝ)) (z, none) =
        B.indicator (fun _ => (1 : ℝ))
          (codeAt rate rewards C_star C_h b z, none) := by
    change (if (codeAt rate rewards C_star C_h b z, none) ∈ B
      then (1 : ℝ) else 0) = _
    rfl
  have hsection (u t : Fin p.T) (a : Outcome p) (z : SourceInput p) :
      calendarSection rate rewards C_star C_h control0 b u t a B z =
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
          rate rewards C_star C_h control0 u t a B' z := by
    exact congrFun (calendarSection_eq_originalSourceSection (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (control0 := control0) (b := b)
      (u := u) (t := t) (a := a) (B := B)) z
  calc
    _ = ∫ z, ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceTest
        rate rewards C_star C_h control0 B' z
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall htest
    _ = (∫ z in ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h,
        B'.indicator (fun _ => (1 : ℝ)) (z, none)
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p) +
        ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
          ∫ z in firstCell rate rewards C_star C_h u t,
            ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
              rate rewards C_star C_h control0 u t a B' z
            ∂BootstrapPrivateRoundStreams.sourceInputLaw p :=
      ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceOutput_borel_test_law
        rate rewards C_star C_h control0 B' hB'
    _ = _ := by
      have hnoneInt :
          (∫ z in ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
              rate rewards C_star C_h,
            B'.indicator (fun _ => (1 : ℝ)) (z, none)
            ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
            ∫ z in ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
              rate rewards C_star C_h,
              B.indicator (fun _ => (1 : ℝ))
                (codeAt rate rewards C_star C_h b z, none)
              ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hnone
      have hsum :
          (∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
            ∫ z in firstCell rate rewards C_star C_h u t,
              ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
                rate rewards C_star C_h control0 u t a B' z
              ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
          ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
            ∫ z in firstCell rate rewards C_star C_h u t,
              calendarSection rate rewards C_star C_h control0 b u t a B z
              ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro t ht
        apply Finset.sum_congr rfl
        intro a ha
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => (hsection u t a z).symm
      rw [hnoneInt, hsum]

/-- The calendar code is the optional record at its actual physical suffix
offset. Before launch the value is genuinely absent. -/
theorem calendarCode_eq_suffixLookup (b : Fin p.T) (z : SourceInput p) :
    codeAt rate rewards C_star C_h b z =
      if ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ b.val
      then (completeSuffixCode (rate := rate) rewards C_star C_h z)[
        b.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]?
      else none := by
  by_cases hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h ≤ b.val
  · simp [ReferenceCalendarActualControlCallbackSections.codeAt,
      ReferenceSourcePrefixHistoryFiltration.actualRecord,
      ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode, hstart]
  · simp [ReferenceCalendarActualControlCallbackSections.codeAt,
      ReferenceSourcePrefixHistoryFiltration.actualRecord, hstart]

/-- The fixed date is absent before the actual suffix begins, including no
launch and terminal-launch paths. -/
theorem calendarCode_none_before_start (b : Fin p.T) (z : SourceInput p)
    (hstart : b.val < ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h) :
    codeAt rate rewards C_star C_h b z = none := by
  rw [calendarCode_eq_suffixLookup rate rewards C_star C_h b z]
  simp [Nat.not_le_of_gt hstart]

/-- Every calendar date at or after the physical start has the corresponding
actual suffix record; no record is supplied by a replay or padding branch. -/
theorem calendarCode_some_at_or_after_start (b : Fin p.T) (z : SourceInput p)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ b.val) :
    (codeAt rate rewards C_star C_h b z).isSome := by
  rw [calendarCode_eq_suffixLookup rate rewards C_star C_h b z]
  have hlen := ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode_length
    (rate := rate) rewards C_star C_h z
  have hindex : b.val - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h <
        (completeSuffixCode (rate := rate) rewards C_star C_h z).length := by
    rw [hlen]
    have hb := b.isLt
    omega
  simp [hstart, List.getElem?_eq_getElem hindex]

/-- The actual-date code is present exactly on dates in the physical suffix. -/
theorem calendarCode_isSome_iff_at_or_after_start (b : Fin p.T) (z : SourceInput p) :
    (codeAt rate rewards C_star C_h b z).isSome ↔
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ b.val := by
  constructor
  · intro h
    by_contra hstart
    have hnone := calendarCode_none_before_start rate rewards C_star C_h b z
      (Nat.lt_of_not_ge hstart)
    rw [hnone] at h
    simp at h
  · exact calendarCode_some_at_or_after_start rate rewards C_star C_h b z

/-- A present fixed-date code carries its genuine calendar label `b`, whether
the invocation date is before or after `b`. -/
theorem calendarCode_label (b : Fin p.T) (z : SourceInput p)
    (code : RoundRecordCode p rate)
    (hcode : codeAt rate rewards C_star C_h b z = some code) :
    code.1 = b.val := by
  unfold ReferenceCalendarActualControlCallbackSections.codeAt at hcode
  cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h b z with
  | none => simp [hrecord] at hcode
  | some record =>
      have hrecordTime : record.input.time.val = b.val := by
        unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hrecord
        by_cases hstart : ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h ≤ b.val
        · simp only [ite_eq_left hstart] at hrecord
          obtain ⟨hindex, hget⟩ := List.getElem?_eq_some_iff.mp hrecord
          have hindex' : b.val -
              ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
                p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
            have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
              rate z rewards C_star C_h
            rw [hlen] at hindex
            exact hindex
          have htimes := congrArg
            (fun xs : List ℕ => xs[b.val -
              ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]?)
            (ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
              rate z rewards C_star C_h)
          simp only [List.getElem?_map] at htimes
          rw [List.getElem?_eq_getElem hindex, hget] at htimes
          simp only [Option.map_some] at htimes
          simp only [ReferenceActivePhysicalHorizon.calendar,
            List.getElem?_range' hindex', Nat.one_mul] at htimes
          have htime := Option.some.inj htimes
          omega
        · simp only [ite_eq_right hstart] at hrecord
          cases hrecord
      have hcode' : ReferenceActiveHorizonMeasurability.roundRecordCode record = code := by
        simpa [hrecord] using hcode
      calc
        code.1 = (ReferenceActiveHorizonMeasurability.roundRecordCode record).1 :=
          (congrArg Prod.fst hcode').symm
        _ = record.input.time.val := rfl
        _ = b.val := hrecordTime

/-- Replacing a later control leaves the earlier literal calendar code alone.
This handles the `b < t` branch without dropping the fixed-date observation. -/
theorem calendarCode_unchanged_by_later_control
    (control0 : ContinuousLearningRows.TimeControl p) (b t : Fin p.T)
    (z : SourceInput p) (c : ContinuousLearningRows.TimeControl p)
    (hbt : b.val < t.val) :
    codeAt rate rewards C_star C_h b
        (replaceSourceControl p t z c) = codeAt rate rewards C_star C_h b z := by
  have hpref : sourcePrefix control0 (b.val + 1)
        (replaceSourceControl p t z c) = sourcePrefix control0 (b.val + 1) z := by
    calc
      _ = sourcePrefix control0 (b.val + 1)
          (sourcePrefix control0 t.val (replaceSourceControl p t z c)) := by
        symm
        exact ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
          control0 (b.val + 1) t.val (by omega) (replaceSourceControl p t z c)
      _ = sourcePrefix control0 (b.val + 1) (sourcePrefix control0 t.val z) := by
        rw [ReferenceFirstCollectionOriginalSourceFibreTransport.sourcePrefix_replaceSourceControl
          control0 t z c]
      _ = sourcePrefix control0 (b.val + 1) z :=
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
          control0 (b.val + 1) t.val (by omega) z
  calc
    _ = codeAt rate rewards C_star C_h b
        (sourcePrefix control0 (b.val + 1)
          (replaceSourceControl p t z c)) :=
      ReferenceCalendarActualControlCallbackSections.codeAt_successor_factor
        rate rewards C_star C_h control0 b (replaceSourceControl p t z c)
    _ = codeAt rate rewards C_star C_h b (sourcePrefix control0 (b.val + 1) z) := by
      rw [hpref]
    _ = codeAt rate rewards C_star C_h b z :=
      (ReferenceCalendarActualControlCallbackSections.codeAt_successor_factor
        rate rewards C_star C_h control0 b z).symm

/-- Both literal outputs use the same source-generated suffix: the path map
encodes every actual record, while the calendar map selects its real physical
offset and preserves the common first-call mark. -/
theorem literal_outputs_share_actual_suffix
    (control0 : ContinuousLearningRows.TimeControl p) (b : Fin p.T)
    (z : SourceInput p) :
    (pathOutput rate rewards C_star C_h control0 z).1 =
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).map
          (ReferenceActiveHorizonMeasurability.roundRecordCode
            (p := p) (rate := rate)) ∧
    ((calendarOutput rate rewards C_star C_h control0 b z).1 =
        (if ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ b.val
        then ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).map
            (ReferenceActiveHorizonMeasurability.roundRecordCode
              (p := p) (rate := rate)))[
            b.val - ReferenceCompletePhysicalHistory.physicalStart
              rate z rewards C_star C_h]?
        else none)) ∧
      (pathOutput rate rewards C_star C_h control0 z).2 =
        (calendarOutput rate rewards C_star C_h control0 b z).2 ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).map
          (fun record => record.input.time.val) =
        ReferenceActivePhysicalHorizon.calendar
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) := by
  constructor
  · rfl
  · constructor
    · change codeAt rate rewards C_star C_h b z = _
      simpa only [completeSuffixCode, List.getElem?_map] using
        calendarCode_eq_suffixLookup rate rewards C_star C_h b z
    · constructor
      · rfl
      · exact ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
          rate z rewards C_star C_h

/-- The canonical code of each actual record reconstructs its own input
state, actions, feedback, coordinator/follower observations, successor, and
own entries by the established whole-step reconstruction APIs. -/
theorem actualRecord_code_reconstructs
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    (ReferenceActiveHorizonMeasurability.roundRecordCode record).1 =
        record.input.time.val ∧
      ReferenceActivePhysicalStepMeasurability.decodeState
        (ReferenceActiveHorizonMeasurability.roundRecordCode record).2.1 =
          record.input.state ∧
      ReferenceActiveHorizonMeasurability.roundRecordCodeActions
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) = record.actions ∧
      ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) = record.gridFeedback ∧
      ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
        (ReferenceActiveHorizonMeasurability.roundRecordCode record).2.2.1.2.2.2.2 =
          record.coordinatorDiagnostics ∧
      (∀ i, ReferenceFollowerTailComposition.reconstructFollowerObservable
        ((ReferenceActiveHorizonMeasurability.roundRecordCode record).2.2.2.1 i) =
          record.followerDiagnostics i) ∧
      ReferenceActivePhysicalStepMeasurability.decodeState
        (ReferenceActiveHorizonMeasurability.roundRecordCode record).2.2.2.2 =
          record.output.next ∧
      (∀ player, ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) player =
          record.ownEntries player) := by
  obtain ⟨hstate, hcoord, hfollowers, hsuccessor, hentries⟩ :=
    ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs record
  obtain ⟨hselection, hdown, hactions, hfeedback⟩ :=
    ReferenceActiveHorizonMeasurability.roundRecordCode_front record
  exact ⟨rfl, hstate, hactions, hfeedback, hcoord, hfollowers, hsuccessor, hentries⟩

/-- A present calendar observation is reconstructed from its actual suffix
record at the physical offset, with the canonical whole-step code. -/
theorem calendarCode_reconstructs_actual_record (b : Fin p.T) (z : SourceInput p)
    (code : RoundRecordCode p rate)
    (hcode : codeAt rate rewards C_star C_h b z = some code) :
    ∃ record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h b z =
        some record ∧
      code = ReferenceActiveHorizonMeasurability.roundRecordCode record ∧
      (ReferenceActiveHorizonMeasurability.roundRecordCode record).1 = b.val ∧
      ReferenceActivePhysicalStepMeasurability.decodeState
        (ReferenceActiveHorizonMeasurability.roundRecordCode record).2.1 =
          record.input.state ∧
      ReferenceActiveHorizonMeasurability.roundRecordCodeActions
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) = record.actions ∧
      ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) = record.gridFeedback ∧
      ReferenceActivePhysicalStepMeasurability.decodeState
        (ReferenceActiveHorizonMeasurability.roundRecordCode record).2.2.2.2 =
          record.output.next := by
  cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h b z with
  | none =>
      simp [ReferenceCalendarActualControlCallbackSections.codeAt, hrecord] at hcode
  | some record =>
      have hcode' : code = ReferenceActiveHorizonMeasurability.roundRecordCode record := by
        have heq : ReferenceActiveHorizonMeasurability.roundRecordCode record = code := by
          simpa [ReferenceCalendarActualControlCallbackSections.codeAt, hrecord] using hcode
        exact heq.symm
      obtain ⟨_, hstate, hactions, hfeedback, _, _, hsuccessor, _⟩ :=
        actualRecord_code_reconstructs rate record
      refine ⟨record, rfl, hcode', ?_, hstate, hactions, hfeedback, hsuccessor⟩
      · calc
          (ReferenceActiveHorizonMeasurability.roundRecordCode record).1 = code.1 :=
            (congrArg Prod.fst hcode').symm
          _ = b.val := calendarCode_label rate rewards C_star C_h b z code hcode

end Bandits.Support.ReferenceFirstCollectionPhysicalContinuationFibreLaw

end
