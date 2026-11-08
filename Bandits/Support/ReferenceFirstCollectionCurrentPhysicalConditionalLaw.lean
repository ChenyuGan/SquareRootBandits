/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionMarkedCurrentConditionalLaw
public import Bandits.Support.ReferenceFirstCollectionPhysicalContinuationFibreLaw

/-!
# One-invocation conditional law of the actual current physical round

This module projects the existing marked-current law to the actual optional
physical record code together with its full marked current payload. The code
is rebuilt from the strict source prefix and the complete current control, so
the projection keeps the actual chronological round and all its present or
absent branches.

Sources: `06_interruptions.tex:391-426` and
`appendix_b_communication.tex:25-58`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Bandits.Support.ReferenceFirstCollectionCurrentPhysicalConditionalLaw

open ReferenceFirstCollectionMarkedCurrentConditionalLaw
  (SourceInput MarkedCurrentPair)
open ReferenceFirstCollectionPhysicalContinuationFibreLaw (RoundRecordCode)
open BootstrapPrivateRoundStreams (sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceCalendarLaterSamplerPredictability (calendarParameters)
open AssignmentParameterFibreKernel (Outcome AssignmentVector fibreMass fibreMeasure)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix sourcePrefixFiltration)
open ReferenceSourceCurrentControlFreshness (u_t)
open ReferenceFixedTimeSourceControlCoupling (replaceSourceControl)
open ReferenceLaterOptionalControlResampling (ControlRemainder controlRemainderLaw)
open LaunchAssignmentCoordinateSplit (controlAssignmentSplitEquiv)

local instance sourceInputMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
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

/-- The actual optional current-round record code paired with the full marked
current physical payload. -/
abbrev PhysicalCurrentY (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Option (RoundRecordCode p rate) × MarkedCurrentPair p

/-- Rebuild the canonical current physical code from a marked pair's strict
past and complete current control, retaining the pair itself. -/
def reconstructCurrentPhysical (t : Fin p.T) (q : MarkedCurrentPair p) :
    PhysicalCurrentY rate :=
  (ReferenceCalendarActualControlCallbackSections.codeAt rate rewards C_star C_h t
      (replaceSourceControl p t q.1 ((controlAssignmentSplitEquiv p).symm q.2.2)), q)

/-- The actual one-invocation physical round: canonical optional record code
and the exact actual marked-current pair. -/
def physicalCurrent (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) : PhysicalCurrentY rate :=
  (ReferenceCalendarActualControlCallbackSections.codeAt rate rewards C_star C_h t z,
    ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentPair
      rate rewards C_star C_h control0 t z)

/-- Pull a Borel physical-current test back along its literal reconstruction
map on the marked-current carrier. -/
def physicalMarkPreimage (t : Fin p.T) (B : Set (PhysicalCurrentY rate)) :
    Set (MarkedCurrentPair p) :=
  (reconstructCurrentPhysical rate rewards C_star C_h t) ⁻¹' B

/-- The Borel reconstruction map on the original continuous measurable
structures. -/
theorem reconstructCurrentPhysical_measurable (t : Fin p.T) :
    Measurable (reconstructCurrentPhysical rate rewards C_star C_h t) := by
  have hsplit : Measurable (fun q : MarkedCurrentPair p =>
      (controlAssignmentSplitEquiv p).symm q.2.2) :=
    (controlAssignmentSplitEquiv p).symm.measurable.comp
      (measurable_snd.comp measurable_snd)
  have hinput : Measurable (fun q : MarkedCurrentPair p => (q.1,
      (controlAssignmentSplitEquiv p).symm q.2.2)) :=
    measurable_fst.prodMk hsplit
  have hreplace : Measurable (fun q : MarkedCurrentPair p =>
      replaceSourceControl p t q.1 ((controlAssignmentSplitEquiv p).symm q.2.2)) :=
    (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
      hinput
  have hcode :=
    (ReferenceCalendarActualControlCallbackSections.measurable_codeAt
      rate rewards C_star C_h t).comp hreplace
  exact hcode.prodMk measurable_id

/-- Pulling back a Borel physical-current set remains Borel. -/
theorem physicalMarkPreimage_measurable (t : Fin p.T)
    (B : Set (PhysicalCurrentY rate)) (hB : MeasurableSet B) :
    MeasurableSet (physicalMarkPreimage rate rewards C_star C_h t B) :=
  reconstructCurrentPhysical_measurable rate rewards C_star C_h t hB

/-- Every original source point reconstructs its actual current code from
the strict past and the full current-control split. -/
theorem reconstructCurrentPhysical_markedCurrentPair (control0 : TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    reconstructCurrentPhysical rate rewards C_star C_h t
        (ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentPair
          rate rewards C_star C_h control0 t z) =
      physicalCurrent rate rewards C_star C_h control0 t z := by
  have hcoordinates :
      (ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentPair
        rate rewards C_star C_h control0 t z).2.2 =
        controlAssignmentSplitEquiv p (u_t p t z) := by
    rfl
  have hcontrol :
      (controlAssignmentSplitEquiv p).symm
          (ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentPair
            rate rewards C_star C_h control0 t z).2.2 = u_t p t z := by
    rw [hcoordinates]
    exact (controlAssignmentSplitEquiv p).symm_apply_apply _
  have hrestore :
      replaceSourceControl p t (sourcePrefix control0 t.val z) (u_t p t z) =
        sourcePrefix control0 (t.val + 1) z := by
    have hcurrent : u_t p t z =
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t) := rfl
    rw [hcurrent]
    exact (ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore
      control0 t z).symm
  change
    (ReferenceCalendarActualControlCallbackSections.codeAt rate rewards C_star C_h t
        (replaceSourceControl p t (sourcePrefix control0 t.val z)
          ((controlAssignmentSplitEquiv p).symm
            (ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentPair
              rate rewards C_star C_h control0 t z).2.2)),
      ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentPair
        rate rewards C_star C_h control0 t z) =
      (ReferenceCalendarActualControlCallbackSections.codeAt rate rewards C_star C_h t z,
        ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentPair
          rate rewards C_star C_h control0 t z)
  congr 1
  rw [hcontrol, hrestore]
  exact (ReferenceCalendarActualControlCallbackSections.codeAt_successor_factor
    rate rewards C_star C_h control0 t z).symm

/-- The tested current physical output is Borel on the original source. -/
theorem physicalCurrent_measurable (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (physicalCurrent rate rewards C_star C_h control0 t) := by
  exact (ReferenceCalendarActualControlCallbackSections.measurable_codeAt
      rate rewards C_star C_h t).prodMk
    (ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentPair_measurable
      rate rewards C_star C_h control0 t)

/-- The physical-current code is exactly the canonical optional code of the
actual record at calendar date `t`, including all absent branches. -/
theorem physicalCurrent_code_eq_actualRecord (control0 : TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    (physicalCurrent rate rewards C_star C_h control0 t z).1 =
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
        ReferenceActiveHorizonMeasurability.roundRecordCode := rfl

/-- On the present branch, the actual code names the same actual record and
retains its input state, actions, feedback, coordinator and follower
diagnostics, successor state, and own observations. -/
theorem physicalCurrent_present_code_reconstructs_actual_record
    (control0 : TimeControl p) (t : Fin p.T) (z : SourceInput p)
    (code : RoundRecordCode p rate)
    (hcode : (physicalCurrent rate rewards C_star C_h control0 t z).1 = some code) :
    ∃ record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some record ∧
      code = ReferenceActiveHorizonMeasurability.roundRecordCode record ∧
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
  have hcanonical :
      ReferenceCalendarActualControlCallbackSections.codeAt rate rewards C_star C_h t z =
        some code := by
    exact hcode
  obtain ⟨record, hrecord, hcode', _, _, _, _, _⟩ :=
    ReferenceFirstCollectionPhysicalContinuationFibreLaw.calendarCode_reconstructs_actual_record
      rate rewards C_star C_h t z code hcanonical
  obtain ⟨hlabel, hstate, hactions, hfeedback, hcoordinator, hfollowers,
      hsuccessor, hentries⟩ :=
    ReferenceFirstCollectionPhysicalContinuationFibreLaw.actualRecord_code_reconstructs
      rate record
  exact ⟨record, hrecord, hcode', hlabel, hstate, hactions, hfeedback,
    hcoordinator, hfollowers, hsuccessor, hentries⟩

/-- The Borel indicator of the entire actual current physical output. -/
def physicalCurrentTest (control0 : TimeControl p) (t : Fin p.T)
    (B : Set (PhysicalCurrentY rate)) (z : SourceInput p) : ℝ :=
  B.indicator (fun _ => (1 : ℝ))
    (physicalCurrent rate rewards C_star C_h control0 t z)

/-- The current-output test is Borel for every Borel output set. -/
theorem physicalCurrentTest_measurable (control0 : TimeControl p) (t : Fin p.T)
    (B : Set (PhysicalCurrentY rate)) (hB : MeasurableSet B) :
    Measurable (physicalCurrentTest rate rewards C_star C_h control0 t B) :=
  (measurable_const.indicator hB).comp
    (physicalCurrent_measurable rate rewards C_star C_h control0 t)

/-- The current-output indicator is bounded by one and nonnegative. -/
theorem physicalCurrentTest_bounds (control0 : TimeControl p) (t : Fin p.T)
    (B : Set (PhysicalCurrentY rate)) (z : SourceInput p) :
    0 ≤ physicalCurrentTest rate rewards C_star C_h control0 t B z ∧
      physicalCurrentTest rate rewards C_star C_h control0 t B z ≤ 1 := by
  by_cases hz : physicalCurrent rate rewards C_star C_h control0 t z ∈ B <;>
    simp [physicalCurrentTest, Set.indicator, hz]

/-- Integrability of a Borel current-output test under the entire original
source law. -/
theorem physicalCurrentTest_integrable (control0 : TimeControl p) (t : Fin p.T)
    (B : Set (PhysicalCurrentY rate)) (hB : MeasurableSet B) :
    Integrable (physicalCurrentTest rate rewards C_star C_h control0 t B)
      (sourceInputLaw p) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((physicalCurrentTest_measurable rate rewards C_star C_h control0 t B hB).aestronglyMeasurable)
  filter_upwards [] with z
  obtain ⟨h0, h1⟩ := physicalCurrentTest_bounds rate rewards C_star C_h control0 t B z
  change ‖physicalCurrentTest rate rewards C_star C_h control0 t B z‖ ≤ 1
  rw [Real.norm_of_nonneg h0]
  exact h1

/-- The unnormalised section for an actual current outcome and physical test.
It is definitionally the marked-current section on the exact
preimage under `reconstructCurrentPhysical`. -/
def physicalCurrentSection (control0 : TimeControl p) (t : Fin p.T)
    (a : Outcome p) (B : Set (PhysicalCurrentY rate)) (z : SourceInput p) : ℝ :=
  ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentSection
    rate rewards C_star C_h control0 t a
    (physicalMarkPreimage rate rewards C_star C_h t B) z

/-- Literal expansion of the physical section: the code and complete marked
current payload are evaluated on the same replacement source. -/
theorem physicalCurrentSection_eq_explicit (control0 : TimeControl p)
    (t : Fin p.T) (a : Outcome p) (B : Set (PhysicalCurrentY rate))
    (z : SourceInput p) :
    physicalCurrentSection rate rewards C_star C_h control0 t a B z =
      match calendarParameters rate rewards C_star C_h t z with
      | none => 0
      | some theta => (fibreMass p theta a).toReal *
          ∫ vw : AssignmentParameterFibreKernel.AssignmentVector p × ControlRemainder p,
            B.indicator (fun _ => (1 : ℝ))
              (ReferenceCalendarActualControlCallbackSections.codeAt rate rewards C_star C_h t
                  (replaceSourceControl p t (sourcePrefix control0 t.val z)
                    ((controlAssignmentSplitEquiv p).symm vw)),
                (sourcePrefix control0 t.val z, (some a, vw)))
            ∂(fibreMeasure p theta a).prod (controlRemainderLaw p) := by
  cases htheta : calendarParameters rate rewards C_star C_h t z with
  | none =>
      simp only [physicalCurrentSection,
        ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentSection, htheta]
  | some theta =>
      simp only [physicalCurrentSection,
        ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentSection, htheta]
      congr 1

/-- Each physical section is Borel in the original continuous source space. -/
theorem physicalCurrentSection_measurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Outcome p) (B : Set (PhysicalCurrentY rate))
    (hB : MeasurableSet B) :
    Measurable (physicalCurrentSection rate rewards C_star C_h control0 t a B) := by
  exact ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentSection_measurable
    rate rewards C_star C_h control0 u t a
    (physicalMarkPreimage rate rewards C_star C_h t B)
    (physicalMarkPreimage_measurable rate rewards C_star C_h t B hB)

/-- Each unnormalised physical section keeps the marked-current `[0,1]`
bounds, including zero-mass fibres. -/
theorem physicalCurrentSection_bounds (control0 : TimeControl p)
    (u t : Fin p.T) (a : Outcome p) (B : Set (PhysicalCurrentY rate))
    (hB : MeasurableSet B) (z : SourceInput p) :
    0 ≤ physicalCurrentSection rate rewards C_star C_h control0 t a B z ∧
      physicalCurrentSection rate rewards C_star C_h control0 t a B z ≤ 1 := by
  exact ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentSection_bounds
    rate rewards C_star C_h control0 u t a
    (physicalMarkPreimage rate rewards C_star C_h t B)
    (physicalMarkPreimage_measurable rate rewards C_star C_h t B hB) z

/-- Every physical section is integrable under the original source law. -/
theorem physicalCurrentSection_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Outcome p) (B : Set (PhysicalCurrentY rate))
    (hB : MeasurableSet B) :
    Integrable (physicalCurrentSection rate rewards C_star C_h control0 t a B)
      (sourceInputLaw p) := by
  exact ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentSection_integrable
    rate rewards C_star C_h control0 u t a
    (physicalMarkPreimage rate rewards C_star C_h t B)
    (physicalMarkPreimage_measurable rate rewards C_star C_h t B hB)

/-- Each physical section is strongly measurable in exactly the successor
source-prefix field `H(t.val + 1)`. -/
theorem physicalCurrentSection_stronglyMeasurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Outcome p) (B : Set (PhysicalCurrentY rate))
    (hB : MeasurableSet B) :
    StronglyMeasurable[sourcePrefixFiltration control0 (t.val + 1)]
      (physicalCurrentSection rate rewards C_star C_h control0 t a B) := by
  exact ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentSection_stronglyMeasurable
    rate rewards C_star C_h control0 u t a
    (physicalMarkPreimage rate rewards C_star C_h t B)
    (physicalMarkPreimage_measurable rate rewards C_star C_h t B hB)

/-- The finite sum of all physical-outcome sections is strongly measurable in
exactly the successor source-prefix field. -/
theorem physicalCurrentSection_sum_stronglyMeasurable (control0 : TimeControl p)
    (u t : Fin p.T) (B : Set (PhysicalCurrentY rate)) (hB : MeasurableSet B) :
    StronglyMeasurable[sourcePrefixFiltration control0 (t.val + 1)]
      (fun z => ∑ a : Outcome p,
        physicalCurrentSection rate rewards C_star C_h control0 t a B z) := by
  exact ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentSection_sum_stronglyMeasurable
    rate rewards C_star C_h control0 u t
    (physicalMarkPreimage rate rewards C_star C_h t B)
    (physicalMarkPreimage_measurable rate rewards C_star C_h t B hB)

private theorem physicalCurrentTest_apply_eq_markedCurrentTest
    (control0 : TimeControl p) (t : Fin p.T) (B : Set (PhysicalCurrentY rate))
    (z : SourceInput p) :
    physicalCurrentTest rate rewards C_star C_h control0 t B z =
      ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentTest
        rate rewards C_star C_h control0 t
        (physicalMarkPreimage rate rewards C_star C_h t B) z := by
  simp only [physicalCurrentTest,
    ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentTest,
    Set.indicator, physicalMarkPreimage, Set.mem_preimage]
  rw [reconstructCurrentPhysical_markedCurrentPair]

private theorem physicalCurrentTest_eq_markedCurrentTest (control0 : TimeControl p)
    (t : Fin p.T) (B : Set (PhysicalCurrentY rate)) :
    physicalCurrentTest rate rewards C_star C_h control0 t B =
      ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentTest
        rate rewards C_star C_h control0 t
        (physicalMarkPreimage rate rewards C_star C_h t B) := by
  funext z
  exact physicalCurrentTest_apply_eq_markedCurrentTest
    rate rewards C_star C_h control0 t B z

private theorem physicalCurrentSection_eq_markedCurrentSection
    (control0 : TimeControl p) (t : Fin p.T) (a : Outcome p)
    (B : Set (PhysicalCurrentY rate)) (z : SourceInput p) :
    physicalCurrentSection rate rewards C_star C_h control0 t a B z =
      ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrentSection
        rate rewards C_star C_h control0 t a
        (physicalMarkPreimage rate rewards C_star C_h t B) z := rfl

/-- For every event in the exact successor source-prefix field, the
unnormalised first-cell set integrals agree with the finite sum of physical
sections. -/
theorem physicalCurrent_cell_setIntegral (control0 : TimeControl p)
    (u t : Fin p.T) (B : Set (PhysicalCurrentY rate)) (hB : MeasurableSet B)
    (A : Set (SourceInput p))
    (hA : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] A) :
    ∫ z in A,
        (firstCell rate rewards C_star C_h u t).indicator
          (physicalCurrentTest rate rewards C_star C_h control0 t B) z
      ∂sourceInputLaw p =
    ∫ z in A,
        (firstCell rate rewards C_star C_h u t).indicator
          (fun y => ∑ a : Outcome p,
            physicalCurrentSection rate rewards C_star C_h control0 t a B y) z
      ∂sourceInputLaw p := by
  simpa only [physicalCurrentTest_eq_markedCurrentTest rate rewards C_star C_h control0 t B,
    physicalCurrentSection_eq_markedCurrentSection rate rewards C_star C_h control0 t]
    using ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrent_cell_setIntegral
    rate rewards C_star C_h control0 u t
    (physicalMarkPreimage rate rewards C_star C_h t B)
    (physicalMarkPreimage_measurable rate rewards C_star C_h t B hB) A hA

/-- The corresponding total integral uses the marked-current total
integral identity, with every actual outcome retained. -/
theorem physicalCurrent_cell_integral (control0 : TimeControl p)
    (u t : Fin p.T) (B : Set (PhysicalCurrentY rate)) (hB : MeasurableSet B) :
    ∫ z in firstCell rate rewards C_star C_h u t,
        physicalCurrentTest rate rewards C_star C_h control0 t B z
      ∂sourceInputLaw p =
    ∑ a : Outcome p, ∫ z in firstCell rate rewards C_star C_h u t,
      physicalCurrentSection rate rewards C_star C_h control0 t a B z
      ∂sourceInputLaw p := by
  simpa only [physicalCurrentTest_eq_markedCurrentTest rate rewards C_star C_h control0 t B,
    physicalCurrentSection_eq_markedCurrentSection rate rewards C_star C_h control0 t]
    using ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrent_cell_integral
    rate rewards C_star C_h control0 u t
    (physicalMarkPreimage rate rewards C_star C_h t B)
    (physicalMarkPreimage_measurable rate rewards C_star C_h t B hB)

/-- The one-invocation conditional law of the actual physical current output
on the exact successor strict-past field, with the original possibly-zero
first-cell measure left unnormalised. -/
theorem physicalCurrent_cell_condExp (control0 : TimeControl p)
    (u t : Fin p.T) (B : Set (PhysicalCurrentY rate)) (hB : MeasurableSet B) :
    (sourceInputLaw p)[
      (firstCell rate rewards C_star C_h u t).indicator
        (physicalCurrentTest rate rewards C_star C_h control0 t B) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      (firstCell rate rewards C_star C_h u t).indicator
        (fun z => ∑ a : Outcome p,
          physicalCurrentSection rate rewards C_star C_h control0 t a B z) := by
  simpa only [physicalCurrentTest_eq_markedCurrentTest rate rewards C_star C_h control0 t B,
    physicalCurrentSection_eq_markedCurrentSection rate rewards C_star C_h control0 t]
    using ReferenceFirstCollectionMarkedCurrentConditionalLaw.markedCurrent_cell_condExp
    rate rewards C_star C_h control0 u t
    (physicalMarkPreimage rate rewards C_star C_h t B)
    (physicalMarkPreimage_measurable rate rewards C_star C_h t B hB)

end Bandits.Support.ReferenceFirstCollectionCurrentPhysicalConditionalLaw

end
