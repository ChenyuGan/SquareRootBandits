/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionSamplerOutputLaw
public import Bandits.Support.ReferenceCalendarLaterSamplerFibreMass

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# First actual collection-sampler full-vector finite-fibre law

This module retains the original first invocation, checked failure outcome,
and entire continuous assignment vector. Its strata are original and
unnormalized; the conditional identity stays in the original successor
source-prefix field.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical ENNReal BigOperators

namespace Bandits.Support.ReferenceFirstCollectionSamplerFibreLaw

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p

abbrev Outcome (p : ConstructorDimensions.Parameters) :=
  AssignmentParameterFibreKernel.Outcome p

abbrev AssignmentVector (p : ConstructorDimensions.Parameters) :=
  AssignmentParameterFibreKernel.AssignmentVector p

abbrev FibrePayload (p : ConstructorDimensions.Parameters) :=
  Option (Outcome p) × AssignmentVector p

abbrev Y (p : ConstructorDimensions.Parameters) :=
  Option (Fin p.T × (Fin p.T × FibrePayload p))

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

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

local instance fibrePayloadOptionMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (Option (Outcome p)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

private theorem measurableSet_option_singleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace] {a} := by
  let e := Equiv.optionEquivSumPUnit α
  have he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e :=
    comap_measurable _
  have hset : ({a} : Set (Option α)) = e ⁻¹' {e a} := by
    ext x
    exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e a with
  | inl value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inr_image (α := α)

local instance fibrePayloadOptionMeasurableSingletonClass
    (p : ConstructorDimensions.Parameters) :
    @MeasurableSingletonClass (Option (Outcome p))
      LaterAssignmentStartMeasurability.optionMeasurableSpace :=
  ⟨measurableSet_option_singleton⟩

private def codeSlow (p : ConstructorDimensions.Parameters)
    (code : LaterAssignmentStartMeasurability.LaterAssignmentStartCode p) :
    Outcome p :=
  match code with
  | .sampled outcome => CheckedAssignmentSample.successfulSlowSet p (.sampled outcome)
  | _ => none

private def projectOutput (p : ConstructorDimensions.Parameters)
    (o : Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p)) :
    Option (Outcome p) :=
  o.bind fun value => value.2.1.map fun _ => codeSlow p value.1

private theorem measurable_optionBind {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (input : X → Option Y) (hinput : Measurable input)
    (f : Y → Option Z) (hf : Measurable f) :
    Measurable (fun x => (input x).bind f) := by
  let e : Option Y ≃ᵐ Y ⊕ PUnit := {
    toEquiv := Equiv.optionEquivSumPUnit Y
    measurable_toFun := comap_measurable _
    measurable_invFun := by
      rw [measurable_comap_iff]
      exact measurable_id }
  have heq : (fun x => (input x).bind f) =
      fun x => Sum.elim f (fun _ : PUnit => (none : Option Z)) (e (input x)) := by
    funext x
    cases input x <;> rfl
  have hlift : Measurable (Sum.elim f (fun _ : PUnit => (none : Option Z))) := by
    apply measurable_fun_sum
    · exact hf
    · exact measurable_const
  rw [heq]
  exact hlift.comp (e.measurable.comp hinput)

private theorem measurable_codeSlow (p : ConstructorDimensions.Parameters) :
    Measurable (codeSlow p) := Measurable.of_discrete

private theorem measurable_selectedProjection (p : ConstructorDimensions.Parameters) :
    Measurable (fun o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p =>
      o.2.1.map fun _ => codeSlow p o.1) := by
  let Code := LaterAssignmentStartMeasurability.LaterAssignmentStartCode p
  let Theta := AssignmentParameterFibreKernel.Theta p
  let Out := Outcome p
  let e := ReferenceCollectionDispatchMeasurability.optionPairEquiv Theta Code
  let decode : (Theta × Code) ⊕ (PUnit × Code) → Option Out :=
    Sum.elim (fun q => some (codeSlow p q.2)) (fun _ => none)
  have hdecode : Measurable decode := by
    apply measurable_fun_sum
    · exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable
        (fun q : Theta × Code => codeSlow p q.2)
        ((measurable_codeSlow p).comp measurable_snd)
    · exact measurable_const
  have harg : Measurable (fun o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p =>
      (o.2.1, o.1)) :=
    (measurable_fst.comp measurable_snd).prodMk measurable_fst
  have heq : (fun o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p =>
      o.2.1.map fun _ => codeSlow p o.1) = fun o => decode (e (o.2.1, o.1)) := by
    funext o
    cases h : o.2.1 <;> rfl
  rw [heq]
  exact hdecode.comp (e.measurable.comp harg)

private theorem measurable_projectOutput (p : ConstructorDimensions.Parameters) :
    Measurable (projectOutput p) := by
  exact measurable_optionBind _ measurable_id _ (measurable_selectedProjection p)

abbrev FirstCall (p : ConstructorDimensions.Parameters) :=
  Fin p.T × (Fin p.T × AssignmentParameterFibreKernel.Theta p)

/-- The literal first-invocation observation, retaining the original call,
the optional checked outcome, and the complete `K + 1` assignment vector. -/
def firstFibreOutput (z : SourceInput p) : Y p :=
  (ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z).map
    (fun c => (c.1, (c.2.1,
      (ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt
          rate rewards C_star C_h c.2.1 z,
        ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector
          c.2.1 z))))

private def projectStratum (x : ReferenceFirstCollectionSamplerOutputLaw.FirstStratum p) :
    FibrePayload p :=
  (projectOutput p x.1, x.2)

private theorem projectStratum_measurable :
    Measurable (projectStratum (p := p)) := by
  exact ((measurable_projectOutput p).comp measurable_fst).prodMk measurable_snd

private theorem firstFibreOutput_eq_projectedFirstOutput (z : SourceInput p) :
    firstFibreOutput rate rewards C_star C_h z =
      (ReferenceFirstCollectionSamplerOutputLaw.firstOutput rate rewards C_star C_h z).map
        (fun c => (c.1, (c.2.1, projectStratum c.2.2))) := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      simp [firstFibreOutput, ReferenceFirstCollectionSamplerOutputLaw.firstOutput, hcall]
  | some _ =>
      simp [firstFibreOutput, ReferenceFirstCollectionSamplerOutputLaw.firstOutput,
        projectStratum, projectOutput,
        ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt, codeSlow,
        hcall, ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector]
      rfl

/-- Borel measurability on the original nested sum/product carrier. -/
theorem firstFibreOutput_measurable : Measurable (firstFibreOutput rate rewards C_star C_h) := by
  have hmap : Measurable (fun c : Fin p.T ×
      (Fin p.T × ReferenceFirstCollectionSamplerOutputLaw.FirstStratum p) =>
      (c.1, (c.2.1, projectStratum c.2.2))) := by
    exact (measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        ((projectStratum_measurable (p := p)).comp
          (measurable_snd.comp measurable_snd))))
  have hprojected := LaterAssignmentFullOutputMeasurability.measurable_optionMap
    (fun c : Fin p.T × (Fin p.T × ReferenceFirstCollectionSamplerOutputLaw.FirstStratum p) =>
      (c.1, (c.2.1, projectStratum c.2.2))) hmap
    (ReferenceFirstCollectionSamplerOutputLaw.firstOutput rate rewards C_star C_h)
    (ReferenceFirstCollectionSamplerOutputLaw.firstOutput_measurable rate rewards C_star C_h)
  have hrewrite : firstFibreOutput rate rewards C_star C_h =
      fun z => (ReferenceFirstCollectionSamplerOutputLaw.firstOutput
        rate rewards C_star C_h z).map
          (fun c => (c.1, (c.2.1, projectStratum c.2.2))) :=
    funext (firstFibreOutput_eq_projectedFirstOutput rate rewards C_star C_h)
  exact hrewrite ▸ hprojected

/-- The outer absence tag is exactly absence of the original first call. -/
theorem firstFibreOutput_eq_none_iff_original_call_eq_none (z : SourceInput p) :
    firstFibreOutput rate rewards C_star C_h z = none ↔
      ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z = none := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z <;> simp [firstFibreOutput, hcall]

/-- A Borel event on one original cutoff/date/outcome stratum, pulled back to
the whole continuous assignment vector. -/
def fibreVectorSlice (B : Set (Y p)) (u t : Fin p.T) (a : Outcome p) :
    Set (AssignmentVector p) :=
  {v | some (u, (t, (some a, v))) ∈ B}

theorem fibreVectorSlice_measurable (B : Set (Y p)) (hB : MeasurableSet B)
    (u t : Fin p.T) (a : Outcome p) :
    MeasurableSet (fibreVectorSlice B u t a) := by
  apply hB.preimage
  exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable
    (fun v : AssignmentVector p => (u, (t, (some a, v))))
    (measurable_const.prodMk (measurable_const.prodMk
      (measurable_const.prodMk measurable_id)))

/-- The literal same-field finite-fibre test. -/
def firstFibreCellEvent (t : Fin p.T) (a : Outcome p)
    (Cv : Set (AssignmentVector p)) (z : SourceInput p) : Prop :=
  ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt rate rewards C_star C_h t z = some a ∧
    ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector
      t z ∈ Cv

def firstFibreCellTest (t : Fin p.T) (a : Outcome p)
    (Cv : Set (AssignmentVector p)) (z : SourceInput p) : ℝ :=
  Set.indicator {z | firstFibreCellEvent rate rewards C_star C_h t a Cv z}
    (fun _ => (1 : ℝ)) z

def firstFibreProbability (t : Fin p.T) (a : Outcome p)
    (Cv : Set (AssignmentVector p)) (z : SourceInput p) : ℝ :=
  match ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z with
  | none => 0
  | some theta =>
      (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
        (AssignmentParameterFibreKernel.fibreMeasure p theta a Cv).toReal

private theorem firstFibreCellEvent_measurable (t : Fin p.T) (a : Outcome p)
    (Cv : Set (AssignmentVector p)) (hCv : MeasurableSet Cv) :
    MeasurableSet {z | firstFibreCellEvent rate rewards C_star C_h t a Cv z} := by
  apply MeasurableSet.inter
  · exact (show Measurable (ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt
        rate rewards C_star C_h t) from by
        change Measurable (projectOutput p ∘
          ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h t)
        exact (measurable_projectOutput p).comp
          (ReferenceCalendarLaterSamplerOutputSections.measurable_outputAt rate rewards C_star C_h t))
      (measurableSet_option_singleton (some a))
  · exact hCv.preimage
      (measurable_snd.comp
        (ReferenceFirstCollectionSamplerOutputLaw.firstOutputPair_measurable
          rate rewards C_star C_h t))

private theorem firstFibreCellTest_integrable (t : Fin p.T) (a : Outcome p)
    (Cv : Set (AssignmentVector p)) (hCv : MeasurableSet Cv) :
    Integrable (firstFibreCellTest rate rewards C_star C_h t a Cv)
      (sourceInputLaw p) := by
  exact (integrable_const (1 : ℝ)).indicator
    (firstFibreCellEvent_measurable rate rewards C_star C_h t a Cv hCv)

/-- Same-field conditional finite-fibre law on each original first-call cell.
The conditioning field is the exact successor source-prefix field. -/
theorem firstFibre_cell_condExp (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (a : Outcome p) (Cv : Set (AssignmentVector p))
    (hCv : MeasurableSet Cv) :
    (sourceInputLaw p)[
      (ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t).indicator
        (firstFibreCellTest rate rewards C_star C_h t a Cv) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      =ᵐ[sourceInputLaw p]
      (ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t).indicator
        (firstFibreProbability rate rewards C_star C_h t a Cv) := by
  let μ := sourceInputLaw p
  let cell := ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t
  let H := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let test := firstFibreCellTest rate rewards C_star C_h t a Cv
  let q := firstFibreProbability rate rewards C_star C_h t a Cv
  have hcellField : MeasurableSet[H (t.val + 1)] cell :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hfieldLe : H (t.val + 1) ≤ (inferInstance : MeasurableSpace (SourceInput p)) :=
    H.le (t.val + 1)
  have hcellGlobal : MeasurableSet cell := hfieldLe _ hcellField
  have htestInt : Integrable test μ := by
    exact firstFibreCellTest_integrable rate rewards C_star C_h t a Cv hCv
  have hqInt : Integrable q μ := by
    exact ReferenceCalendarLaterSamplerFibreMass.fibreProbability_integrable
      rate rewards C_star C_h control0 t a Cv hCv
  have hsectionCE :=
    ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt_vector_condExp
      rate rewards C_star C_h control0 t a Cv hCv
  have hsectionCE' : μ[test | H (t.val + 1)] =ᵐ[μ] q := by
    change (sourceInputLaw p)[(fun z => Set.indicator
      {z | ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt
          rate rewards C_star C_h t z = some a ∧
        ContinuousControlSlice.assignmentVector
          (ReferenceSourceCurrentControlFreshness.u_t p t z).1 ∈ Cv}
      (fun _ => (1 : ℝ)) z) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      =ᵐ[sourceInputLaw p] (fun z =>
        match ReferenceCalendarLaterSamplerPredictability.calendarParameters
            rate rewards C_star C_h t z with
        | none => 0
        | some theta => (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
            (AssignmentParameterFibreKernel.fibreMeasure p theta a Cv).toReal)
    exact hsectionCE
  have hcellStrong : StronglyMeasurable[H (t.val + 1)]
      (cell.indicator (fun _ => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hcellField
  have hproduct :
      (fun z => cell.indicator (fun _ => (1 : ℝ)) z * test z) = cell.indicator test := by
    funext z
    by_cases hz : z ∈ cell <;> simp [Set.indicator, hz]
  have hrestrictedInt : Integrable (cell.indicator test) μ := htestInt.indicator hcellGlobal
  have hproductInt : Integrable
      (fun z => cell.indicator (fun _ => (1 : ℝ)) z * test z) μ := by
    rw [hproduct]
    exact hrestrictedInt
  have hproductAE :
      (fun z => cell.indicator (fun _ => (1 : ℝ)) z * test z) =ᵐ[μ] cell.indicator test :=
    Filter.Eventually.of_forall (fun z => congrFun hproduct z)
  have hpull := condExp_mul_of_stronglyMeasurable_left hcellStrong hproductInt htestInt
  have hleft := condExp_congr_ae (μ := μ) (m := H (t.val + 1)) hproductAE.symm
  filter_upwards [hleft, hpull, hsectionCE'] with z h₁ h₂ h₃
  calc
    μ[cell.indicator test | H (t.val + 1)] z =
        μ[(fun z => cell.indicator (fun _ => (1 : ℝ)) z * test z) | H (t.val + 1)] z := h₁
    _ = cell.indicator (fun _ => (1 : ℝ)) z * μ[test | H (t.val + 1)] z := h₂
    _ = cell.indicator (fun _ => (1 : ℝ)) z * q z := by rw [h₃]
    _ = cell.indicator q z := by
      by_cases hz : z ∈ cell <;> simp [Set.indicator, hz]

/-- The restricted integral form of the same original-cell identity. -/
theorem firstFibre_cell_integral (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (a : Outcome p) (Cv : Set (AssignmentVector p))
    (hCv : MeasurableSet Cv) :
    ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t,
      firstFibreCellTest rate rewards C_star C_h t a Cv z ∂sourceInputLaw p =
    ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t,
      firstFibreProbability rate rewards C_star C_h t a Cv z ∂sourceInputLaw p := by
  let μ := sourceInputLaw p
  let cell := ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t
  let H := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let test := firstFibreCellTest rate rewards C_star C_h t a Cv
  let q := firstFibreProbability rate rewards C_star C_h t a Cv
  have hcellField : MeasurableSet[H (t.val + 1)] cell :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hfieldLe : H (t.val + 1) ≤ (inferInstance : MeasurableSpace (SourceInput p)) :=
    H.le (t.val + 1)
  have hcellGlobal : MeasurableSet cell := hfieldLe _ hcellField
  have htestInt : Integrable test μ :=
    firstFibreCellTest_integrable rate rewards C_star C_h t a Cv hCv
  have hrestrictedInt : Integrable (cell.indicator test) μ := htestInt.indicator hcellGlobal
  have hce := firstFibre_cell_condExp rate rewards C_star C_h control0 u t a Cv hCv
  have hce' : μ[cell.indicator test | H (t.val + 1)] =ᵐ[μ] cell.indicator q := by
    simpa only [μ, H, cell, test, q] using hce
  calc
    ∫ z in cell, test z ∂μ = ∫ z in cell, cell.indicator test z ∂μ := by
      apply setIntegral_congr_ae hcellGlobal
      filter_upwards [] with z hz
      simp [Set.indicator, hz]
    _ = ∫ z in cell, μ[cell.indicator test | H (t.val + 1)] z ∂μ := by
      symm
      exact setIntegral_condExp hfieldLe hrestrictedInt hcellField
    _ = ∫ z in cell, cell.indicator q z ∂μ :=
      setIntegral_congr_ae hcellGlobal (hce'.mono fun z hz _ => hz)
    _ = ∫ z in cell, q z ∂μ := by
      apply setIntegral_congr_ae hcellGlobal
      filter_upwards [] with z hz
      simp [Set.indicator, hz]

/-- The pointwise call/record trace: on every original first-call cell the
parameter is the one read from its actual physical record, and the output code
is the checked sampler on the original full vector. -/
theorem firstCell_actualSamplerTrace (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) :
    ∃ theta : AssignmentParameterFibreKernel.Theta p,
      ∃ o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p,
        ReferenceCalendarLaterSamplerPredictability.calendarParameters
          rate rewards C_star C_h t z = some theta ∧
        ReferenceCalendarLaterSamplerOutputSections.outputAt
          rate rewards C_star C_h t z = some o ∧
        o.2.1 = some theta ∧
        o.2.2.2.1 =
          ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector
            t z ∧
        o.1 = LaterAssignmentStartMeasurability.codeOfCheckedSample p
          (CheckedAssignmentSample.checkedAssignmentSample p theta.1 theta.2
            (ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector
              t z)) ∧
        ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt rate rewards C_star C_h t z =
          some (AssignmentParameterFibreKernel.successfulSlowSet p theta
            (ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector
              t z)) := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      have htags :=
        (ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags
          rate rewards C_star C_h u t z).mp hz
      rw [hcall] at htags
      simp at htags
  | some c =>
      have htags :=
        (ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags
          rate rewards C_star C_h u t z).mp hz
      rw [hcall] at htags
      simp only [Option.map_some, Option.some.injEq] at htags
      change (c.1, c.2.1) = (u, t) at htags
      have hu : c.1 = u := congrArg Prod.fst htags
      have ht : c.2.1 = t := congrArg Prod.snd htags
      have hpair : c = (u, (t, c.2.2)) := by
        apply Prod.ext hu
        apply Prod.ext ht
        rfl
      let theta : AssignmentParameterFibreKernel.Theta p := c.2.2
      have hcall' :
          ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z =
            some (u, (t, theta)) := by
        rw [hcall, hpair]
      obtain ⟨n, r, hr, htime, hcollection, _hbefore⟩ :=
        (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec
          (rate := rate) rewards C_star C_h z u t theta).mp hcall'
      obtain ⟨_payload, _ledger, _proposal, _hcoord, _hcut, hparameters⟩ :=
        (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcollection
      have hrActual :
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r := by
        have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
          rate z rewards C_star C_h
        have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
          rate z rewards C_star C_h
        have hn : n < p.T - ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h := by
          simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using
            (List.getElem?_eq_some_iff.mp hr).1
        have hget := congrArg
          (fun records : List ℕ => records[n]?) htimes
        simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_map,
          List.getElem?_range' hn, Nat.one_mul] at hget
        rw [hr] at hget
        simp only [Option.map_some] at hget
        have htimeNat : r.input.time.val =
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n := by
          exact Option.some.inj hget
        have htimeNat' : t.val =
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n := by
          simpa only [htime] using htimeNat
        have hstart : ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h ≤ t.val := by omega
        unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
        rw [ite_eq_left hstart]
        rw [show t.val - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h = n by omega, hr]
      have hparam : ReferenceCalendarLaterSamplerPredictability.calendarParameters
          rate rewards C_star C_h t z = some theta := by
        rw [ReferenceCalendarLaterSamplerPredictability.calendarParameters, hrActual]
        exact hparameters
      have hselected := ReferenceCalendarLaterSamplerOutputSections.outputAt_parameters
        rate rewards C_star C_h t z
      rw [hparam] at hselected
      cases hout : ReferenceCalendarLaterSamplerOutputSections.outputAt
          rate rewards C_star C_h t z with
      | none => simp [hout] at hselected
      | some o =>
          have htheta : o.2.1 = some theta := by
            simpa only [hout, Option.bind_some] using hselected
          have hcode := ReferenceCalendarLaterSamplerOutputSections.outputAt_code_vector
            rate rewards C_star C_h t z o theta hout htheta
          have hactive := ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt_eq_selectedSampler
            rate rewards C_star C_h t z o theta hout htheta
          refine ⟨theta, o, hparam, rfl, htheta, ?_, ?_, ?_⟩
          · simpa only [ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector] using
              hcode.1
          · exact hcode.2
          · simpa only [ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector] using
              hactive

private def firstFibreCellTerm (B : Set (Y p)) (u t : Fin p.T) (a : Outcome p)
    (z : SourceInput p) : ℝ :=
  (ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t).indicator
    (firstFibreCellTest rate rewards C_star C_h t a
      (fibreVectorSlice B u t a)) z

private theorem firstFibreIndicator_reconstruction (B : Set (Y p)) (z : SourceInput p) :
    B.indicator (fun _ => (1 : ℝ)) (firstFibreOutput rate rewards C_star C_h z) =
      (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
        rate rewards C_star C_h).indicator
          (fun _ => B.indicator (fun _ => (1 : ℝ)) none) z +
        ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
          firstFibreCellTerm rate rewards C_star C_h B u t a z := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      simp [firstFibreOutput, firstFibreCellTerm,
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent,
        ReferenceCalendarCollectionCallControlLaw.firstCell, hcall]
  | some c =>
      rcases c with ⟨u₀, t₀, theta₀⟩
      have htags (u t : Fin p.T) :
          z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t ↔
            (u, t) = (u₀, t₀) := by
        rw [ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags]
        simp only [hcall, Option.map_some, Option.some.injEq]
        exact eq_comm
      have hfirst : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
          rate rewards C_star C_h u₀ t₀ := (htags u₀ t₀).2 rfl
      obtain ⟨theta, _o, _hparameter, _hout, _hselected, _hvector, _hcode, hactive⟩ :=
        firstCell_actualSamplerTrace rate rewards C_star C_h u₀ t₀ z hfirst
      let a₀ : Outcome p := AssignmentParameterFibreKernel.successfulSlowSet p theta
        (ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector
          t₀ z)
      have hactive' :
          ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt rate rewards C_star C_h t₀ z =
            some a₀ := by
        simpa only [a₀] using hactive
      let value : ℝ := B.indicator (fun _ => (1 : ℝ))
        (firstFibreOutput rate rewards C_star C_h z)
      have htest_eq :
          firstFibreCellTest rate rewards C_star C_h t₀ a₀
            (fibreVectorSlice B u₀ t₀ a₀) z = value := by
        simp [firstFibreCellTest, firstFibreCellEvent, fibreVectorSlice,
          Set.indicator, firstFibreOutput, hcall, hactive', value]
      have hterm (u t : Fin p.T) (a : Outcome p) :
          firstFibreCellTerm rate rewards C_star C_h B u t a z =
            if (u, (t, a)) = (u₀, (t₀, a₀)) then value else 0 := by
        by_cases htag : (u, t) = (u₀, t₀)
        · have hu : u = u₀ := congrArg Prod.fst htag
          have ht : t = t₀ := congrArg Prod.snd htag
          subst u
          subst t
          by_cases ha : a = a₀
          · subst a
            simp [firstFibreCellTerm, hfirst, htest_eq, value]
          · have hne : a₀ ≠ a := Ne.symm ha
            have htestzero : firstFibreCellTest rate rewards C_star C_h t₀ a
                (fibreVectorSlice B u₀ t₀ a) z = 0 := by
              simp [firstFibreCellTest, firstFibreCellEvent, hactive', hne]
            simp [firstFibreCellTerm, hfirst, htestzero, value, ha]
        · have hnot : z ∉ ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u t := fun hz => htag ((htags u t).mp hz)
          have htriple : (u, (t, a)) ≠ (u₀, (t₀, a₀)) := by
            intro h
            apply htag
            exact congrArg (fun q : Fin p.T × (Fin p.T × Outcome p) => (q.1, q.2.1)) h
          simp [firstFibreCellTerm, Set.indicator, hnot, htriple, value]
      have hinner (u t : Fin p.T) :
          (∑ a : Outcome p, firstFibreCellTerm rate rewards C_star C_h B u t a z) =
            if (u, t) = (u₀, t₀) then value else 0 := by
        by_cases htag : (u, t) = (u₀, t₀)
        · have hu : u = u₀ := congrArg Prod.fst htag
          have ht : t = t₀ := congrArg Prod.snd htag
          subst u
          subst t
          have hsum :
              (∑ a : Outcome p,
                if (u₀, (t₀, a)) = (u₀, (t₀, a₀)) then value else 0) = value := by
            rw [Finset.sum_eq_single a₀]
            · simp
            · intro b _hb hba
              simp [hba]
            · intro hmem
              exact (hmem (Finset.mem_univ a₀)).elim
          simp [hterm, Prod.mk.injEq]
        · simp_rw [hterm]
          have hindices : u ≠ u₀ ∨ t ≠ t₀ := by
            by_cases hu : u = u₀
            · right
              intro ht
              exact htag (Prod.ext hu ht)
            · exact Or.inl hu
          rcases hindices with hu | ht
          · simp [Prod.mk.injEq, hu]
          · simp [Prod.mk.injEq, ht]
      have hmiddle (u : Fin p.T) :
          (∑ t : Fin p.T, ∑ a : Outcome p,
            firstFibreCellTerm rate rewards C_star C_h B u t a z) =
              if u = u₀ then value else 0 := by
        by_cases hu : u = u₀
        · subst u
          have hsum :
              (∑ t : Fin p.T, if (u₀, t) = (u₀, t₀) then value else 0) = value := by
            rw [Finset.sum_eq_single t₀]
            · simp
            · intro b _hb hbt
              simp [hbt]
            · intro hmem
              exact (hmem (Finset.mem_univ t₀)).elim
          simp [hinner, Prod.mk.injEq]
        · simp_rw [hinner]
          simp [Prod.mk.injEq, hu]
      have hsum :
          (∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
            firstFibreCellTerm rate rewards C_star C_h B u t a z) = value := by
        have hsum' : (∑ u : Fin p.T, if u = u₀ then value else 0) = value := by
          rw [Finset.sum_eq_single u₀]
          · simp
          · intro b _hb hbu
            simp [hbu]
          · intro hmem
            exact (hmem (Finset.mem_univ u₀)).elim
        calc
          (∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
            firstFibreCellTerm rate rewards C_star C_h B u t a z) =
              ∑ u : Fin p.T, if u = u₀ then value else 0 := by
            apply Finset.sum_congr rfl
            intro u _hu
            exact hmiddle u
          _ = value := hsum'
      rw [hsum]
      simp [value, firstFibreOutput, hcall,
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent]

private theorem firstFibreCellTerm_integrable (B : Set (Y p))
    (hB : MeasurableSet B) (u t : Fin p.T) (a : Outcome p) :
    Integrable (firstFibreCellTerm rate rewards C_star C_h B u t a)
      (sourceInputLaw p) := by
  have hslice := fibreVectorSlice_measurable B hB u t a
  have htest := firstFibreCellTest_integrable rate rewards C_star C_h t a
    (fibreVectorSlice B u t a) hslice
  have hcell := ReferenceFirstCollectionSamplerCall.measurableSet_firstCollectionCall_cell
    rate rewards C_star C_h u t
  exact htest.indicator hcell

private theorem firstFibreProbability_integrable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (a : Outcome p)
    (Cv : Set (AssignmentVector p)) (hCv : MeasurableSet Cv) :
    Integrable (firstFibreProbability rate rewards C_star C_h t a Cv)
      (sourceInputLaw p) := by
  exact ReferenceCalendarLaterSamplerFibreMass.fibreProbability_integrable
    rate rewards C_star C_h control0 t a Cv hCv

/-- The full-vector disintegration conserves each original first-cell mass:
all optional checked outcomes, including failure, are summed, and actual
selected-parameter support makes the total conditional fibre mass one. -/
theorem firstCell_fibreMass_conservation
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) :
    ∑ a : Outcome p,
      ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t,
        firstFibreProbability rate rewards C_star C_h t a Set.univ z ∂sourceInputLaw p =
      (sourceInputLaw p).real
        (ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) := by
  let μ := sourceInputLaw p
  let cell := ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t
  have hcellGlobal : MeasurableSet cell := by
    have hfield := ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
    exact ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le
      (t.val + 1)) _ hfield
  have htermInt (a : Outcome p) : IntegrableOn
      (firstFibreProbability rate rewards C_star C_h t a Set.univ) cell μ :=
    (firstFibreProbability_integrable rate rewards C_star C_h control0 t a Set.univ
      MeasurableSet.univ).integrableOn
  have hpoint (z : SourceInput p) (hz : z ∈ cell) :
      (∑ a : Outcome p, firstFibreProbability rate rewards C_star C_h t a Set.univ z) = 1 := by
    obtain ⟨theta, _o, htheta, _hout, _hselected, _hvector, _hcode, _hactive⟩ :=
      firstCell_actualSamplerTrace rate rewards C_star C_h u t z hz
    simp only [firstFibreProbability, htheta]
    have hmass := ReferenceCalendarLaterSamplerFibreMass.fibreProbability_sum_outcomes
      rate rewards C_star C_h t z
    rw [htheta] at hmass
    have hmeasure (a : Outcome p) :
        (AssignmentParameterFibreKernel.fibreMeasure p theta a Set.univ).toReal = 1 := by
      have hprob : IsProbabilityMeasure
          (AssignmentParameterFibreKernel.fibreMeasure p theta a) := by
        change IsProbabilityMeasure
          (FiniteFibreLift.fibreMeasure (ContinuousControlSlice.assignmentLaw p.K)
            (AssignmentParameterFibreKernel.successfulSlowSet p theta) a)
        exact FiniteFibreLift.instIsProbabilityMeasureFibreMeasure
          (μ := ContinuousControlSlice.assignmentLaw p.K)
          (F := AssignmentParameterFibreKernel.successfulSlowSet p theta) (a := a)
      simp
    have hmass' :
        (∑ a : Outcome p,
          (AssignmentParameterFibreKernel.fibreMass p theta a).toReal) = 1 := by
      simpa using hmass
    simp_rw [hmeasure]
    simpa only [mul_one] using hmass'
  calc
    _ = ∫ z in cell,
          ∑ a : Outcome p, firstFibreProbability rate rewards C_star C_h t a Set.univ z ∂μ := by
      symm
      exact integral_finsetSum Finset.univ
        (fun a _ => htermInt a)
    _ = ∫ z in cell, (1 : ℝ) ∂μ := by
      apply setIntegral_congr_ae hcellGlobal
      filter_upwards [] with z hz
      exact hpoint z hz
    _ = μ.real cell := by
      simp [Measure.real]

/-- Exact Borel-test law for the actual first invocation, retaining the
no-call mass and every unnormalized original cutoff/date/outcome/vector fibre.
-/
theorem firstFibreOutput_borel_test_law
    (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (Y p)) (hB : MeasurableSet B) :
    ∫ z, B.indicator (fun _ => (1 : ℝ))
        (firstFibreOutput rate rewards C_star C_h z) ∂sourceInputLaw p =
      (sourceInputLaw p).real
          (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
            rate rewards C_star C_h) *
        B.indicator (fun _ => (1 : ℝ)) none +
        ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
          ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u t,
            firstFibreProbability rate rewards C_star C_h t a
              (fibreVectorSlice B u t a) z ∂sourceInputLaw p := by
  let μ := sourceInputLaw p
  let noneValue : ℝ := B.indicator (fun _ => (1 : ℝ)) none
  let noneTerm : SourceInput p → ℝ :=
    (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
      rate rewards C_star C_h).indicator (fun _ => noneValue)
  let cellTerm (u t : Fin p.T) (a : Outcome p) : SourceInput p → ℝ :=
    firstFibreCellTerm rate rewards C_star C_h B u t a
  have hnoneMeas :=
    ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent_measurable
      rate rewards C_star C_h
  have hnoneInt : Integrable noneTerm μ := (integrable_const noneValue).indicator hnoneMeas
  have hcellInt (u t : Fin p.T) (a : Outcome p) : Integrable (cellTerm u t a) μ :=
    firstFibreCellTerm_integrable rate rewards C_star C_h B hB u t a
  have hsumInt : Integrable
      (fun z => ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p, cellTerm u t a z) μ := by
    apply integrable_finsetSum
    intro u hu
    apply integrable_finsetSum
    intro t ht
    apply integrable_finsetSum
    intro a ha
    exact hcellInt u t a
  have hleftInt : Integrable
      (fun z => B.indicator (fun _ => (1 : ℝ))
        (firstFibreOutput rate rewards C_star C_h z)) μ :=
    (integrable_const (1 : ℝ)).indicator
      (hB.preimage (firstFibreOutput_measurable rate rewards C_star C_h))
  have hpoint (z : SourceInput p) :
      B.indicator (fun _ => (1 : ℝ)) (firstFibreOutput rate rewards C_star C_h z) =
        noneTerm z + ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
          cellTerm u t a z := by
    simpa only [noneTerm, cellTerm, noneValue] using
      firstFibreIndicator_reconstruction rate rewards C_star C_h B z
  have hnoneIntegral :
      ∫ z, noneTerm z ∂μ = μ.real
        (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h) * noneValue := by
    change ∫ z, (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
      rate rewards C_star C_h).indicator (fun _ => noneValue) z ∂μ = _
    rw [integral_indicator_const noneValue hnoneMeas, smul_eq_mul]
  have hsumIntegral :
      ∫ z, ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p, cellTerm u t a z ∂μ =
        ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
          ∫ z, cellTerm u t a z ∂μ := by
    calc
      _ = ∑ u : Fin p.T, ∫ z, ∑ t : Fin p.T, ∑ a : Outcome p,
            cellTerm u t a z ∂μ := by
        simpa using integral_finsetSum Finset.univ
          (f := fun u z => ∑ t : Fin p.T, ∑ a : Outcome p, cellTerm u t a z)
          (fun u hu => by
            apply integrable_finsetSum
            intro t ht
            apply integrable_finsetSum
            intro a ha
            exact hcellInt u t a)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u hu
        calc
          _ = ∑ t : Fin p.T, ∫ z, ∑ a : Outcome p, cellTerm u t a z ∂μ := by
            simpa using integral_finsetSum Finset.univ
              (f := fun t z => ∑ a : Outcome p, cellTerm u t a z)
              (fun t ht => by
                apply integrable_finsetSum
                intro a ha
                exact hcellInt u t a)
          _ = _ := by
            apply Finset.sum_congr rfl
            intro t ht
            exact integral_finsetSum Finset.univ (fun a ha => hcellInt u t a)
  have hcellMix (u t : Fin p.T) (a : Outcome p) :
      ∫ z, cellTerm u t a z ∂μ =
        ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t,
          firstFibreProbability rate rewards C_star C_h t a
            (fibreVectorSlice B u t a) z ∂μ := by
    change ∫ z, (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t).indicator
        (firstFibreCellTest rate rewards C_star C_h t a
          (fibreVectorSlice B u t a)) z ∂μ = _
    have hcellGlobal : MeasurableSet
        (ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) := by
      have hcellField := ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
        rate rewards C_star C_h control0 u t
      exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le
        (t.val + 1) _ hcellField
    rw [integral_indicator hcellGlobal]
    exact firstFibre_cell_integral rate rewards C_star C_h control0 u t a
      (fibreVectorSlice B u t a)
      (fibreVectorSlice_measurable B hB u t a)
  calc
    _ = ∫ z, noneTerm z +
          (∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p, cellTerm u t a z) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ z, noneTerm z ∂μ +
          ∫ z, ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p, cellTerm u t a z ∂μ :=
      integral_add' hnoneInt hsumInt
    _ = μ.real
          (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
            rate rewards C_star C_h) * noneValue +
          ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
            ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
                rate rewards C_star C_h u t,
              firstFibreProbability rate rewards C_star C_h t a
                (fibreVectorSlice B u t a) z ∂μ := by
      rw [hnoneIntegral, hsumIntegral]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro a ha
      exact hcellMix u t a

end Bandits.Support.ReferenceFirstCollectionSamplerFibreLaw

end
