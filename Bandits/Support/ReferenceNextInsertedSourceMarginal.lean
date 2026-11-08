/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceNextRetainedEndpointFibreLaw

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-!
# Next physical-source insertion on the original branch lift

The extension retains the entire original first-invocation lift and inserts
one complete assignment vector at the actual first next invocation. All
measures are unnormalized. PRE stopping uses the canonical current-vector
Dirac. The actual physical call, numerical word and generated PRE list are
read on the same source and auxiliary array.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:176-215,323-390`, `08_main_theorem.tex:78-109`.
This module does not assert manuscript or all-calendar closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstNextInstallationCellFactors
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationSupportedDisintegration
open ReferencePostInvocationKilledJointLaw
open ReferenceNextRetainedEndpointFibreLaw

namespace Bandits.Support.ReferenceNextInsertedSourceMarginal

variable {p : ConstructorDimensions.Parameters}

abbrev Source := BootstrapPrivateRoundStreams.SourceInput
abbrev Vector := AssignmentParameterFibreKernel.AssignmentVector
abbrev Scalar := ContinuousControlSlice.Scalar
abbrev Outcome (p : ConstructorDimensions.Parameters) := AssignmentParameterFibreKernel.Outcome p

local instance sourceMeasurableSpace : MeasurableSpace (Source p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance controlMeasurableSpace : MeasurableSpace (ContinuousLearningRows.TimeControl p) :=
  ReferencePostInvocationSupportedDisintegration.controlMeasurableSpace

local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩
local instance outcomeMeasurableSpace : MeasurableSpace (Outcome p) := ⊤
local instance outcomeDiscrete : DiscreteMeasurableSpace (Outcome p) := ⟨fun _ => trivial⟩

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p) (b : Bool) (u t q : Fin p.T)

local notation "Lift" => BranchLift rate rewards C_star C_h b u t
local notation "Lambda" => branchLaw rate rewards C_star C_h control0 b u t
local notation "O" => branchObservation rate rewards C_star C_h control0 b u t
local notation "E" => firstNextEvent rate rewards C_star C_h control0 b u t q

def actualNextVectorKernel : ProbabilityTheory.Kernel Lift (Vector p) :=
  (nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0).comap
    (actualNextInput rate rewards C_star C_h control0 b u t q)
    (measurable_actualNextInput rate rewards C_star C_h control0 b u t q)

instance actualNextVectorKernel_markov : ProbabilityTheory.IsMarkovKernel
    (actualNextVectorKernel rate rewards C_star C_h control0 b u t q) := by
  unfold actualNextVectorKernel
  infer_instance

/-- No event normalization: absent, stopped and null masses keep their
original weights. The full original source and analytical array remain. -/
def nextLiftLaw : Measure (Lift × Vector p) :=
  ((Lambda).restrict (firstNextEvent rate rewards C_star C_h control0 b u t q)).compProd
    (actualNextVectorKernel rate rewards C_star C_h control0 b u t q)

/-- Retain the whole previous observer, first vector and arrays while
exposing the entire newly inserted physical source separately. -/
def nextInsertedReadout (wv : Lift × Vector p) :
    Lift × (Vector p × Source p) :=
  (wv.1, (wv.2, ReferenceFirstCollectionRenewalVectorInsertion.insert q
    (O q.castSucc wv.1).1.1.1.2 wv.2))

theorem measurable_nextInsertedReadout :
    Measurable (nextInsertedReadout rate rewards C_star C_h control0 b u t q) :=
  measurable_fst.prodMk (measurable_snd.prodMk
    ((ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert (t := q)).comp
      (((measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).fst.fst.fst.snd.comp
        measurable_fst).prodMk measurable_snd)))

def nextInsertedLaw : Measure (Lift × (Vector p × Source p)) :=
  (nextLiftLaw rate rewards C_star C_h control0 b u t q).map
    (nextInsertedReadout rate rewards C_star C_h control0 b u t q)

theorem nextInsertedLaw_map_original :
    (nextInsertedLaw rate rewards C_star C_h control0 b u t q).map Prod.fst =
      (Lambda).restrict (firstNextEvent rate rewards C_star C_h control0 b u t q) := by
  rw [nextInsertedLaw, Measure.map_map measurable_fst
    (measurable_nextInsertedReadout rate rewards C_star C_h control0 b u t q)]
  exact Measure.fst_compProd _ _

instance nextLiftLaw_finite : IsFiniteMeasure
    (nextLiftLaw rate rewards C_star C_h control0 b u t q) := by
  unfold nextLiftLaw
  infer_instance

instance nextInsertedLaw_finite : IsFiniteMeasure
    (nextInsertedLaw rate rewards C_star C_h control0 b u t q) := by
  unfold nextInsertedLaw
  infer_instance

/-- The constant-one test keeps exactly the original first-next-call mass. -/
theorem nextInsertedLaw_mass :
    nextInsertedLaw rate rewards C_star C_h control0 b u t q Set.univ = Lambda E := by
  rw [nextInsertedLaw, Measure.map_apply
    (measurable_nextInsertedReadout rate rewards C_star C_h control0 b u t q) MeasurableSet.univ]
  change nextLiftLaw rate rewards C_star C_h control0 b u t q Set.univ = _
  rw [nextLiftLaw, Measure.compProd_apply_univ, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter]

/-- Analytical stopping preserves the complete physical source at this
date, so its later prescribed physical continuation is still available. -/
theorem stopped_insertedSource_map (i : NextInput rate t q)
    (hi : preClearFlag rate (t := t) q i.1 = false) :
    (nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0 i).map
      (fun v => ReferenceFirstCollectionRenewalVectorInsertion.insert q i.1.1.1.1.2 v) =
        Measure.dirac i.1.1.1.1.2 := by
  have hf : Measurable (fun v : Vector p =>
      ReferenceFirstCollectionRenewalVectorInsertion.insert q i.1.1.1.1.2 v) :=
    (ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert (t := q)).comp
      ((measurable_const (a := i.1.1.1.1.2)).prodMk measurable_id)
  rw [nextVectorKernel_of_preStopped rate rewards C_star C_h (t := t) (q := q) control0 i hi,
    Measure.map_dirac' hf]
  exact congrArg Measure.dirac
    (ReferenceFirstCollectionRenewalVectorInsertion.insert_original_vector q i.1.1.1.1.2)

/-- Averaging this fresh scalar first gives the exact sampler atom. No
independence of this outcome from a history already revealing it is used. -/
theorem freshEndpoint_fibre (theta : AssignmentParameterFibreKernel.Theta p) (a : Outcome p) :
    ContinuousControlSlice.scalarLaw {x | freshEndpoint theta x = a} =
      AssignmentParameterFibreKernel.fibreMass p theta a := by
  have he : {x : Scalar | freshEndpoint theta x = a} =
      (ContinuousCategorical.sample (outcome_card_pos p) (fibreAtom theta) (fibreAtom_sum theta)) ⁻¹'
        {(outcomeEnumeration p).symm a} := by
    ext x
    change freshEndpoint theta x = a ↔ _
    unfold freshEndpoint
    exact (outcomeEnumeration p).eq_symm_apply.symm
  rw [he]
  change ContinuousCategorical.uniform _ = _
  rw [ContinuousCategorical.uniform_sample_singleton (outcome_card_pos p) (p := fibreAtom theta)
    (fun _ => ENNReal.toReal_nonneg) (fibreAtom_sum theta), fibreAtom,
    Equiv.apply_symm_apply, ENNReal.ofReal_toReal (samplerMass_ne_top theta a)]

/-- A fresh inverse-CDF draw never selects a null fibre, pointwise. -/
theorem freshEndpoint_mass_pos (theta : AssignmentParameterFibreKernel.Theta p) (x : Scalar) :
    0 < AssignmentParameterFibreKernel.fibreMass p theta (freshEndpoint theta x) := by
  have h := (freshEndpoint_eq_iff theta x (freshEndpoint theta x)).mp rfl
  rw [ContinuousCategorical.upper_eq_lower_add] at h
  have hp : 0 < fibreAtom theta ((outcomeEnumeration p).symm (freshEndpoint theta x)) := by
    linarith only [h.1, h.2]
  rw [fibreAtom, Equiv.apply_symm_apply] at hp
  by_contra hn
  have hz := le_antisymm (not_lt.mp hn) bot_le
  rw [hz, ENNReal.toReal_zero] at hp
  exact (lt_irrefl _ hp)

private theorem renewed_parameter_of_selector
    (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (old : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
    (hcoord : r.input.state.coordinator = .collection old ledger saved)
    (hcut : ledger.cutoff = cutoff.val + 1)
    (hparameter : ReferenceLaterSamplerParameterMeasurability.parameters? r.input = some theta)
    (hfreeze : ledger.freezeAt ≤ r.input.time.val + 1) :
    (∀ j, 0 < theta.2 j) ∧ theta.1 = LaterAssignmentStartOperation.productQOnPrefixCarrier theta.2 := by
  have hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    omega
  have hindex : (⟨ledger.cutoff - 1, by omega⟩ : Fin p.T) = cutoff := by
    apply Fin.ext
    dsimp only
    omega
  change ReferenceLaterAssignmentFibreStep.parameters? r.input = some theta at hparameter
  simp only [ReferenceLaterAssignmentFibreStep.parameters?, hcoord, dite_eq_left hvalid, hindex] at hparameter
  let x := ReferenceActivePhysicalStep.collectionInput r.input old ledger
    (ReferenceActivePhysicalStep.collectionClock old ledger saved cutoff) cutoff
  change ReferenceLaterAssignmentFibreStep.collectionParameters? x = some theta at hparameter
  unfold ReferenceLaterAssignmentFibreStep.collectionParameters? at hparameter
  cases hclock : CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock x.ledger.pending with
  | error reason => simp only [hclock, reduceCtorEq] at hparameter
  | ok started =>
      simp only [hclock] at hparameter
      by_cases core : CoordinatorRoundDispatch.CollectionCoreValid x
      · rw [dite_eq_left core] at hparameter
        by_cases hpending : x.ledger.pending.Nonempty
        · simp only [ite_eq_left hpending, reduceCtorEq] at hparameter
        · rw [ite_eq_right hpending] at hparameter
          cases hinstruction : started.assignmentStart with
          | none => simp only [hinstruction, reduceCtorEq] at hparameter
          | some instruction =>
              simp only [hinstruction] at hparameter
              rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match] at hparameter
              cases hd : LaterAssignmentStartOperation.decideReconstruction x.payload
                  (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq) instruction with
              | failure reason => simp only [hd, reduceCtorEq] at hparameter
              | success out hrec =>
                  rw [hd] at hparameter
                  have htheta : theta = LaterAssignmentStartMeasurability.selectedSamplerParameters old
                      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
                      instruction out hrec := (Option.some.inj hparameter).symm
                  have hitime := (CoordinatorPhaseClock.startRound_assignment_effect p
                    x.etaReal x.time x.clock x.ledger.pending started instruction
                    core.clock_parameter_valid core.clock_registers_valid core.clock_start_time_valid
                    hclock hinstruction).1
                  have hrenewal : instruction.kind = .renewal :=
                    (AssignmentScoreReconstruction.reconstructLaterStart_renewal_iff
                      _ instruction out hrec).mpr (by
                        change ledger.freezeAt ≤ instruction.time.val + 1
                        rw [hitime]
                        exact hfreeze)
                  obtain ⟨ha, hm⟩ := LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
                    old _ instruction out hrec hrenewal
                  rw [htheta]
                  constructor
                  · rw [ha]
                    exact (LaterAssignmentStartMeasurability.successfulLawSelection
                      old _ instruction out hrec).currentWeightPos
                  · rw [ha]
                    exact funext hm
      · simp only [dite_eq_right core, reduceCtorEq] at hparameter

/-- Renewal of the immediate next call has a positive fresh anchor and the
canonical product-weight parameter. All selector facts come from this path. -/
theorem actual_nextRenewal_parameter (htq : t.val < q.val) (w : Lift)
    (hw : w ∈ firstNextEvent rate rewards C_star C_h control0 b u t q)
    (hrenew : renewalFlag rate rewards C_star C_h (t := t) q (O q.castSucc w) = true) :
    ∃ cutoff theta,
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q
        (O q.castSucc w).1.1.1.2 = some (cutoff, theta) ∧
      (∀ j, 0 < theta.2 j) ∧
      theta.1 = LaterAssignmentStartOperation.productQOnPrefixCarrier theta.2 := by
  obtain ⟨r, cutoff, theta, ledger, saved, _hr, ht, hcoord, hcut, hp, hc, hf, _hafter⟩ :=
    firstNextEvent_callData rate rewards C_star C_h control0 b u t q htq w hw
  rw [installedFirstSource_val rate rewards C_star C_h control0 b u t q.castSucc w] at hc hf
  have hle : ledger.freezeAt ≤ q.val + 1 := by
    simpa only [renewalFlag, hf, Option.any_some, decide_eq_true_eq] using hrenew
  have hle' : ledger.freezeAt ≤ r.input.time.val + 1 := by rw [ht]; exact hle
  exact ⟨cutoff, theta, hc, renewed_parameter_of_selector rate r _ ledger saved cutoff theta
    hcoord hcut hp hle'⟩

/-- The new complete source really runs the selected checked sampler on
the newly inserted vector, including its inclusion/orientation failures. -/
theorem insertReadout_actual_checkedSample (control0 : ContinuousLearningRows.TimeControl p)
    (o : PrefixObservation rate t q.castSucc) (v : Vector p)
    (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
    (hc : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q o.1.1.1.2 =
      some (cutoff, theta)) :
    ∃ output : LaterAssignmentFullOutputMeasurability.FullOutputObservation p,
      ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h q
        (ReferenceFirstCollectionRenewalVectorInsertion.insert q o.1.1.1.2 v) = some output ∧
      output.2.1 = some theta ∧
      output.1 = LaterAssignmentStartMeasurability.codeOfCheckedSample p
        (CheckedAssignmentSample.checkedAssignmentSample p theta.1 theta.2 v) := by
  let z := (ReferenceFirstCollectionRenewalVectorInsertion.insert q o.1.1.1.2 v)
  have hcall : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q z =
      some (cutoff, theta) := by
    change ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q
      (ReferenceFirstCollectionRenewalVectorInsertion.insert q o.1.1.1.2 v) = _
    rw [ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 q,
      ReferenceFirstCollectionRenewalVectorInsertion.insert,
      ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl,
      ← ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 q, hc]
  obtain ⟨record, hr, hrecord⟩ := Option.bind_eq_some_iff.mp hcall
  obtain ⟨_payload, _ledger, _saved, _hcoord, _hcutoff, hparam⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec record cutoff theta).mp hrecord
  have hp : ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h q z =
      some theta := by
    rw [ReferenceCalendarLaterSamplerPredictability.calendarParameters, hr, Option.bind_some]
    exact hparam
  have hout := (ReferenceCalendarLaterSamplerOutputSections.outputAt_parameters
    rate rewards C_star C_h q z).trans hp
  obtain ⟨output, ho, htheta⟩ := Option.bind_eq_some_iff.mp hout
  have hcode := ReferenceCalendarLaterSamplerOutputSections.outputAt_code_vector
    rate rewards C_star C_h q z output theta ho htheta
  have hv : ContinuousControlSlice.assignmentVector
      (ReferenceSourceCurrentControlFreshness.u_t p q z).1 = v :=
    ReferenceFirstCollectionRenewalVectorInsertion.av_insert q o.1.1.1.2 v
  rw [hv] at hcode
  exact ⟨output, ho, htheta, hcode.2⟩

/-- Recomputing the complete PRE numerical word after insertion gives the
retained state, rather than just the state at the last enabled logical date. -/
theorem insertReadout_numerical (control0 : ContinuousLearningRows.TimeControl p) (o : PrefixObservation rate t q.castSucc) (v : Vector p) :
    prefixNumerical rate rewards C_star C_h q.castSucc (ReferenceFirstCollectionRenewalVectorInsertion.insert q o.1.1.1.2 v) =
      prefixNumerical rate rewards C_star C_h q.castSucc o.1.1.1.2 := by
  rw [prefixNumerical_sourcePrefix rate rewards C_star C_h control0 q.castSucc q.val le_rfl,
    ReferenceFirstCollectionRenewalVectorInsertion.insert,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl,
    ← prefixNumerical_sourcePrefix rate rewards C_star C_h control0 q.castSucc q.val le_rfl]

/-- Pointwise preservation of the actual generated PRE-q list after the
second insertion, with its old produced append and original auxiliary array. -/
theorem actual_inserted_history (w : Lift) (v : Vector p) :
    noncallCalendar rate rewards C_star C_h t
      (nextInsertedReadout rate rewards C_star C_h control0 b u t q (w, v)).2.2 w.1.2
        (postSeed rate (branchTransition rate rewards C_star C_h control0 b u t w),
          postHistory (branchTransition rate rewards C_star C_h control0 b u t w)) q.val =
      (O q.castSucc w).2.2.2 := by
  let initial := (postSeed rate (branchTransition rate rewards C_star C_h control0 b u t w),
    postHistory (branchTransition rate rewards C_star C_h control0 b u t w))
  change noncallCalendar rate rewards C_star C_h t
    (ReferenceFirstCollectionRenewalVectorInsertion.insert q (O q.castSucc w).1.1.1.2 v) w.1.2 initial q.val = _
  rw [noncallCalendar_sourcePrefix rate rewards C_star C_h control0 q.val q.isLt.le t
      _ w.1.2 initial q.val le_rfl,
    ReferenceFirstCollectionRenewalVectorInsertion.insert,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl,
    ← noncallCalendar_sourcePrefix rate rewards C_star C_h control0 q.val q.isLt.le t
      _ w.1.2 initial q.val le_rfl,
    branchObservation_source, branchObservation_prefix]
  rfl



/-- Refreshing the unused block preserves the original first-fibre weight
as a measure identity, including every zero-mass branch. -/
theorem refreshAgain_map :
    ((Lambda).prod (refreshAuxiliaryLaw b t)).map
      (fun wa => refreshAgain rate rewards C_star C_h b u t wa.1 wa.2) = Lambda := by
  let R := fun wa : Lift × RefreshAuxiliary b t =>
    refreshAgain rate rewards C_star C_h b u t wa.1 wa.2
  have hR : Measurable R := measurable_refreshAgain rate rewards C_star C_h b u t
  ext A hA
  apply (measureReal_eq_measureReal_iff).mp
  let f : Lift → ℝ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have hb (w) : ‖f w‖ ≤ 1 := by
    by_cases hw : w ∈ A <;> simp only [f, Set.indicator, hw, ite_true, ite_false, norm_one,
      norm_zero, zero_le_one, le_refl]
  have hi : Integrable (f ∘ R) ((Lambda).prod (refreshAuxiliaryLaw b t)) :=
    Integrable.of_bound (hf.comp hR).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => hb (R x))
  calc
    _ = ∫ w, f w ∂((Lambda).prod (refreshAuxiliaryLaw b t)).map R :=
      (integral_indicator_one hA).symm
    _ = ∫ x, f (R x) ∂(Lambda).prod (refreshAuxiliaryLaw b t) :=
      integral_map hR.aemeasurable hf.aestronglyMeasurable
    _ = ∫ w, ∫ a, f (refreshAgain rate rewards C_star C_h b u t w a)
        ∂refreshAuxiliaryLaw b t ∂Lambda := integral_prod _ hi
    _ = ∫ w, f w ∂Lambda :=
      refreshAgain_integral rate rewards C_star C_h control0 b u t f hf 1 hb
    _ = _ := integral_indicator_one hA

/-- Nonnegative Borel transport through the SAME fresh-block resampling. -/
theorem lintegral_refreshAgain (f : Lift → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, ∫⁻ a, f (refreshAgain rate rewards C_star C_h b u t w a)
      ∂refreshAuxiliaryLaw b t ∂Lambda) = ∫⁻ w, f w ∂Lambda := by
  calc
    _ = ∫⁻ wa : Lift × RefreshAuxiliary b t,
        f (refreshAgain rate rewards C_star C_h b u t wa.1 wa.2)
        ∂(Lambda).prod (refreshAuxiliaryLaw b t) :=
      (lintegral_prod _ (hf.comp
        (measurable_refreshAgain rate rewards C_star C_h b u t)).aemeasurable).symm
    _ = ∫⁻ w, f w ∂((Lambda).prod (refreshAuxiliaryLaw b t)).map
        (fun wa => refreshAgain rate rewards C_star C_h b u t wa.1 wa.2) :=
      (lintegral_map hf (measurable_refreshAgain rate rewards C_star C_h b u t)).symm
    _ = _ := by rw [refreshAgain_map rate rewards C_star C_h control0 b u t]


/-- The native next-call slice is a physical source event; it excludes the
boundary call from the preceding open interval and includes that call at q. -/
def physicalNextEvent : Set (Source p) :=
  {z | NoCallBetween rate rewards C_star C_h t q.castSucc z ∧
    ¬ ReferenceFirstCollectionLogicalPrefixExtension.noCallAt rate rewards C_star C_h q z}

theorem measurableSet_physicalNextEvent (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet (physicalNextEvent rate rewards C_star C_h t q) :=
  (measurableSet_noCallBetween rate rewards C_star C_h control0 t q.castSucc).inter
    (ReferenceFirstCollectionLogicalPrefixExtension.measurableSet_noCallAt
      rate rewards C_star C_h control0 q).compl

theorem firstNextEvent_eq_preimage :
    E = (fun w : Lift => (O q.castSucc w).1.1.1.2) ⁻¹'
      physicalNextEvent rate rewards C_star C_h t q := rfl

/-- The accepted first insertion retains the entire source, including J. -/
theorem branchLaw_map_source :
    (Lambda).map (fun w : Lift => (O q.castSucc w).1.1.1.2) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (branchEvent rate rewards C_star C_h b u t) := by
  cases b with
  | false =>
      exact ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw_map_inserted_source
        rate rewards C_star C_h u t control0
  | true =>
      change (ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t).map
          (fun w => (ReferenceFirstCollectionRenewalVectorInsertion.put
            rate rewards C_star C_h u t w.1.1 w.2).val) = _
      simp_rw [ReferenceFirstCollectionRenewalVectorInsertion.put_val]
      exact ReferenceFirstCollectionRenewalInsertedSourceLaw.renewalLiftLaw_map_inserted_source
        rate rewards C_star C_h u t

/-- Exact original-source identification of the unnormalized RHS. -/
theorem firstNext_source_marginal :
    ((Lambda).restrict E).map (fun w : Lift => (O q.castSucc w).1.1.1.2) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (branchEvent rate rewards C_star C_h b u t ∩
          physicalNextEvent rate rewards C_star C_h t q) := by
  rw [firstNextEvent_eq_preimage, ← Measure.restrict_map
    (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).fst.fst.fst.snd
    (measurableSet_physicalNextEvent rate rewards C_star C_h t q control0),
    branchLaw_map_source, Measure.restrict_restrict
      (measurableSet_physicalNextEvent rate rewards C_star C_h t q control0), Set.inter_comm]


private theorem measurable_option_cases {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (o : X → Option A) (ho : Measurable o) (f : X → B) (hf : Measurable f)
    (g : X × A → B) (hg : Measurable g) :
    Measurable (fun x => match o x with | none => f x | some a => g (x, a)) := by
  have hs := hg.sumElim (hf.comp (measurable_fst : Measurable (Prod.fst : X × PUnit → X)))
  have he := (MeasurableEquiv.prodSumDistrib X A PUnit).measurable.comp
    (measurable_id.prodMk ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp ho))
  convert hs.comp he using 1
  funext x
  cases h : o x <;> simp only [Function.comp_apply, id_eq, h] <;> rfl

/-- The mass of the actual requested endpoint; absence has no endpoint mass. -/
def installationMass (i : NextInput rate t q) : ℝ≥0∞ :=
  match installationSelection rate rewards C_star C_h (t := t) q i with
  | none => 0
  | some a => AssignmentParameterFibreKernel.fibreMass p a.1 a.2

theorem measurable_installationMass (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (installationMass rate rewards C_star C_h (t := t) q) := by
  unfold installationMass
  convert measurable_option_cases _
    (measurable_installationSelection rate rewards C_star C_h (t := t) (q := q) control0)
    (fun _ => 0) measurable_const _
    ((AssignmentParameterFibreKernel.measurable_fibreMass_joint p).comp measurable_snd) using 1
  funext i
  cases installationSelection rate rewards C_star C_h (t := t) q i <;> rfl

private theorem installationSelection_retained (w : Lift)
    (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
    (hc : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q
      (O q.castSucc w).1.1.1.2 = some (cutoff, theta))
    (hclear : preClearFlag rate (t := t) q (O q.castSucc w) = true)
    (hnr : renewalFlag rate rewards C_star C_h (t := t) q (O q.castSucc w) = false) :
    installationSelection rate rewards C_star C_h (t := t) q
      (actualNextInput rate rewards C_star C_h control0 b u t q w) =
        some (theta, retainedEndpoint rate (t := t) q (O q.castSucc w)) := by
  simp only [installationSelection, actualNextInput, hc, hclear, ite_true,
    installationEndpoint, endpointChoice, hnr, Bool.false_eq_true, ite_false]

/-- Zero endpoint atoms disappear under the actual fresh-block law. This
support statement is derived on the original retained event, not assumed. -/
theorem ae_retained_installationMass_pos (htq : t.val < q.val) :
    ∀ᵐ w ∂(Lambda).restrict (retainedNextEvent rate rewards C_star C_h control0 b u t q),
      0 < installationMass rate rewards C_star C_h (t := t) q
        (actualNextInput rate rewards C_star C_h control0 b u t q w) := by
  let Er := retainedNextEvent rate rewards C_star C_h control0 b u t q
  let m := fun w : Lift => installationMass rate rewards C_star C_h (t := t) q
    (actualNextInput rate rewards C_star C_h control0 b u t q w)
  have hm : Measurable m :=
    (measurable_installationMass rate rewards C_star C_h (t := t) q control0).comp
      (measurable_actualNextInput rate rewards C_star C_h control0 b u t q)
  have hEr := measurableSet_retainedNextEvent rate rewards C_star C_h control0 b u t q
  have hgood : MeasurableSet {w | w ∈ Er → 0 < m w} := by
    convert hEr.compl.union (measurableSet_lt (measurable_const (a := (0 : ℝ≥0∞))) hm) using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
    exact imp_iff_not_or
  have hsection (w : Lift) : ∀ᵐ a ∂refreshAuxiliaryLaw b t,
      refreshAgain rate rewards C_star C_h b u t w a ∈ Er →
        0 < m (refreshAgain rate rewards C_star C_h b u t w a) := by
    by_cases hw : w ∈ Er
    · obtain ⟨cutoff, theta, hc, _hnone, hatom⟩ :=
        actual_nextNonrenewed_refresh_atoms rate rewards C_star C_h control0 b u t q htq
          w hw.1 hw.2.1 hw.2.2
      let wa := fun a : RefreshAuxiliary b t => refreshAgain rate rewards C_star C_h b u t w a
      let endpoint := fun a => retainedEndpoint rate (t := t) q (O q.castSucc (wa a))
      have hall : ∀ᵐ a ∂refreshAuxiliaryLaw b t, ∀ A : Outcome p,
          AssignmentParameterFibreKernel.fibreMass p theta A = 0 → endpoint a ≠ A := by
        apply (ae_all_iff).mpr
        intro A
        by_cases hA : AssignmentParameterFibreKernel.fibreMass p theta A = 0
        · have hz : refreshAuxiliaryLaw b t {a | endpoint a = A} = 0 :=
            (hatom (refreshSplit b t w.1.2).1 A).trans hA
          filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with a ha
          exact fun _ => ha
        · exact Filter.Eventually.of_forall fun _ h => (hA h).elim
      filter_upwards [hall] with a ha _
      have hs := withAuxiliary_source rate rewards C_star C_h control0 b u t q.castSucc w
        ((refreshSplit b t).symm ((refreshSplit b t w.1.2).1, a))
      change (O q.castSucc (wa a)).1.1.1.2 = (O q.castSucc w).1.1.1.2 at hs
      have hn : (O q.castSucc (wa a)).2.2.1 = (O q.castSucc w).2.2.1 := by cases b <;> rfl
      have hclear : preClearFlag rate (t := t) q (O q.castSucc (wa a)) = true := by
        simpa only [preClearFlag, hn] using hw.2.1
      have hnr : renewalFlag rate rewards C_star C_h (t := t) q (O q.castSucc (wa a)) = false := by
        simpa only [renewalFlag, hs] using hw.2.2
      have hsel := installationSelection_retained rate rewards C_star C_h control0 b u t q
        (wa a) cutoff theta (hs ▸ hc) hclear hnr
      change 0 < installationMass rate rewards C_star C_h (t := t) q
        (actualNextInput rate rewards C_star C_h control0 b u t q (wa a))
      rw [installationMass, hsel]
      exact bot_lt_iff_ne_bot.mpr (fun hz => ha (endpoint a) hz rfl)
    · exact Filter.Eventually.of_forall fun a ha => (hw
        ((withAuxiliary_retainedNextEvent_iff rate rewards C_star C_h control0 b u t q w _).mp ha)).elim
  have hp : ∀ᵐ wa ∂(Lambda).prod (refreshAuxiliaryLaw b t),
      refreshAgain rate rewards C_star C_h b u t wa.1 wa.2 ∈ Er →
        0 < m (refreshAgain rate rewards C_star C_h b u t wa.1 wa.2) :=
    (Measure.ae_prod_iff_ae_ae
      (hgood.preimage (measurable_refreshAgain rate rewards C_star C_h b u t))).mpr
        (Filter.Eventually.of_forall hsection)
  have hmap := (ae_map_iff
    (measurable_refreshAgain rate rewards C_star C_h b u t).aemeasurable hgood).mpr hp
  rw [refreshAgain_map rate rewards C_star C_h control0 b u t] at hmap
  exact (ae_restrict_iff' hEr).mpr hmap

private theorem productParameter_none_mass (theta : AssignmentParameterFibreKernel.Theta p)
    (hp : ∀ j, 0 < theta.2 j)
    (hm : theta.1 = LaterAssignmentStartOperation.productQOnPrefixCarrier theta.2) :
    AssignmentParameterFibreKernel.fibreMass p theta none = 0 := by
  have htheta : theta =
      ((CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K theta.2 hp).weight,
        theta.2) := Prod.ext hm rfl
  have hs (v : Vector p) : AssignmentParameterFibreKernel.successfulSlowSet p theta v =
      some (CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K theta.2 theta.2 hp hp v) := by
    conv_lhs => rw [htheta]
    exact CheckedAssignmentSample.productQ_successfulSlowSet_eq_canonical p theta.2 theta.2 hp hp v
  change ContinuousControlSlice.assignmentLaw p.K {v | _ = none} = 0
  simp_rw [hs]
  simp only [reduceCtorEq, Set.ofPred_false, measure_empty]

/-- Renewal's actual parameter is positive and its failure atom is zero. -/
theorem actual_nextRenewal_none_mass (htq : t.val < q.val) (w : Lift)
    (hw : w ∈ E)
    (hrenew : renewalFlag rate rewards C_star C_h (t := t) q (O q.castSucc w) = true) :
    ∃ cutoff theta,
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q
        (O q.castSucc w).1.1.1.2 = some (cutoff, theta) ∧
      (∀ j, 0 < theta.2 j) ∧
      theta.1 = LaterAssignmentStartOperation.productQOnPrefixCarrier theta.2 ∧
      AssignmentParameterFibreKernel.fibreMass p theta none = 0 := by
  obtain ⟨cutoff, theta, hc, hp, hm⟩ :=
    actual_nextRenewal_parameter rate rewards C_star C_h control0 b u t q htq w hw hrenew
  exact ⟨cutoff, theta, hc, hp, hm, productParameter_none_mass theta hp hm⟩


/-- Borel equality of the sampled vector's actual outcome and the requested
endpoint. Absence requests no insertion and imposes no sampler assertion. -/
def fibreMatch (iv : NextInput rate t q × Vector p) : Bool :=
  match installationSelection rate rewards C_star C_h (t := t) q iv.1 with
  | none => true
  | some a => decide (AssignmentParameterFibreKernel.successfulSlowSet p a.1 iv.2 = a.2)

theorem measurable_fibreMatch (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (fibreMatch rate rewards C_star C_h (t := t) q) := by
  unfold fibreMatch
  have he : Measurable (fun z : (NextInput rate t q × Vector p) ×
      (AssignmentParameterFibreKernel.Theta p × Outcome p) =>
      decide (AssignmentParameterFibreKernel.successfulSlowSet p z.2.1 z.1.2 = z.2.2)) :=
    (measurable_of_countable (fun v : Outcome p × Outcome p => decide (v.1 = v.2))).comp
      (((AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
        (measurable_snd.fst.prodMk measurable_fst.snd)).prodMk measurable_snd.snd)
  convert measurable_option_cases _
    ((measurable_installationSelection rate rewards C_star C_h (t := t) (q := q) control0).comp
      measurable_fst) (fun _ => true) measurable_const _ he using 1
  funext iv
  cases hs : installationSelection rate rewards C_star C_h (t := t) q iv.1 <;>
    simp only [Function.comp_apply, hs]

/-- On the actual next-call slice every PRE-clear instruction has positive
support; renewal uses fresh ORIGINAL q label one, retained calls their own
varying generated endpoint. -/
theorem ae_firstNext_installationMass_pos (htq : t.val < q.val) :
    ∀ᵐ w ∂(Lambda).restrict E,
      preClearFlag rate (t := t) q (O q.castSucc w) = true →
        0 < installationMass rate rewards C_star C_h (t := t) q
          (actualNextInput rate rewards C_star C_h control0 b u t q w) := by
  have hret := (ae_restrict_iff'
    (measurableSet_retainedNextEvent rate rewards C_star C_h control0 b u t q)).mp
      (ae_retained_installationMass_pos rate rewards C_star C_h control0 b u t q htq)
  filter_upwards [ae_restrict_of_ae hret,
    ae_restrict_mem (measurableSet_firstNextEvent rate rewards C_star C_h control0 b u t q)]
      with w hret hw hclear
  cases hr : renewalFlag rate rewards C_star C_h (t := t) q (O q.castSucc w) with
  | false => exact hret ⟨hw, hclear, hr⟩
  | true =>
      obtain ⟨cutoff, theta, hc, _hp, _hm, _hnone⟩ :=
        actual_nextRenewal_none_mass rate rewards C_star C_h control0 b u t q htq w hw hr
      simp only [installationMass, installationSelection, actualNextInput, hc, hclear, ite_true,
        installationEndpoint, endpointChoice, hr]
      exact freshEndpoint_mass_pos theta _

/-- The canonical fibre kernel has the requested graph on this SAME original
branch extension. Positive support is an output of the preceding proof. -/
theorem ae_nextLiftLaw_fibreMatch (htq : t.val < q.val) :
    ∀ᵐ wv ∂nextLiftLaw rate rewards C_star C_h control0 b u t q,
      fibreMatch rate rewards C_star C_h (t := t) q
        (actualNextInput rate rewards C_star C_h control0 b u t q wv.1, wv.2) = true := by
  have hmap : Measurable (fun wv : Lift × Vector p =>
      (actualNextInput rate rewards C_star C_h control0 b u t q wv.1, wv.2)) :=
    ((measurable_actualNextInput rate rewards C_star C_h control0 b u t q).comp
      measurable_fst).prodMk measurable_snd
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun ((measurable_fibreMatch rate rewards C_star C_h (t := t) q control0).comp hmap)
      measurable_const)
  filter_upwards [ae_firstNext_installationMass_pos rate rewards C_star C_h control0 b u t q htq]
    with w hw
  let i := actualNextInput rate rewards C_star C_h control0 b u t q w
  cases hs : installationSelection rate rewards C_star C_h (t := t) q i with
  | none =>
      exact Filter.Eventually.of_forall fun v => by
        change fibreMatch rate rewards C_star C_h (t := t) q (i, v) = true
        simp only [fibreMatch, hs]
  | some a =>
      have hclear : preClearFlag rate (t := t) q i.1 = true := by
        by_contra hn
        have hf : preClearFlag rate (t := t) q i.1 = false := Bool.eq_false_iff.mpr hn
        have hz : installationSelection rate rewards C_star C_h (t := t) q i = none := by
          unfold installationSelection
          cases ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q i.1.1.1.1.2 <;>
            simp only [hf, Bool.false_eq_true, ite_false]
        rw [hz] at hs
        cases hs
      have hmass := hw hclear
      change 0 < installationMass rate rewards C_star C_h (t := t) q i at hmass
      rw [installationMass, hs] at hmass
      have hkernel : actualNextVectorKernel rate rewards C_star C_h control0 b u t q w =
          AssignmentParameterFibreKernel.fibreMeasure p a.1 a.2 := by
        change nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0 i = _
        rw [nextVectorKernel_apply, hs]
      rw [hkernel]
      filter_upwards [AssignmentParameterFibreKernel.ae_successfulSlowSet_eq_of_fibreMass_pos p a.1 a.2 hmass]
        with v hv
      change fibreMatch rate rewards C_star C_h (t := t) q (i, v) = true
      simp only [fibreMatch, hs, hv, decide_true]

/-- Retaining the original lift preserves every Borel observer jointly. -/
theorem nextInsertedLaw_map_observer {X : Type*} [MeasurableSpace X]
    (f : Lift → X) (hf : Measurable f) :
    (nextInsertedLaw rate rewards C_star C_h control0 b u t q).map (fun x => f x.1) =
      ((Lambda).restrict E).map f := by
  rw [← nextInsertedLaw_map_original rate rewards C_star C_h control0 b u t q,
    Measure.map_map hf measurable_fst]
  rfl

/-- The matching statement on the complete correlated readout. -/
theorem ae_nextInsertedLaw_fibreMatch (htq : t.val < q.val) :
    ∀ᵐ x ∂nextInsertedLaw rate rewards C_star C_h control0 b u t q,
      fibreMatch rate rewards C_star C_h (t := t) q
        (actualNextInput rate rewards C_star C_h control0 b u t q x.1, x.2.1) = true := by
  apply (ae_map_iff
    (measurable_nextInsertedReadout rate rewards C_star C_h control0 b u t q).aemeasurable
      (measurableSet_eq_fun
        ((measurable_fibreMatch rate rewards C_star C_h (t := t) q control0).comp
          (((measurable_actualNextInput rate rewards C_star C_h control0 b u t q).comp
            measurable_fst).prodMk measurable_snd.fst)) measurable_const)).mpr
  exact ae_nextLiftLaw_fibreMatch rate rewards C_star C_h control0 b u t q htq


/-- Only physical source and candidate vector are projected here. The full
old observer remains in `nextInsertedLaw`; this projection does not assert
independence after revealing that observer. -/
def sourceVectorReadout (wv : Lift × Vector p) : Source p × Vector p :=
  ((O q.castSucc wv.1).1.1.1.2, wv.2)

theorem measurable_sourceVectorReadout :
    Measurable (sourceVectorReadout rate rewards C_star C_h control0 b u t q) :=
  ((measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).fst.fst.fst.snd.comp
    measurable_fst).prodMk measurable_snd

/-- The actual retained fresh-block averaging gives the whole assignment
cube jointly with the ENTIRE physical source on the actual retained slice. -/
theorem retained_source_vector_product (htq : t.val < q.val) :
    (((Lambda).restrict (retainedNextEvent rate rewards C_star C_h control0 b u t q)).compProd
      (actualNextVectorKernel rate rewards C_star C_h control0 b u t q)).map
        (sourceVectorReadout rate rewards C_star C_h control0 b u t q) =
    (((Lambda).restrict (retainedNextEvent rate rewards C_star C_h control0 b u t q)).map
      (fun w : Lift => (O q.castSucc w).1.1.1.2)).prod
        (ContinuousControlSlice.assignmentLaw p.K) := by
  let Er := retainedNextEvent rate rewards C_star C_h control0 b u t q
  let S := fun w : Lift => (O q.castSucc w).1.1.1.2
  let k := actualNextVectorKernel rate rewards C_star C_h control0 b u t q
  have hEr := measurableSet_retainedNextEvent rate rewards C_star C_h control0 b u t q
  have hS : Measurable S :=
    (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).fst.fst.fst.snd
  have hread := measurable_sourceVectorReadout rate rewards C_star C_h control0 b u t q
  apply Measure.ext_prod
  intro A B hA hB
  let f : Lift → ℝ≥0∞ := fun w => if w ∈ Er then if S w ∈ A then k w B else 0 else 0
  have hf : Measurable f :=
    Measurable.ite hEr (Measurable.ite (hS hA) (ProbabilityTheory.Kernel.measurable_coe k hB)
      measurable_const) measurable_const
  have hleft : (((Lambda).restrict Er).compProd k).map
      (sourceVectorReadout rate rewards C_star C_h control0 b u t q) (A ×ˢ B) = ∫⁻ w, f w ∂Lambda := by
    rw [Measure.map_apply hread (hA.prod hB), Measure.compProd_apply (hread (hA.prod hB)),
      ← lintegral_indicator hEr]
    apply lintegral_congr
    intro w
    have hsection : Prod.mk w ⁻¹' ((sourceVectorReadout rate rewards C_star C_h control0 b u t q) ⁻¹'
        (A ×ˢ B)) = if S w ∈ A then B else ∅ := by
      ext v
      by_cases ha : S w ∈ A <;> simp only [sourceVectorReadout, Set.mem_preimage, Set.mem_prod,
        S, ha, true_and, false_and, ite_true, ite_false, Set.mem_empty_iff_false]
    change (if w ∈ Er then k w (Prod.mk w ⁻¹'
      ((sourceVectorReadout rate rewards C_star C_h control0 b u t q) ⁻¹' (A ×ˢ B))) else 0) = f w
    rw [hsection]
    by_cases hw : w ∈ Er <;> by_cases ha : S w ∈ A <;>
      simp only [f, hw, ha, ite_true, ite_false, measure_empty]
  have havg (w : Lift) :
      (∫⁻ a, f (refreshAgain rate rewards C_star C_h b u t w a) ∂refreshAuxiliaryLaw b t) =
        if w ∈ Er then if S w ∈ A then ContinuousControlSlice.assignmentLaw p.K B else 0 else 0 := by
    have he (a : RefreshAuxiliary b t) : refreshAgain rate rewards C_star C_h b u t w a ∈ Er ↔ w ∈ Er :=
      withAuxiliary_retainedNextEvent_iff rate rewards C_star C_h control0 b u t q w _
    have hs (a : RefreshAuxiliary b t) : S (refreshAgain rate rewards C_star C_h b u t w a) = S w :=
      withAuxiliary_source rate rewards C_star C_h control0 b u t q.castSucc w _
    simp only [f, he, hs]
    by_cases hw : w ∈ Er
    · simp only [hw, ite_true]
      by_cases ha : S w ∈ A
      · simp only [ha, ite_true]
        exact retainedNext_vector_marginal rate rewards C_star C_h control0 b u t q htq w hw
          (refreshSplit b t w.1.2).1 B hB
      · simp only [ha, ite_false, lintegral_zero]
    · simp only [hw, ite_false, lintegral_zero]
  rw [hleft, ← lintegral_refreshAgain rate rewards C_star C_h control0 b u t f hf]
  simp_rw [havg]
  rw [Measure.prod_prod, Measure.map_apply hS hA, Measure.restrict_apply (hS hA)]
  calc
    _ = ∫⁻ w, (S ⁻¹' A ∩ Er).indicator (fun _ => ContinuousControlSlice.assignmentLaw p.K B) w
        ∂Lambda := by
      apply lintegral_congr
      intro w
      by_cases hw : w ∈ Er <;> by_cases ha : S w ∈ A <;>
        simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, hw, ha, and_true,
          and_false, ite_true, ite_false]
    _ = _ := by rw [lintegral_indicator_const ((hS hA).inter hEr), mul_comm]


private theorem measurable_freshEndpoint_fixed (theta : AssignmentParameterFibreKernel.Theta p) :
    Measurable (fun x : Scalar => freshEndpoint theta x) := by
  apply measurable_to_countable'
  intro A
  convert (measurableSet_le (measurable_const (a :=
    ContinuousCategorical.lower (fibreAtom theta) ((outcomeEnumeration p).symm A)))
      measurable_subtype_coe).inter
    (measurableSet_lt measurable_subtype_coe (measurable_const (a :=
      ContinuousCategorical.upper (fibreAtom theta) ((outcomeEnumeration p).symm A)))) using 1
  ext x
  exact freshEndpoint_eq_iff theta x A

/-- The renewed fresh endpoint/fibre mixture is the complete assignment cube,
with all finite outcome atoms, including zero and failure atoms. -/
theorem freshEndpoint_vector_marginal (theta : AssignmentParameterFibreKernel.Theta p)
    (B : Set (Vector p)) :
    (∫⁻ x : Scalar, AssignmentParameterFibreKernel.fibreMeasure p theta (freshEndpoint theta x) B
      ∂ContinuousControlSlice.scalarLaw) = ContinuousControlSlice.assignmentLaw p.K B := by
  let endpoint : Scalar → Outcome p := fun x => freshEndpoint theta x
  have he : Measurable endpoint := measurable_freshEndpoint_fixed theta
  have hf : Measurable (fun A : Outcome p => AssignmentParameterFibreKernel.fibreMeasure p theta A B) :=
    measurable_of_countable _
  rw [← lintegral_map hf he, lintegral_fintype]
  calc
    _ = ∑ A : Outcome p, AssignmentParameterFibreKernel.fibreMass p theta A *
        AssignmentParameterFibreKernel.fibreMeasure p theta A B := by
      apply Finset.sum_congr rfl
      intro A _
      rw [Measure.map_apply he (measurableSet_singleton A)]
      change AssignmentParameterFibreKernel.fibreMeasure p theta A B *
        ContinuousControlSlice.scalarLaw {x | freshEndpoint theta x = A} = _
      rw [freshEndpoint_fibre, mul_comm]
    _ = _ := by
      have h := congrArg (fun mu : Measure (Vector p) => mu B)
        (AssignmentParameterFibreKernel.sum_fibreMass_smul_fibreMeasure p theta)
      simpa only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul] using h

private theorem freshEndpoint_pair_vector_marginal
    (theta : AssignmentParameterFibreKernel.Theta p) (B : Set (Vector p)) :
    (∫⁻ x : Scalar × Scalar,
      AssignmentParameterFibreKernel.fibreMeasure p theta (freshEndpoint theta x.2) B
      ∂ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) =
        ContinuousControlSlice.assignmentLaw p.K B := by
  let f : Scalar → ℝ≥0∞ := fun x =>
    AssignmentParameterFibreKernel.fibreMeasure p theta (freshEndpoint theta x) B
  have htest : Measurable (fun A : Outcome p => AssignmentParameterFibreKernel.fibreMeasure p theta A B) :=
    measurable_of_countable _
  have hf : Measurable f := htest.comp (measurable_freshEndpoint_fixed theta)
  change (∫⁻ x : Scalar × Scalar, f x.2
    ∂ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) = _
  rw [← lintegral_map hf measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  exact freshEndpoint_vector_marginal theta B

/-- The literal renewed PRE observation event. -/
def renewedObservationEvent : Set (PrefixObservation rate t q.castSucc) :=
  {o | o.1.1.1.2 ∈ physicalNextEvent rate rewards C_star C_h t q ∧
    preClearFlag rate (t := t) q o = true ∧
      renewalFlag rate rewards C_star C_h (t := t) q o = true}

theorem measurableSet_renewedObservationEvent (control0 : ContinuousLearningRows.TimeControl p) :
    MeasurableSet (renewedObservationEvent rate rewards C_star C_h (t := t) q) :=
  ((measurableSet_physicalNextEvent rate rewards C_star C_h t q control0).preimage
    measurable_fst.fst.fst.snd).inter
      ((measurableSet_eq_fun (measurable_preClearFlag rate (t := t) q) measurable_const).inter
        (measurableSet_eq_fun (measurable_renewalFlag rate rewards C_star C_h (t := t) q) measurable_const))

/-- The original lift's actual renewed, PRE-clear, first-next-call event. -/
def renewedNextEvent : Set Lift :=
  (O q.castSucc) ⁻¹' renewedObservationEvent rate rewards C_star C_h (t := t) q

theorem measurableSet_renewedNextEvent :
    MeasurableSet (renewedNextEvent rate rewards C_star C_h control0 b u t q) :=
  (measurableSet_renewedObservationEvent rate rewards C_star C_h (t := t) q control0).preimage
    (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc)


/-- The new source is the literal insertion on this very old lift/vector
sample, without a diagonal old/new source assertion. -/
theorem ae_nextInsertedLaw_readout :
    ∀ᵐ x ∂nextInsertedLaw rate rewards C_star C_h control0 b u t q,
      x.2.2 = ReferenceFirstCollectionRenewalVectorInsertion.insert q
        (O q.castSucc x.1).1.1.1.2 x.2.1 := by
  have hi : Measurable (fun x : Lift × (Vector p × Source p) =>
      ReferenceFirstCollectionRenewalVectorInsertion.insert q (O q.castSucc x.1).1.1.1.2 x.2.1) :=
    (ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert (t := q)).comp
      (((measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).fst.fst.fst.snd.comp
        measurable_fst).prodMk measurable_snd.fst)
  apply (ae_map_iff
    (measurable_nextInsertedReadout rate rewards C_star C_h control0 b u t q).aemeasurable
      (measurableSet_eq_fun measurable_snd.snd hi)).mpr
  exact Filter.Eventually.of_forall fun _ => rfl

/-- PRE numerical state, generated endpoint/list, original seed and used
auxiliary array all remain the SAME data for the native next-call consumer. -/
theorem ae_nextInsertedLaw_pre_locality :
    ∀ᵐ x ∂nextInsertedLaw rate rewards C_star C_h control0 b u t q,
      prefixNumerical rate rewards C_star C_h q.castSucc x.2.2 = (O q.castSucc x.1).2.2.1 ∧
      noncallCalendar rate rewards C_star C_h t x.2.2 x.1.1.2
        (postSeed rate (branchTransition rate rewards C_star C_h control0 b u t x.1),
          postHistory (branchTransition rate rewards C_star C_h control0 b u t x.1)) q.val =
            (O q.castSucc x.1).2.2.2 ∧
      x.2.2.2 = (O q.castSucc x.1).1.1.1.2.2 ∧
      ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q x.2.2 =
        ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q
          (O q.castSucc x.1).1.1.1.2 := by
  filter_upwards [ae_nextInsertedLaw_readout rate rewards C_star C_h control0 b u t q] with x hx
  rw [hx]
  refine ⟨?_, actual_inserted_history rate rewards C_star C_h control0 b u t q x.1 x.2.1,
    (ReferenceFirstCollectionRenewalVectorInsertion.insert_identity_private_selector q _ _).2.1, ?_⟩
  · rw [insertReadout_numerical rate rewards C_star C_h (t := t) q control0]
    cases b <;> rfl
  · rw [ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 q,
      ReferenceFirstCollectionRenewalVectorInsertion.insert,
      ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl,
      ← ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 q]


/-- Actual new-source sampler graph on BOTH PRE-clear branches. Its endpoint
is the canonical retained endpoint or ORIGINAL q label-one fresh draw. The
parameter, non-failure and positive support are derived on the same sample. -/
theorem ae_nextInsertedLaw_sampler_graph (htq : t.val < q.val) :
    ∀ᵐ x ∂nextInsertedLaw rate rewards C_star C_h control0 b u t q,
      preClearFlag rate (t := t) q (O q.castSucc x.1) = true →
      ∃ (cutoff : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
        (U : SlowSet p) (output : LaterAssignmentFullOutputMeasurability.FullOutputObservation p),
        ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q x.2.2 =
          some (cutoff, theta) ∧
        ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h q x.2.2 = some output ∧
        output.2.1 = some theta ∧
        output.1 = LaterAssignmentStartMeasurability.codeOfCheckedSample p
          (CheckedAssignmentSample.checkedAssignmentSample p theta.1 theta.2
            (ReferenceFirstCollectionRenewalVectorInsertion.av q x.2.2)) ∧
        AssignmentParameterFibreKernel.successfulSlowSet p theta
          (ReferenceFirstCollectionRenewalVectorInsertion.av q x.2.2) = some U ∧
        installationEndpoint rate rewards C_star C_h (t := t) q
          (actualNextInput rate rewards C_star C_h control0 b u t q x.1, theta) = some U ∧
        0 < AssignmentParameterFibreKernel.fibreMass p theta (some U) ∧
        AssignmentParameterFibreKernel.fibreMass p theta none = 0 := by
  have hmem := ae_restrict_mem
    (μ := Lambda) (measurableSet_firstNextEvent rate rewards C_star C_h control0 b u t q)
  have hpos := ae_firstNext_installationMass_pos rate rewards C_star C_h control0 b u t q htq
  rw [← nextInsertedLaw_map_original rate rewards C_star C_h control0 b u t q] at hmem hpos
  have hm := ae_of_ae_map measurable_fst.aemeasurable hmem
  have hp := ae_of_ae_map measurable_fst.aemeasurable hpos
  filter_upwards [hm, hp, ae_nextInsertedLaw_readout rate rewards C_star C_h control0 b u t q,
    ae_nextInsertedLaw_pre_locality rate rewards C_star C_h control0 b u t q,
    ae_nextInsertedLaw_fibreMatch rate rewards C_star C_h control0 b u t q htq]
      with x hx hpos hread hlocal hmatch hclear
  obtain ⟨_hbetween, cutoff, theta, hc⟩ :=
    (firstNextEvent_iff rate rewards C_star C_h control0 b u t q x.1).mp hx
  let i := actualNextInput rate rewards C_star C_h control0 b u t q x.1
  let endpoint := installationEndpoint rate rewards C_star C_h (t := t) q (i, theta)
  have hsel : installationSelection rate rewards C_star C_h (t := t) q i = some (theta, endpoint) := by
    simp only [installationSelection, i, actualNextInput, hc, hclear, ite_true, endpoint]
  have hmass := hpos hclear
  change 0 < installationMass rate rewards C_star C_h (t := t) q i at hmass
  rw [installationMass, hsel] at hmass
  change 0 < AssignmentParameterFibreKernel.fibreMass p theta endpoint at hmass
  have hsampler : AssignmentParameterFibreKernel.successfulSlowSet p theta x.2.1 = endpoint := by
    change fibreMatch rate rewards C_star C_h (t := t) q (i, x.2.1) = true at hmatch
    simpa only [fibreMatch, hsel, decide_eq_true_eq] using hmatch
  have hnone : AssignmentParameterFibreKernel.fibreMass p theta none = 0 := by
    cases hr : renewalFlag rate rewards C_star C_h (t := t) q (O q.castSucc x.1) with
    | false =>
        obtain ⟨cutoff', theta', hc', hn, _hatom⟩ :=
          actual_nextNonrenewed_refresh_atoms rate rewards C_star C_h control0 b u t q htq
            x.1 hx hclear hr
        have he : theta' = theta := congrArg Prod.snd (Option.some.inj (hc'.symm.trans hc))
        exact he ▸ hn
    | true =>
        obtain ⟨cutoff', theta', hc', _hp, _hm, hn⟩ :=
          actual_nextRenewal_none_mass rate rewards C_star C_h control0 b u t q htq x.1 hx hr
        have he : theta' = theta := congrArg Prod.snd (Option.some.inj (hc'.symm.trans hc))
        exact he ▸ hn
  have hnotnone : endpoint ≠ none := by
    intro he
    rw [he, hnone] at hmass
    exact (lt_irrefl _ hmass)
  obtain ⟨U, he⟩ := Option.ne_none_iff_exists'.mp hnotnone
  obtain ⟨output, ho, htheta, hcode⟩ :=
    insertReadout_actual_checkedSample rate rewards C_star C_h (t := t) q control0
      (O q.castSucc x.1) x.2.1 cutoff theta hc
  rw [← hread] at ho
  have hv : ReferenceFirstCollectionRenewalVectorInsertion.av q x.2.2 = x.2.1 := by
    rw [hread, ReferenceFirstCollectionRenewalVectorInsertion.av_insert]
  refine ⟨cutoff, theta, U, output, hlocal.2.2.2.trans hc, ho, htheta, ?_, ?_, he, ?_, hnone⟩
  · rw [hv]
    exact hcode
  · rw [hv]
    exact hsampler.trans he
  · simpa only [he] using hmass


/-- Renewal averages the actual fresh q label one against the full PRE
observation. The original label zero is not relabelled or consumed. -/
theorem renewed_source_vector_product (htq : t.val < q.val) :
    (((Lambda).restrict (renewedNextEvent rate rewards C_star C_h control0 b u t q)).compProd
      (actualNextVectorKernel rate rewards C_star C_h control0 b u t q)).map
        (sourceVectorReadout rate rewards C_star C_h control0 b u t q) =
    (((Lambda).restrict (renewedNextEvent rate rewards C_star C_h control0 b u t q)).map
      (fun w : Lift => (O q.castSucc w).1.1.1.2)).prod
        (ContinuousControlSlice.assignmentLaw p.K) := by
  let Rn := renewedObservationEvent rate rewards C_star C_h (t := t) q
  let En := renewedNextEvent rate rewards C_star C_h control0 b u t q
  let S := fun w : Lift => (O q.castSucc w).1.1.1.2
  let k := actualNextVectorKernel rate rewards C_star C_h control0 b u t q
  have hRn := measurableSet_renewedObservationEvent rate rewards C_star C_h (t := t) q control0
  have hEn := measurableSet_renewedNextEvent rate rewards C_star C_h control0 b u t q
  have hO := measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc
  have hS : Measurable S := hO.fst.fst.fst.snd
  have hread := measurable_sourceVectorReadout rate rewards C_star C_h control0 b u t q
  apply Measure.ext_prod
  intro A B hA hB
  let f : NextInput rate t q → ℝ≥0∞ := fun i => if i.1 ∈ Rn then if i.1.1.1.1.2 ∈ A then
    nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0 i B else 0 else 0
  have hf : Measurable f := Measurable.ite (hRn.preimage measurable_fst)
    (Measurable.ite (measurable_fst.fst.fst.fst.snd hA)
      (ProbabilityTheory.Kernel.measurable_coe
        (nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0) hB) measurable_const)
    measurable_const
  have hleft : (((Lambda).restrict En).compProd k).map
      (sourceVectorReadout rate rewards C_star C_h control0 b u t q) (A ×ˢ B) =
        ∫⁻ w, f (actualNextInput rate rewards C_star C_h control0 b u t q w) ∂Lambda := by
    rw [Measure.map_apply hread (hA.prod hB), Measure.compProd_apply (hread (hA.prod hB)),
      ← lintegral_indicator hEn]
    apply lintegral_congr
    intro w
    have hs : Prod.mk w ⁻¹' ((sourceVectorReadout rate rewards C_star C_h control0 b u t q) ⁻¹'
        (A ×ˢ B)) = if S w ∈ A then B else ∅ := by
      ext v
      by_cases ha : S w ∈ A <;> simp only [sourceVectorReadout, Set.mem_preimage, Set.mem_prod,
        S, ha, true_and, false_and, ite_true, ite_false, Set.mem_empty_iff_false]
    change (if w ∈ En then k w (Prod.mk w ⁻¹' _) else 0) = _
    rw [hs]
    change (if w ∈ En then k w (if S w ∈ A then B else ∅) else 0) =
      if w ∈ En then if S w ∈ A then k w B else 0 else 0
    by_cases hw : w ∈ En <;> by_cases ha : S w ∈ A <;>
      simp only [hw, ha, ite_true, ite_false, measure_empty]
  have havg (o : PrefixObservation rate t q.castSucc) :
      (∫⁻ x : Scalar × Scalar, f (o, x)
        ∂(ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)) =
      if o ∈ Rn then if o.1.1.1.2 ∈ A then ContinuousControlSlice.assignmentLaw p.K B else 0 else 0 := by
    by_cases ho : o ∈ Rn
    · by_cases ha : o.1.1.1.2 ∈ A
      · have hn : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q
            o.1.1.1.2 ≠ none := by
          simpa only [ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none] using ho.1.2
        obtain ⟨⟨cutoff, theta⟩, hc⟩ := Option.ne_none_iff_exists'.mp hn
        have hk (x : Scalar × Scalar) :
            nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0 (o, x) =
              AssignmentParameterFibreKernel.fibreMeasure p theta (freshEndpoint theta x.2) := by
          rw [nextVectorKernel_of_call rate rewards C_star C_h (t := t) (q := q) control0
            (o, x) cutoff theta hc ho.2.1]
          simp only [installationEndpoint, endpointChoice, ho.2.2, ite_true]
        simp only [f, ho, ha, ite_true, hk]
        exact freshEndpoint_pair_vector_marginal theta B
      · simp only [f, ho, ha, ite_true, ite_false, lintegral_zero]
    · simp only [f, ho, ite_false, lintegral_zero]
  let g : PrefixObservation rate t q.castSucc → ℝ≥0∞ := fun o =>
    if o ∈ Rn then if o.1.1.1.2 ∈ A then ContinuousControlSlice.assignmentLaw p.K B else 0 else 0
  have hg : Measurable g := Measurable.ite hRn
    (Measurable.ite (measurable_fst.fst.fst.snd hA) measurable_const measurable_const) measurable_const
  have hj : (Lambda).map (actualNextInput rate rewards C_star C_h control0 b u t q) =
      ((Lambda).map (O q.castSucc)).prod
        (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) :=
    branchObservation_pair_product rate rewards C_star C_h control0 b u t q htq
  rw [hleft, ← lintegral_map hf
    (measurable_actualNextInput rate rewards C_star C_h control0 b u t q),
    hj, lintegral_prod _ hf.aemeasurable]
  simp_rw [havg]
  rw [lintegral_map hg hO, Measure.prod_prod, Measure.map_apply hS hA, Measure.restrict_apply (hS hA)]
  calc
    _ = ∫⁻ w, (S ⁻¹' A ∩ En).indicator (fun _ => ContinuousControlSlice.assignmentLaw p.K B) w
        ∂Lambda := by
      apply lintegral_congr
      intro w
      change (if w ∈ En then if S w ∈ A then _ else 0 else 0) = _
      by_cases hw : w ∈ En <;> by_cases ha : S w ∈ A <;>
        simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, hw, ha, and_true,
          and_false, ite_true, ite_false]
    _ = _ := by rw [lintegral_indicator_const ((hS hA).inter hEn), mul_comm]


/-- Both analytical insertion branches use the actual PRE-clear flag. -/
def clearNextEvent : Set Lift := E ∩ {w | preClearFlag rate (t := t) q (O q.castSucc w) = true}

theorem measurableSet_clearNextEvent :
    MeasurableSet (clearNextEvent rate rewards C_star C_h control0 b u t q) :=
  (measurableSet_firstNextEvent rate rewards C_star C_h control0 b u t q).inter
    (measurableSet_eq_fun ((measurable_preClearFlag rate (t := t) q).comp
      (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc)) measurable_const)

private theorem clearNextEvent_union :
    clearNextEvent rate rewards C_star C_h control0 b u t q =
      retainedNextEvent rate rewards C_star C_h control0 b u t q ∪
        renewedNextEvent rate rewards C_star C_h control0 b u t q := by
  ext w
  change (w ∈ E ∧ preClearFlag rate (t := t) q (O q.castSucc w) = true) ↔
    (w ∈ E ∧ preClearFlag rate (t := t) q (O q.castSucc w) = true ∧
      renewalFlag rate rewards C_star C_h (t := t) q (O q.castSucc w) = false) ∨
    (w ∈ E ∧ preClearFlag rate (t := t) q (O q.castSucc w) = true ∧
      renewalFlag rate rewards C_star C_h (t := t) q (O q.castSucc w) = true)
  cases renewalFlag rate rewards C_star C_h (t := t) q (O q.castSucc w) <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, and_false, and_true, false_or, or_false]

private theorem clearNext_restrict_add :
    (Lambda).restrict (clearNextEvent rate rewards C_star C_h control0 b u t q) =
      (Lambda).restrict (retainedNextEvent rate rewards C_star C_h control0 b u t q) +
        (Lambda).restrict (renewedNextEvent rate rewards C_star C_h control0 b u t q) := by
  rw [clearNextEvent_union]
  apply Measure.restrict_union _ (measurableSet_renewedNextEvent rate rewards C_star C_h control0 b u t q)
  apply Set.disjoint_left.mpr
  intro w hr hn
  exact Bool.false_ne_true (hr.2.2.symm.trans hn.2.2)

/-- Every Borel test of the WHOLE source and assignment vector factors on
PRE-clear calls after integrating the actual retained/renewed endpoint. -/
theorem clear_source_vector_product (htq : t.val < q.val) :
    (((Lambda).restrict (clearNextEvent rate rewards C_star C_h control0 b u t q)).compProd
      (actualNextVectorKernel rate rewards C_star C_h control0 b u t q)).map
        (sourceVectorReadout rate rewards C_star C_h control0 b u t q) =
    (((Lambda).restrict (clearNextEvent rate rewards C_star C_h control0 b u t q)).map
      (fun w : Lift => (O q.castSucc w).1.1.1.2)).prod
        (ContinuousControlSlice.assignmentLaw p.K) := by
  rw [clearNext_restrict_add, Measure.compProd_add_left,
    Measure.map_add _ _ (measurable_sourceVectorReadout rate rewards C_star C_h control0 b u t q),
    retained_source_vector_product rate rewards C_star C_h control0 b u t q htq,
    renewed_source_vector_product rate rewards C_star C_h control0 b u t q htq,
    Measure.map_add _ _
      (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).fst.fst.fst.snd,
    Measure.add_prod]


private theorem controlVectorReplacement_map :
    ((ContinuousLearningRows.timeControlLaw p).prod (ContinuousControlSlice.assignmentLaw p.K)).map
      (fun cv => (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
        (cv.2, ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p) cv.1).2)) =
          ContinuousLearningRows.timeControlLaw p := by
  let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  let tc := ContinuousLearningRows.timeControlLaw p
  let av := ContinuousControlSlice.assignmentLaw p.K
  let nr := (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
    (ContinuousLearningRows.affineSamplesLaw p)
  have he := LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p
  have hm : Measurable (fun c : ContinuousLearningRows.TimeControl p => (e c).2) := e.measurable.snd
  have hr : tc.map (fun c => (e c).2) = nr := by
    change tc.map (Prod.snd ∘ e) = nr
    rw [← Measure.map_map measurable_snd e.measurable, he.map_eq, Measure.map_snd_prod,
      measure_univ, one_smul]
  have hp : (tc.map (fun c => (e c).2)).prod av =
      (tc.prod av).map (Prod.map (fun c => (e c).2) id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map tc av hm measurable_id
  calc
    _ = (((tc.prod av).map (Prod.map (fun c => (e c).2) id)).map Prod.swap).map e.symm := by
      rw [Measure.map_map e.symm.measurable measurable_swap,
        Measure.map_map (e.symm.measurable.comp measurable_swap) (hm.prodMap measurable_id)]
      rfl
    _ = ((nr.prod av).map Prod.swap).map e.symm := by rw [← hp, hr]
    _ = (av.prod nr).map e.symm := by rw [Measure.prod_swap]
    _ = tc := by rw [← he.map_eq]; exact e.map_symm_map

private theorem insert_replace_current (z : Source p) (c : ContinuousLearningRows.TimeControl p)
    (v : Vector p) :
    ReferenceFirstCollectionRenewalVectorInsertion.insert q
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z c) v =
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z
      ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
        (v, ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p) c).2)) := by
  have hc : ReferenceFirstCollectionRenewalVectorInsertion.c q
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z c) = c := by
    simp only [ReferenceFirstCollectionRenewalVectorInsertion.c,
      ReferenceFirstCollectionRenewalVectorInsertion.q,
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
      ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
  rw [ReferenceFirstCollectionRenewalVectorInsertion.insert,
    ReferenceFirstCollectionRenewalVectorInsertion.ctrl, hc]
  simp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    Function.update_self, Function.update_idem]

include control0 in
private theorem physicalNextEvent_replace_current (z : Source p)
    (c : ContinuousLearningRows.TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z c ∈
        physicalNextEvent rate rewards C_star C_h t q ↔
      z ∈ physicalNextEvent rate rewards C_star C_h t q := by
  have hN (x : Source p) : NoCallBetween rate rewards C_star C_h t q.castSucc x ↔
      NoCallBetween rate rewards C_star C_h t q.castSucc
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val x) := by
    simpa only [Fin.val_castSucc] using
      noCallBetween_sourcePrefix rate rewards C_star C_h control0 t q.castSucc x
  have hC (x : Source p) := ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_sourcePrefix
    rate rewards C_star C_h control0 q q.val le_rfl x
  change (NoCallBetween rate rewards C_star C_h t q.castSucc _ ∧
    ¬ ReferenceFirstCollectionLogicalPrefixExtension.noCallAt rate rewards C_star C_h q _) ↔
      (NoCallBetween rate rewards C_star C_h t q.castSucc z ∧
        ¬ ReferenceFirstCollectionLogicalPrefixExtension.noCallAt rate rewards C_star C_h q z)
  rw [hN _, ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl,
    ← hN z, hC _,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl,
    ← hC z]

private theorem restoreControl_source (htq : t.val < q.val) (i : Fin (M p))
    (r : RemainderLift rate rewards C_star C_h control0 b u t q i)
    (c : ContinuousLearningRows.TimeControl p) :
    (O q.castSucc (restoreControl rate rewards C_star C_h control0 b u t q htq i (r, c))).1.1.1.2 =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q
        (O q.castSucc (restoreControl rate rewards C_star C_h control0 b u t q htq i (r, control0))).1.1.1.2 c := by
  cases b with
  | false =>
      exact congrArg (fun x : ((Source p × Source p) ×
        ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) × Vector p => x.1.1.2)
        (ReferenceFirstNextLiftFutureControl.nonrenewedRestoreLift_readout
          rate rewards C_star C_h control0 u t q htq i r.1.1 r.1.2 r.2 c)
  | true =>
      exact congrArg (fun x : ((Source p × Source p) ×
        ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) × Vector p => x.1.1.2)
        (ReferenceFirstNextLiftFutureControl.renewedRestoreLift_readout
          rate rewards C_star C_h control0 u t q htq i r.1.1 r.1.2 r.2 c)

private theorem clearNextEvent_restoreControl (htq : t.val < q.val) (i : Fin (M p))
    (r : RemainderLift rate rewards C_star C_h control0 b u t q i)
    (c : ContinuousLearningRows.TimeControl p) :
    restoreControl rate rewards C_star C_h control0 b u t q htq i (r, c) ∈
        clearNextEvent rate rewards C_star C_h control0 b u t q ↔
      restoreControl rate rewards C_star C_h control0 b u t q htq i (r, control0) ∈
        clearNextEvent rate rewards C_star C_h control0 b u t q := by
  have hn (w : Lift) : (O q.castSucc w).2.2.1 =
      prefixNumerical rate rewards C_star C_h q.castSucc (O q.castSucc w).1.1.1.2 := by cases b <;> rfl
  have hf : preClearFlag rate (t := t) q
      (O q.castSucc (restoreControl rate rewards C_star C_h control0 b u t q htq i (r, c))) =
        preClearFlag rate (t := t) q
          (O q.castSucc (restoreControl rate rewards C_star C_h control0 b u t q htq i (r, control0))) := by
    simp only [preClearFlag, hn]
    rw [restoreControl_source rate rewards C_star C_h control0 b u t q htq i r c,
      prefixNumerical_sourcePrefix rate rewards C_star C_h control0 q.castSucc q.val le_rfl,
      ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl,
      ← prefixNumerical_sourcePrefix rate rewards C_star C_h control0 q.castSucc q.val le_rfl]
  change (_ ∈ physicalNextEvent rate rewards C_star C_h t q ∧ _ = true) ↔
    (_ ∈ physicalNextEvent rate rewards C_star C_h t q ∧ _ = true)
  rw [hf, restoreControl_source rate rewards C_star C_h control0 b u t q htq i r c,
    physicalNextEvent_replace_current rate rewards C_star C_h control0 t q]


/-- Event-restricted assignment erasure, with the original first-vector
weight retained inside the unconditional whole-control disintegration. -/
theorem clear_uniform_lintegral (htq : t.val < q.val)
    (F : Source p → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w in clearNextEvent rate rewards C_star C_h control0 b u t q,
      ∫⁻ v, F (ReferenceFirstCollectionRenewalVectorInsertion.insert q (O q.castSucc w).1.1.1.2 v)
        ∂ContinuousControlSlice.assignmentLaw p.K ∂Lambda) =
    ∫⁻ w in clearNextEvent rate rewards C_star C_h control0 b u t q,
      F (O q.castSucc w).1.1.1.2 ∂Lambda := by
  let Ec := clearNextEvent rate rewards C_star C_h control0 b u t q
  let S := fun w : Lift => (O q.castSucc w).1.1.1.2
  let av := ContinuousControlSlice.assignmentLaw p.K
  let tc := ContinuousLearningRows.timeControlLaw p
  have hEc := measurableSet_clearNextEvent rate rewards C_star C_h control0 b u t q
  have hS : Measurable S :=
    (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).fst.fst.fst.snd
  have hFi : Measurable (fun wv : Lift × Vector p =>
      F (ReferenceFirstCollectionRenewalVectorInsertion.insert q (S wv.1) wv.2)) :=
    hF.comp (measurable_nextInsertedReadout rate rewards C_star C_h control0 b u t q).snd.snd
  let f : Lift → ℝ≥0∞ := Ec.indicator (fun w => ∫⁻ v,
    F (ReferenceFirstCollectionRenewalVectorInsertion.insert q (S w) v) ∂av)
  let g : Lift → ℝ≥0∞ := Ec.indicator (fun w => F (S w))
  have hf : Measurable f := hFi.lintegral_prod_right'.indicator hEc
  have hg : Measurable g := (hF.comp hS).indicator hEc
  rw [← lintegral_indicator hEc, ← lintegral_indicator hEc]
  change (∫⁻ w, f w ∂Lambda) = ∫⁻ w, g w ∂Lambda
  rw [branchLaw_eq_sum_restore_control rate rewards C_star C_h control0 b u t q htq,
    lintegral_sum_measure, lintegral_sum_measure]
  apply tsum_congr
  intro i
  let restore := restoreControl rate rewards C_star C_h control0 b u t q htq i
  have hr := measurable_restoreControl rate rewards C_star C_h control0 b u t q htq i
  rw [lintegral_map hf hr, lintegral_map hg hr]
  change (∫⁻ a, (f ∘ restore) a ∂(remainderLaw rate rewards C_star C_h control0 b u t q htq i).prod tc) =
    ∫⁻ a, (g ∘ restore) a ∂(remainderLaw rate rewards C_star C_h control0 b u t q htq i).prod tc
  rw [lintegral_prod (f ∘ restore) (hf.comp hr).aemeasurable,
    lintegral_prod (g ∘ restore) (hg.comp hr).aemeasurable]
  apply lintegral_congr
  intro r
  let z := S (restore (r, control0))
  have hgate (c : ContinuousLearningRows.TimeControl p) : restore (r, c) ∈ Ec ↔
      restore (r, control0) ∈ Ec :=
    clearNextEvent_restoreControl rate rewards C_star C_h control0 b u t q htq i r c
  have hsrc (c : ContinuousLearningRows.TimeControl p) : S (restore (r, c)) =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z c :=
    restoreControl_source rate rewards C_star C_h control0 b u t q htq i r c
  simp only [Function.comp_apply, f, g, Set.indicator, hgate]
  by_cases he : restore (r, control0) ∈ Ec
  · simp only [he, ite_true]
    simp_rw [hsrc]
    let e := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
    let replace := fun cv : ContinuousLearningRows.TimeControl p × Vector p => e.symm (cv.2, (e cv.1).2)
    have hp : Measurable replace := e.symm.measurable.comp
      (measurable_snd.prodMk (e.measurable.snd.comp measurable_fst))
    let R := fun c : ContinuousLearningRows.TimeControl p =>
      F (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z c)
    have hR : Measurable R := by
      convert hF.comp (hS.comp (hr.comp ((measurable_const (a := r)).prodMk measurable_id))) using 1
      funext c
      exact congrArg F (hsrc c).symm
    have hRP : Measurable (fun cv : ContinuousLearningRows.TimeControl p × Vector p => R (replace cv)) :=
      hR.comp hp
    calc
      _ = ∫⁻ c, ∫⁻ v, R (replace (c, v)) ∂av ∂tc := by
        simp_rw [insert_replace_current (q := q)]
        rfl
      _ = ∫⁻ cv, R (replace cv) ∂tc.prod av := (lintegral_prod _ hRP.aemeasurable).symm
      _ = ∫⁻ c, R c ∂(tc.prod av).map replace := (lintegral_map hR hp).symm
      _ = _ := by rw [controlVectorReplacement_map]
  · simp only [he, ite_false, lintegral_zero]


/-- The entire newly inserted physical source, as a literal readout. -/
def insertedSourceReadout (wv : Lift × Vector p) : Source p :=
  (nextInsertedReadout rate rewards C_star C_h control0 b u t q wv).2.2

theorem measurable_insertedSourceReadout :
    Measurable (insertedSourceReadout rate rewards C_star C_h control0 b u t q) :=
  (measurable_nextInsertedReadout rate rewards C_star C_h control0 b u t q).snd.snd

/-- The complete physical-source projection on actual PRE-clear next calls. -/
theorem clear_inserted_source_marginal (htq : t.val < q.val) :
    (((Lambda).restrict (clearNextEvent rate rewards C_star C_h control0 b u t q)).compProd
      (actualNextVectorKernel rate rewards C_star C_h control0 b u t q)).map
        (insertedSourceReadout rate rewards C_star C_h control0 b u t q) =
      ((Lambda).restrict (clearNextEvent rate rewards C_star C_h control0 b u t q)).map
        (fun w : Lift => (O q.castSucc w).1.1.1.2) := by
  let mu := (Lambda).restrict (clearNextEvent rate rewards C_star C_h control0 b u t q)
  let S := fun w : Lift => (O q.castSucc w).1.1.1.2
  have hS : Measurable S :=
    (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).fst.fst.fst.snd
  refine Measure.ext_of_lintegral _ (fun F hF => ?_)
  have hi : Measurable (fun sv : Source p × Vector p =>
      F (ReferenceFirstCollectionRenewalVectorInsertion.insert q sv.1 sv.2)) :=
    hF.comp (ReferenceFirstCollectionRenewalVectorInsertion.measurable_insert (t := q))
  have hg : Measurable (fun z : Source p => ∫⁻ v,
      F (ReferenceFirstCollectionRenewalVectorInsertion.insert q z v)
        ∂ContinuousControlSlice.assignmentLaw p.K) := hi.lintegral_prod_right'
  rw [lintegral_map hF (measurable_insertedSourceReadout rate rewards C_star C_h control0 b u t q)]
  calc
    _ = ∫⁻ sv : Source p × Vector p, F (ReferenceFirstCollectionRenewalVectorInsertion.insert q sv.1 sv.2)
        ∂(mu.compProd (actualNextVectorKernel rate rewards C_star C_h control0 b u t q)).map
          (sourceVectorReadout rate rewards C_star C_h control0 b u t q) :=
      (lintegral_map hi (measurable_sourceVectorReadout rate rewards C_star C_h control0 b u t q)).symm
    _ = ∫⁻ sv : Source p × Vector p, F (ReferenceFirstCollectionRenewalVectorInsertion.insert q sv.1 sv.2)
        ∂(mu.map S).prod (ContinuousControlSlice.assignmentLaw p.K) := by
      rw [clear_source_vector_product rate rewards C_star C_h control0 b u t q htq]
    _ = ∫⁻ z, ∫⁻ v, F (ReferenceFirstCollectionRenewalVectorInsertion.insert q z v)
        ∂ContinuousControlSlice.assignmentLaw p.K ∂mu.map S := lintegral_prod _ hi.aemeasurable
    _ = ∫⁻ w, ∫⁻ v, F (ReferenceFirstCollectionRenewalVectorInsertion.insert q (S w) v)
        ∂ContinuousControlSlice.assignmentLaw p.K ∂mu := lintegral_map hg hS
    _ = ∫⁻ w, F (S w) ∂mu := clear_uniform_lintegral rate rewards C_star C_h control0 b u t q htq F hF
    _ = _ := (lintegral_map hF hS).symm

/-- This includes both a stopped PRE state and an absent PRE state. -/
def stoppedNextEvent : Set Lift := E ∩ {w | preClearFlag rate (t := t) q (O q.castSucc w) = false}

theorem measurableSet_stoppedNextEvent :
    MeasurableSet (stoppedNextEvent rate rewards C_star C_h control0 b u t q) :=
  (measurableSet_firstNextEvent rate rewards C_star C_h control0 b u t q).inter
    (measurableSet_eq_fun ((measurable_preClearFlag rate (t := t) q).comp
      (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc)) measurable_const)

/-- Stopping analytical insertion leaves the complete native physical source
unchanged and therefore keeps its prescribed physical continuation. -/
theorem stopped_inserted_source_marginal :
    (((Lambda).restrict (stoppedNextEvent rate rewards C_star C_h control0 b u t q)).compProd
      (actualNextVectorKernel rate rewards C_star C_h control0 b u t q)).map
        (insertedSourceReadout rate rewards C_star C_h control0 b u t q) =
      ((Lambda).restrict (stoppedNextEvent rate rewards C_star C_h control0 b u t q)).map
        (fun w : Lift => (O q.castSucc w).1.1.1.2) := by
  have hS := (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).fst.fst.fst.snd
  have hI := measurable_insertedSourceReadout rate rewards C_star C_h control0 b u t q
  refine Measure.ext_of_lintegral _ (fun F hF => ?_)
  rw [lintegral_map hF hI, lintegral_map hF hS]
  change (∫⁻ a, (F ∘ insertedSourceReadout rate rewards C_star C_h control0 b u t q) a
    ∂((Lambda).restrict (stoppedNextEvent rate rewards C_star C_h control0 b u t q)).compProd
      (actualNextVectorKernel rate rewards C_star C_h control0 b u t q)) = _
  rw [Measure.lintegral_compProd (hF.comp hI)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := Lambda)
    (measurableSet_stoppedNextEvent rate rewards C_star C_h control0 b u t q)] with w hw
  change (∫⁻ v, F (ReferenceFirstCollectionRenewalVectorInsertion.insert q (O q.castSucc w).1.1.1.2 v)
    ∂nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0
      (actualNextInput rate rewards C_star C_h control0 b u t q w)) = _
  rw [nextVectorKernel_of_preStopped rate rewards C_star C_h (t := t) (q := q) control0
    (actualNextInput rate rewards C_star C_h control0 b u t q w) hw.2, lintegral_dirac]
  exact congrArg F (ReferenceFirstCollectionRenewalVectorInsertion.insert_original_vector q _)

private theorem firstNext_restrict_clear_stopped :
    (Lambda).restrict E =
      (Lambda).restrict (clearNextEvent rate rewards C_star C_h control0 b u t q) +
        (Lambda).restrict (stoppedNextEvent rate rewards C_star C_h control0 b u t q) := by
  have hs : E = clearNextEvent rate rewards C_star C_h control0 b u t q ∪
      stoppedNextEvent rate rewards C_star C_h control0 b u t q := by
    ext w
    change (w ∈ E) ↔
      (w ∈ E ∧ preClearFlag rate (t := t) q (O q.castSucc w) = true) ∨
        (w ∈ E ∧ preClearFlag rate (t := t) q (O q.castSucc w) = false)
    cases preClearFlag rate (t := t) q (O q.castSucc w) <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false, and_false, and_true, false_or, or_false]
  rw [hs]
  apply Measure.restrict_union _ (measurableSet_stoppedNextEvent rate rewards C_star C_h control0 b u t q)
  apply Set.disjoint_left.mpr
  intro w hc hs
  exact Bool.false_ne_true (hs.2.symm.trans hc.2)

/-- Full new physical-source equality on the SAME original first-invocation
extension, for every Borel whole-source test, without normalization. -/
theorem nextInsertedLaw_map_newSource (htq : t.val < q.val) :
    (nextInsertedLaw rate rewards C_star C_h control0 b u t q).map (fun x => x.2.2) =
      ((Lambda).restrict E).map (fun w : Lift => (O q.castSucc w).1.1.1.2) := by
  rw [nextInsertedLaw, Measure.map_map measurable_snd.snd
    (measurable_nextInsertedReadout rate rewards C_star C_h control0 b u t q)]
  change (nextLiftLaw rate rewards C_star C_h control0 b u t q).map
    (insertedSourceReadout rate rewards C_star C_h control0 b u t q) = _
  rw [nextLiftLaw, firstNext_restrict_clear_stopped, Measure.compProd_add_left,
    Measure.map_add _ _ (measurable_insertedSourceReadout rate rewards C_star C_h control0 b u t q),
    clear_inserted_source_marginal rate rewards C_star C_h control0 b u t q htq,
    stopped_inserted_source_marginal rate rewards C_star C_h control0 b u t q,
    Measure.map_add _ _
      (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).fst.fst.fst.snd]

/-- Identification with the original full source law and its literal native
no-call-between/next-q-call event, retaining original first-branch weights. -/
theorem nextInsertedLaw_map_sourceInputLaw (htq : t.val < q.val) :
    (nextInsertedLaw rate rewards C_star C_h control0 b u t q).map (fun x => x.2.2) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (branchEvent rate rewards C_star C_h b u t ∩ physicalNextEvent rate rewards C_star C_h t q) := by
  rw [nextInsertedLaw_map_newSource rate rewards C_star C_h control0 b u t q htq,
    firstNext_source_marginal]


/-- Same-sample identity on PRE-stopped and missing-PRE inputs. This is only
an exceptional-branch identity, not a general diagonal source coupling. -/
theorem ae_nextInsertedLaw_stopped_identity :
    ∀ᵐ x ∂nextInsertedLaw rate rewards C_star C_h control0 b u t q,
      preClearFlag rate (t := t) q (O q.castSucc x.1) = false →
        x.2.2 = (O q.castSucc x.1).1.1.1.2 := by
  have hN := measurable_nextInsertedReadout rate rewards C_star C_h control0 b u t q
  have hS := (measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).fst.fst.fst.snd
  have hpre : Measurable (fun x : Lift × (Vector p × Source p) =>
      preClearFlag rate (t := t) q (O q.castSucc x.1)) :=
    (measurable_preClearFlag rate (t := t) q).comp
      ((measurable_branchObservation rate rewards C_star C_h control0 b u t q.castSucc).comp measurable_fst)
  have hg : MeasurableSet {x : Lift × (Vector p × Source p) |
      preClearFlag rate (t := t) q (O q.castSucc x.1) = false →
        x.2.2 = (O q.castSucc x.1).1.1.1.2} := by
    convert (measurableSet_eq_fun hpre (measurable_const (a := false))).compl.union
      (measurableSet_eq_fun measurable_snd.snd (hS.comp measurable_fst)) using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
    exact imp_iff_not_or
  apply (ae_map_iff hN.aemeasurable hg).mpr
  apply Measure.ae_compProd_of_ae_ae (hg.preimage hN)
  apply Filter.Eventually.of_forall
  intro w
  by_cases hw : preClearFlag rate (t := t) q (O q.castSucc w) = false
  · change ∀ᵐ v ∂nextVectorKernel rate rewards C_star C_h (t := t) (q := q) control0
        (actualNextInput rate rewards C_star C_h control0 b u t q w), _
    rw [nextVectorKernel_of_preStopped rate rewards C_star C_h (t := t) (q := q) control0
      (actualNextInput rate rewards C_star C_h control0 b u t q w) hw]
    filter_upwards [ae_eq_dirac (id : Vector p → Vector p)] with v hv _
    change v = currentVector rate (t := t) q
      (actualNextInput rate rewards C_star C_h control0 b u t q w) at hv
    change ReferenceFirstCollectionRenewalVectorInsertion.insert q (O q.castSucc w).1.1.1.2 v = _
    rw [hv]
    exact ReferenceFirstCollectionRenewalVectorInsertion.insert_original_vector q _
  · exact Filter.Eventually.of_forall fun _ h => (hw h).elim

/-- The constant-one integral is the original, unnormalized next-call mass. -/
theorem nextInsertedLaw_const_one :
    (∫⁻ _x, (1 : ℝ≥0∞) ∂nextInsertedLaw rate rewards C_star C_h control0 b u t q) = Lambda E := by
  rw [lintegral_const, one_mul, nextInsertedLaw_mass]

/-- Every nonnegative Borel test may inspect the entire source, with all
rows, private arrays and J retained on the right-hand side. -/
theorem nextInsertedLaw_source_test (htq : t.val < q.val)
    (F : Source p → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x.2.2 ∂nextInsertedLaw rate rewards C_star C_h control0 b u t q) =
      ∫⁻ z, F z ∂(BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (branchEvent rate rewards C_star C_h b u t ∩ physicalNextEvent rate rewards C_star C_h t q) := by
  rw [← lintegral_map hF measurable_snd.snd,
    nextInsertedLaw_map_sourceInputLaw rate rewards C_star C_h control0 b u t q htq]


/-- Identity array, every private array including J, and the original row
selector are retained pointwise on the same extension sample. -/
theorem ae_nextInsertedLaw_source_coordinates :
    ∀ᵐ x ∂nextInsertedLaw rate rewards C_star C_h control0 b u t q,
      x.2.2.1.1 = (O q.castSucc x.1).1.1.1.2.1.1 ∧
      x.2.2.2 = (O q.castSucc x.1).1.1.1.2.2 ∧
      ReferenceFirstCollectionRenewalVectorInsertion.q x.2.2 =
        ReferenceFirstCollectionRenewalVectorInsertion.q (O q.castSucc x.1).1.1.1.2 := by
  filter_upwards [ae_nextInsertedLaw_readout rate rewards C_star C_h control0 b u t q] with x hx
  rw [hx]
  exact ReferenceFirstCollectionRenewalVectorInsertion.insert_identity_private_selector q _ _

/-- Actual source-prefix locality for all native PRE-call readouts. -/
theorem ae_nextInsertedLaw_sourcePrefix :
    ∀ᵐ x ∂nextInsertedLaw rate rewards C_star C_h control0 b u t q,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val x.2.2 =
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val (O q.castSucc x.1).1.1.1.2 := by
  filter_upwards [ae_nextInsertedLaw_readout rate rewards C_star C_h control0 b u t q] with x hx
  rw [hx, ReferenceFirstCollectionRenewalVectorInsertion.insert,
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl]

end Bandits.Support.ReferenceNextInsertedSourceMarginal
