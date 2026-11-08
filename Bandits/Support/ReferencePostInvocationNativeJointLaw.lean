/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostInvocationSupportedDisintegration
public import Bandits.Support.ReferencePostInvocationLiveNativeLaw
public import Bandits.Support.ReferencePostInvocationCollectionNativeLaw
public import Bandits.Support.ReferencePostInvocationPrefixLocality
public import Bandits.Support.ReferencePostInvocationGeneratedAlignment
public import Bandits.Support.ReferenceFirstNextLiftFutureControl
public import Bandits.Support.ReferenceFirstNextLiftFutureAuxiliaryPairLaw

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Native finite-fibre assembly on both literal post-invocation lifts

The branch parameter is false for the nonrenewed law and true for the renewed
law. Native masses are prescribed by the accepted correlated LIVE law and the
OLD-payload COLLECTION formulas. Their equality with the actual supported
innovation fibres is proved below. Full-source tests retain the tested control
and both distinct auxiliary labels inside the original literal restoration.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and `08_main_theorem.tex:78-109`.
This module makes no killed-iteration or manuscript-closure claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFixedTimeSourceControlCoupling

namespace Bandits.Support.ReferencePostInvocationNativeJointLaw

open ReferencePostInvocationSupportedDisintegration
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferenceFirstNextLiftFutureAuxiliaryPairLaw

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance controlMeasurableSpace : MeasurableSpace (Control p) := by
  unfold Control ContinuousLearningRows.TimeControl
  infer_instance

local instance auxiliaryMeasurableSpace : MeasurableSpace (ReferencePostInvocationSupportedDisintegration.Auxiliary p) := by
  unfold ReferencePostInvocationSupportedDisintegration.Auxiliary ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray
  infer_instance

local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : Control p) (b : Bool) (u t q : Fin p.T) (htq : t.val < q.val)
  (i : Fin (M p))

local notation "Observer" => SupportedObserver rate rewards C_star C_h control0 b u t q htq i
local notation "Survivor" => SurvivingObserver rate rewards C_star C_h control0 b u t q htq i
local notation "restore" => restoreSupported rate rewards C_star C_h control0 b u t q htq i
local notation "transition" => branchTransition rate rewards C_star C_h control0 b u t
local notation "outcome" => outcomeOnSupported rate rewards C_star C_h control0 b u t q htq i
local notation "readPrefix" => erasedPrefixReadout rate t q i pairLabels
local notation "liveDomain" => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
  rate rewards C_star C_h q
local notation "collectionDomain" => collectionDateDomain rate rewards C_star C_h q
local notation "μ" => innovationLaw (p := p)

/-- A reference point only for describing the same restored source family.
The resulting finite masses are proved to be its actual innovation masses. -/
def referenceInnovation : Innovation p :=
  (control0, (ReferenceFirstLiveActualRefreshTestLaw.scalarZero,
    ReferenceFirstLiveActualRefreshTestLaw.scalarZero))

/-- The actual inserted full source at the reference innovation. -/
def referenceSource (d : Observer) : BootstrapPrivateRoundStreams.SourceInput p :=
  insertedPhysicalSource rate (transition (restore (d, referenceInnovation control0)))

/-- All other auxiliary coordinates remain the original coordinates. -/
theorem restoreSupported_auxiliary (d : Observer) (ω ω' : Innovation p) :
    (restore (d, ω)).1.2 = fillAuxiliaryPair q (restore (d, ω')).1.2 ω.2 := by
  let a := (ReferencePostInvocationPrefixLocality.auxiliarySplit q pairLabels).symm
    (testedPair q ω'.2, d.val.val.1.1.2)
  change (auxiliarySplit q pairLabels).symm
      (testedPair q ω.2, d.val.val.1.1.2) =
    fillAuxiliaryPair q a ω.2
  have ha : ((auxiliarySplit q pairLabels) a).2 = d.val.val.1.1.2 := by
    rw [MeasurableEquiv.apply_symm_apply]
  rw [← ha]
  exact auxiliarySplit_fillPair q a ω.2

/-- The restored current source is the producer's whole-control family,
simultaneously for both original branches and all auxiliary innovations. -/
theorem restored_source (d : Observer) (ω : Innovation p) :
    insertedPhysicalSource rate (transition (restore (d, ω))) =
      replaceSourceControl p q
        (referenceSource rate rewards C_star C_h control0 b u t q htq i d) ω.1 :=
  restoreSupported_inserted_source rate rewards C_star C_h control0 b u t q htq i
    d ω (referenceInnovation control0)

/-- The continuing-LIVE case is constant across the same supported family. -/
theorem restored_live_iff (d : Observer) (ω : Innovation p) :
    insertedPhysicalSource rate (transition (restore (d, ω))) ∈ liveDomain ↔
      referenceSource rate rewards C_star C_h control0 b u t q htq i d ∈ liveDomain := by
  rw [restored_source]
  exact ReferencePostInvocationLiveNativeLaw.continuingDomain_replace rate rewards C_star C_h control0 q _ ω.1

/-- Collection membership is constant across the same supported family. -/
theorem restored_collection_iff (d : Observer) (ω : Innovation p) :
    insertedPhysicalSource rate (transition (restore (d, ω))) ∈ collectionDomain ↔
      referenceSource rate rewards C_star C_h control0 b u t q htq i d ∈ collectionDomain := by
  constructor
  · intro hc
    have h := ReferencePostInvocationCollectionNativeLaw.collectionDateDomain_replace_control rate rewards C_star C_h control0 q
      ⟨_, hc⟩ (referenceInnovation control0).1
    rw [← restoreSupported_inserted_source rate rewards C_star C_h control0 b u t q htq i
      d (referenceInnovation control0) ω] at h
    exact h
  · intro hc
    rw [restored_source]
    exact ReferencePostInvocationCollectionNativeLaw.collectionDateDomain_replace_control rate rewards C_star C_h control0 q
      ⟨_, hc⟩ ω.1

/-- Exact all-control LIVE readout on the actual supported observer, before
any distributional statement or finite-fibre application. -/
theorem outcome_live (d : Observer) (s : SlowSet p × List (LogicalCell p rate))
    (hp : (readPrefix d.val.val).1 = some s)
    (hl : referenceSource rate rewards C_star C_h control0 b u t q htq i d ∈ liveDomain)
    (ω : Innovation p) :
    outcome (d, ω) = ReferencePostInvocationLiveNativeLaw.sourceOutcome rate rewards C_star C_h control0 q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d, hl⟩
      (restore (d, referenceInnovation control0)).1.2 ω := by
  rw [outcomeOnSupported_readout, hp, Option.bind_some]
  have hl' := (restored_live_iff rate rewards C_star C_h control0 b u t q htq i d ω).mpr hl
  rw [noncallDateCell, dite_eq_left hl']
  have hz : (⟨insertedPhysicalSource rate (transition (restore (d, ω))), hl'⟩ :
      ContinuingLiveSource rate rewards C_star C_h q) =
      ReferencePostInvocationLiveNativeLaw.sourceAt rate rewards C_star C_h control0 q
        ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d, hl⟩ ω.1 := by
    apply Subtype.ext
    exact restored_source rate rewards C_star C_h control0 b u t q htq i d ω
  rw [hz, restoreSupported_auxiliary rate rewards C_star C_h control0 b u t q htq i
    d ω (referenceInnovation control0)]
  rfl

/-- Exact all-control COLLECTION readout. The incoming logical set is read
from the complete actual prefix, independently of the OLD physical payload. -/
theorem outcome_collection (d : Observer) (s : SlowSet p × List (LogicalCell p rate))
    (hp : (readPrefix d.val.val).1 = some s)
    (hl : referenceSource rate rewards C_star C_h control0 b u t q htq i d ∉ liveDomain)
    (hc : referenceSource rate rewards C_star C_h control0 b u t q htq i d ∈ collectionDomain)
    (ω : Innovation p) :
    outcome (d, ω) = ReferencePostInvocationCollectionNativeLaw.sourceOutcome rate rewards C_star C_h control0 q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d, hc⟩ s.1
      (restore (d, referenceInnovation control0)).1.2 ω := by
  rw [outcomeOnSupported_readout, hp, Option.bind_some]
  have hl' := mt (restored_live_iff rate rewards C_star C_h control0 b u t q htq i d ω).mp hl
  have hc' := (restored_collection_iff rate rewards C_star C_h control0 b u t q htq i d ω).mpr hc
  rw [noncallDateCell, dite_eq_right hl', dite_eq_left hc']
  have hz : (⟨insertedPhysicalSource rate (transition (restore (d, ω))), hc'⟩ :
      CollectionDateSource rate rewards C_star C_h q) =
      ReferencePostInvocationCollectionNativeLaw.replaceCollectionSource rate rewards C_star C_h control0 q
        ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d, hc⟩ ω.1 := by
    apply Subtype.ext
    exact restored_source rate rewards C_star C_h control0 b u t q htq i d ω
  rw [hz, restoreSupported_auxiliary rate rewards C_star C_h control0 b u t q htq i
    d ω (referenceInnovation control0)]
  unfold ReferencePostInvocationCollectionNativeLaw.sourceOutcome
  cases laterCollectionCell? rate rewards C_star C_h q
    (ReferencePostInvocationCollectionNativeLaw.replaceCollectionSource rate rewards C_star C_h control0 q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d, hc⟩ ω.1) s.1
      (fillAuxiliaryPair q (restore (d, referenceInnovation control0)).1.2 ω.2) <;> rfl

/-- The literal constructor supplies absence when its old prefix is absent. -/
theorem outcome_absent_prefix (d : Observer)
    (hp : (readPrefix d.val.val).1 = none) (ω : Innovation p) :
    outcome (d, ω) = Sum.inl () := by
  rw [outcomeOnSupported_readout, hp, Option.bind_none]
  rfl

/-- Absence outside both actual phase domains follows from the literal
constructor on every control; it is not inferred from a zero observer mass. -/
theorem outcome_absent_phase (d : Observer) (s : SlowSet p × List (LogicalCell p rate))
    (hp : (readPrefix d.val.val).1 = some s)
    (hl : referenceSource rate rewards C_star C_h control0 b u t q htq i d ∉ liveDomain)
    (hc : referenceSource rate rewards C_star C_h control0 b u t q htq i d ∉ collectionDomain)
    (ω : Innovation p) :
    outcome (d, ω) = Sum.inl () := by
  rw [outcomeOnSupported_readout, hp, Option.bind_some]
  have hl' := mt (restored_live_iff rate rewards C_star C_h control0 b u t q htq i d ω).mp hl
  have hc' := mt (restored_collection_iff rate rewards C_star C_h control0 b u t q htq i d ω).mp hc
  rw [noncallDateCell, dite_eq_right hl', dite_eq_right hc']
  rfl

/-- Prescribed native finite coefficients. The LIVE measure is built from
its correlated recorder/FAST law, physical Bernoulli bit and residual law;
COLLECTION uses the accepted explicit OLD-rate/FAST/residual coefficients.
The Unit cases are precisely literal absence. No innovation fibre appears
in this definition. -/
def nativeMass (d : Observer) (o : Outcome p) : ℝ≥0∞ :=
  match (readPrefix d.val.val).1 with
  | none => (Measure.dirac (Sum.inl () : Outcome p)) {o}
  | some s =>
    if hl : referenceSource rate rewards C_star C_h control0 b u t q htq i d ∈ liveDomain then
      ReferencePostInvocationLiveNativeLaw.nativeLaw rate rewards C_star C_h q
        ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d, hl⟩ {o}
    else if hc : referenceSource rate rewards C_star C_h control0 b u t q htq i d ∈ collectionDomain then
      ReferencePostInvocationCollectionNativeLaw.nativeMass rate rewards C_star C_h q
        ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d, hc⟩ s.1 o
    else (Measure.dirac (Sum.inl () : Outcome p)) {o}

/-- Borel measurability of the actual finite sampler at each supported observer. -/
theorem measurable_outcome_fibre (d : Observer) :
    Measurable (fun ω : Innovation p => outcome (d, ω)) :=
  (measurable_outcomeOnSupported rate rewards C_star C_h control0 b u t q htq i).comp
    (measurable_const.prodMk measurable_id)

/-- Native coefficients equal the ACTUAL supported innovation-fibre masses,
on both literal laws and every private stratum, including null strata. -/
theorem nativeMass_eq_fibreMass (d : Observer) (o : Outcome p) :
    nativeMass rate rewards C_star C_h control0 b u t q htq i d o =
      FiniteFibreLift.fibreMass μ (fun ω => outcome (d, ω)) o := by
  have hmap : FiniteFibreLift.fibreMass μ (fun ω => outcome (d, ω)) o =
      (μ).map (fun ω => outcome (d, ω)) {o} :=
    (Measure.map_apply (measurable_outcome_fibre rate rewards C_star C_h control0 b u t q htq i d)
      (measurableSet_singleton o)).symm
  rw [hmap]
  cases hp : (readPrefix d.val.val).1 with
  | none =>
    have he : (fun ω : Innovation p => outcome (d, ω)) = fun _ => Sum.inl () := by
      funext ω
      exact outcome_absent_prefix rate rewards C_star C_h control0 b u t q htq i d hp ω
    simp only [nativeMass, hp]
    rw [he]
    change (Measure.dirac (Sum.inl () : Outcome p)) {o} =
      ((μ).map (fun _ : Innovation p => (Sum.inl () : Outcome p))) {o}
    rw [Measure.map_const, measure_univ, one_smul]
  | some s =>
    simp only [nativeMass, hp]
    by_cases hl : referenceSource rate rewards C_star C_h control0 b u t q htq i d ∈ liveDomain
    · rw [dite_eq_left hl]
      have he := funext (outcome_live rate rewards C_star C_h control0 b u t q htq i d s hp hl)
      rw [he]
      exact congrArg (fun ν : Measure (Outcome p) => ν {o})
        (ReferencePostInvocationLiveNativeLaw.sourceOutcome_law
          rate rewards C_star C_h control0 q _ _).2.symm
    · rw [dite_eq_right hl]
      by_cases hc : referenceSource rate rewards C_star C_h control0 b u t q htq i d ∈ collectionDomain
      · rw [dite_eq_left hc]
        have he := funext (outcome_collection rate rewards C_star C_h control0 b u t q htq i d s hp hl hc)
        rw [he]
        exact (ReferencePostInvocationCollectionNativeLaw.sourceOutcome_mass
          rate rewards C_star C_h control0 q _ _ _ o).symm
      · rw [dite_eq_right hc]
        have he : (fun ω : Innovation p => outcome (d, ω)) = fun _ => Sum.inl () := by
          funext ω
          exact outcome_absent_phase rate rewards C_star C_h control0 b u t q htq i d s hp hl hc ω
        rw [he]
        change (Measure.dirac (Sum.inl () : Outcome p)) {o} =
          ((μ).map (fun _ : Innovation p => (Sum.inl () : Outcome p))) {o}
        rw [Measure.map_const, measure_univ, one_smul]

/-- The native masses sum to one, including zero outcome and index strata. -/
theorem sum_nativeMass (d : Observer) :
    (∑ o, nativeMass rate rewards C_star C_h control0 b u t q htq i d o) = 1 := by
  simp_rw [nativeMass_eq_fibreMass]
  exact FiniteFibreLift.sum_fibreMass μ _
    (measurable_outcome_fibre rate rewards C_star C_h control0 b u t q htq i d)

/-- The actual finite-fibre mixture reconstructs the whole innovation block,
not just its finite coordinates or their separate marginals. -/
theorem native_fibre_reconstruction (d : Observer) :
    (∑ o, nativeMass rate rewards C_star C_h control0 b u t q htq i d o •
      FiniteFibreLift.fibreMeasure μ (fun ω => outcome (d, ω)) o) = μ := by
  simp_rw [nativeMass_eq_fibreMass]
  exact FiniteFibreLift.sum_fibreMass_smul_fibreMeasure μ _
    (measurable_outcome_fibre rate rewards C_star C_h control0 b u t q htq i d)

/-- Null native atoms use the accepted original-innovation convention. -/
theorem native_fibre_zero (d : Observer) (o : Outcome p)
    (ho : nativeMass rate rewards C_star C_h control0 b u t q htq i d o = 0) :
    FiniteFibreLift.fibreMeasure μ (fun ω => outcome (d, ω)) o = μ := by
  apply FiniteFibreLift.fibreMeasure_of_eq_zero
  exact (nativeMass_eq_fibreMass rate rewards C_star C_h control0 b u t q htq i d o).symm.trans ho

/-- A positive native atom is recovered almost surely by the very same
restored source and auxiliary pair used in the joint observation. -/
theorem native_fibre_outcome (d : Observer) (o : Outcome p)
    (ho : nativeMass rate rewards C_star C_h control0 b u t q htq i d o ≠ 0) :
    ∀ᵐ ω ∂FiniteFibreLift.fibreMeasure μ (fun ω => outcome (d, ω)) o,
      outcome (d, ω) = o := by
  apply FiniteFibreLift.ae_fibreMeasure_eq
    _ _ _ (measurable_outcome_fibre rate rewards C_star C_h control0 b u t q htq i d)
  rw [← nativeMass_eq_fibreMass]
  exact ho

/-- Full-source bounded tests admit the actual finite-fibre expansion at each
supported observer. The tested innovation remains inside literal restoration. -/
theorem native_fibre_integral (d : Observer)
    (Phi : PrefixObservation rate t q.succ → ℝ)
    (hPhi : Measurable Phi) (B : ℝ) (hB : ∀ o, ‖Phi o‖ ≤ B) :
    (∫ ω, Phi (branchObservation rate rewards C_star C_h control0 b u t q.succ
      (restore (d, ω))) ∂μ) =
    ∑ o, (nativeMass rate rewards C_star C_h control0 b u t q htq i d o).toReal *
      ∫ ω, Phi (branchObservation rate rewards C_star C_h control0 b u t q.succ
        (restore (d, ω)))
        ∂FiniteFibreLift.fibreMeasure μ (fun ω => outcome (d, ω)) o := by
  let f := fun ω : Innovation p => Phi
    (branchObservation rate rewards C_star C_h control0 b u t q.succ (restore (d, ω)))
  have hf : Measurable f := hPhi.comp
    ((measurable_branchObservation rate rewards C_star C_h control0 b u t q.succ).comp
      ((measurable_restoreSupported rate rewards C_star C_h control0 b u t q htq i).comp
        (measurable_const.prodMk measurable_id)))
  have hsum := native_fibre_reconstruction rate rewards C_star C_h control0 b u t q htq i d
  change (∫ ω, f ω ∂μ) = _
  conv_lhs => rw [← hsum]
  rw [integral_finsetSum_measure (fun o _ => ?_)]
  · simp only [integral_smul_measure, smul_eq_mul, f]
  · rw [nativeMass_eq_fibreMass, FiniteFibreLift.fibreMass_smul_fibreMeasure]
    exact Integrable.of_bound hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun ω => hB _))

/-- BOTH literal unnormalized surviving full-source laws, with the prescribed
native finite masses and the actual innovation fibre lifts. There is no event
normalization, index-mass division, history premise or native-law premise. -/
theorem surviving_native_joint_integral
    (Phi : PrefixObservation rate t q.succ → ℝ)
    (hPhi : Measurable Phi) (B : ℝ) (hB : ∀ o, ‖Phi o‖ ≤ B) :
    (∫ w, Phi (branchObservation rate rewards C_star C_h control0 b u t q.succ w)
      ∂(branchLaw rate rewards C_star C_h control0 b u t).restrict
        (survivingDomain rate rewards C_star C_h control0 b u t q)) =
    ∑ i : Fin (M p),
      ∫ d in observerGate rate rewards C_star C_h control0 b u t q htq i,
        ∑ o, (nativeMass rate rewards C_star C_h control0 b u t q htq i d o).toReal *
          ∫ ω, Phi (branchObservation rate rewards C_star C_h control0 b u t q.succ
            (restoreSupported rate rewards C_star C_h control0 b u t q htq i (d, ω)))
            ∂FiniteFibreLift.fibreMeasure μ
              (fun ω => outcomeOnSupported rate rewards C_star C_h control0 b u t q htq i (d, ω)) o
        ∂supportedObserverLaw rate rewards C_star C_h control0 b u t q htq i := by
  rw [surviving_joint_integral rate rewards C_star C_h control0 b u t q htq Phi hPhi B hB]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun d =>
    native_fibre_integral rate rewards C_star C_h control0 b u t q htq j d Phi hPhi B hB)

/-- Reference restoration retains the actual first invocation, on BOTH
branches, without a success, score-truth or PRE-clear hypothesis. -/
theorem referenceSource_firstCall (d : Observer) :
    referenceSource rate rewards C_star C_h control0 b u t q htq i d ∈
      ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
        rate rewards C_star C_h u t := by
  cases b
  · let w := restoreSupported rate rewards C_star C_h control0 false u t q htq i
      (d, referenceInnovation control0)
    exact ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_insertVector_mem
      rate rewards C_star C_h u t w.1.1.val w.1.1.property.1 w.2
  · let w := restoreSupported rate rewards C_star C_h control0 true u t q htq i
      (d, referenceInnovation control0)
    exact (ReferenceFirstCollectionRenewalInstallationCoupling.pair
      rate rewards C_star C_h u t w).2.property.1

/-- Every actual surviving observer has an actual LIVE or COLLECTION date.
Thus no extra absent phase can be justified by observer-mass vacuity. -/
theorem surviving_phase_coverage (d : Survivor) :
    referenceSource rate rewards C_star C_h control0 b u t q htq i d.val ∈ liveDomain ∨
      referenceSource rate rewards C_star C_h control0 b u t q htq i d.val ∈ collectionDomain := by
  have hdate := ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_dates
    rate rewards C_star C_h u t _
      (referenceSource_firstCall rate rewards C_star C_h control0 b u t q htq i d.val)
  have hsurv := (survivingDomain_restoreSupported rate rewards C_star C_h control0 b u t q htq i
    d.val (referenceInnovation control0)).mpr d.property
  exact noncall_phase_coverage rate rewards C_star C_h q _
    (hdate.1.trans_lt (hdate.2.1.trans htq)) hsurv.2

/-- The actual incoming supported prefix, read on the SAME restored source. -/
theorem incomingPrefix_readout (d : Survivor) (ω : Innovation p) :
    postInvocationPrefix rate rewards C_star C_h t q.castSucc
      (transition (restore (d.val, ω))) (restore (d.val, ω)).1.2 =
      some (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d) := by
  have hp := congrArg Prod.fst
    (supported_prefix_readout rate rewards C_star C_h control0 b u t q htq i d.val ω)
  exact hp.symm.trans (Option.some_get d.property.1).symm

/-- The clear LIVE atom keeps the correlated recorder/FAST mass. The
retention set is the actual evolving incoming seed, and the numerical
complement is produced from the actual PRE, not assumed. -/
theorem nativeMass_live_clear (d : Survivor)
    (hl : referenceSource rate rewards C_star C_h control0 b u t q htq i d.val ∈ liveDomain)
    (hpre : (continuingBefore rate rewards C_star C_h q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hl⟩).overflow = false) :
    let z : ContinuingLiveSource rate rewards C_star C_h q :=
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hl⟩
    let U := (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d).1
    (∀ j : CanonicalFastSampling.FastArm (continuingSourceCell rate rewards C_star C_h q z).selected.view.payload.slowSet,
      (continuingSourceCell rate rewards C_star C_h q z).selected.view.complementWeights j =
        RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (continuingBefore rate rewards C_star C_h q z) j.val) ∧
    ∀ (marker : Option (Fin p.K)) (fast : Fin p.K) (proposed : Bool) (V : SlowSet p),
      nativeMass rate rewards C_star C_h control0 b u t q htq i d.val
        (Sum.inr (marker, fast, proposed, V)) =
      ReferencePostInvocationLiveNativeLaw.nativePairLaw rate rewards C_star C_h q z {(marker, fast)} *
        (if proposed then ENNReal.ofReal (4 * (p.m : ℝ) * rate.eta.val) *
          ReferencePostInvocationLiveNativeLaw.residualLaw rate rewards C_star C_h q z marker {V}
        else ENNReal.ofReal (1 - 4 * (p.m : ℝ) * rate.eta.val) * if V = U then 1 else 0) := by
  dsimp only
  have ha := supported_live_alignment rate rewards C_star C_h control0 b u t q htq i
    d (referenceInnovation control0) hl hpre
  have hseed : (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d).1 =
      (continuingSourceCell rate rewards C_star C_h q
        ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hl⟩).selected.view.payload.slowSet := ha.1
  refine ⟨ha.2, ?_⟩
  intro marker fast proposed V
  have hp : (readPrefix d.val.val.val).1 =
      some (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d) :=
    (Option.some_get d.property.1).symm
  simp only [nativeMass, hp, dite_eq_left hl]
  have h := ReferencePostInvocationLiveNativeLaw.nativeLaw_atom_clear rate rewards C_star C_h q
    ⟨_, hl⟩ hpre marker fast proposed V
  rw [← hseed] at h
  exact h

/-- Generated COLLECTION atoms use the real OLD recording rates and the
prescribed qGamma on the separately evolving incoming logical set. Its
envelope, birth source and call-free prefix are derived from the actual lift. -/
theorem nativeMass_collection_clear (d : Survivor)
    (hl : referenceSource rate rewards C_star C_h control0 b u t q htq i d.val ∉ liveDomain)
    (hc : referenceSource rate rewards C_star C_h control0 b u t q htq i d.val ∈ collectionDomain)
    (hen : (collectionInput rate rewards C_star C_h q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hc⟩).enabled = true)
    (hpre : (collectionBefore rate rewards C_star C_h q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hc⟩).overflow = false) :
    let z : CollectionDateSource rate rewards C_star C_h q :=
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hc⟩
    let P := (collectionArguments rate rewards C_star C_h q z).1
    let weight := RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (collectionBefore rate rewards C_star C_h q z)
    let U := (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d).1
    (collectionInput rate rewards C_star C_h q z).rate = P.rate ∧
      P.rate = CanonicalRecordingRates.xi p rate.eta.val P.anchor ∧
    ∃ (hlo : ∀ j, P.anchor j ≤ weight j) (hhi : ∀ j, weight j ≤ 2 * P.anchor j),
      ∀ (marker : Option (Fin p.K)) (fast : CanonicalFastSampling.FastArm U)
        (proposed : Bool) (V : SlowSet p),
      nativeMass rate rewards C_star C_h control0 b u t q htq i d.val
        (Sum.inr (marker, fast.val, proposed, V)) =
        (ReferencePostInvocationCollectionNativeLaw.recorderPMF rate rewards C_star C_h q z marker *
          ENNReal.ofReal (CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property rate.sourceCap
            P.anchor weight P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos _ _)
            hlo hhi U fast)) *
          ReferencePostInvocationCollectionNativeLaw.auxiliaryMass rate rewards C_star C_h q z U marker proposed V := by
  dsimp only
  let w := restore (d.val, referenceInnovation control0)
  have hp := incomingPrefix_readout rate rewards C_star C_h control0 b u t q htq i
    d (referenceInnovation control0)
  have ha := branch_collection_alignment rate rewards C_star C_h control0 b u t q htq w
  dsimp only at ha
  rw [hp] at ha
  have halign := ha hc
  obtain ⟨birth, hbirth, _⟩ := halign.1
  have hbirth' : birth.val = referenceSource rate rewards C_star C_h control0 b u t q htq i d.val := hbirth
  have hcall := ReferencePostInvocationGeneratedAlignment.postInvocationPrefix_some_noCall
    rate rewards C_star C_h t q.castSucc (transition w) w.1.2 _ hp
  have hbc : birth.val ∈ collectionDomain := hbirth'.symm ▸ hc
  have hz : (⟨birth.val, hbc⟩ : CollectionDateSource rate rewards C_star C_h q) =
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hc⟩ :=
    Subtype.ext hbirth'
  have hben : (collectionInput rate rewards C_star C_h q ⟨birth.val, hbc⟩).enabled = true := by
    simpa only [hz] using hen
  have hbpre : (collectionBefore rate rewards C_star C_h q ⟨birth.val, hbc⟩).overflow = false := by
    simpa only [hz] using hpre
  have hbcall : NoCallBetween rate rewards C_star C_h t q.castSucc birth.val := hbirth'.symm ▸ hcall
  have hgenerated := ReferencePostInvocationCollectionNativeLaw.generated_collection_clear_atom
    rate rewards C_star C_h control0 q t birth htq hbcall hbc hben hbpre
  dsimp only at hgenerated
  simp only [hz] at hgenerated
  obtain ⟨hlo, hhi, hmass⟩ := hgenerated
  refine ⟨halign.2.2.1, halign.2.2.2.1, ?_⟩
  refine ⟨hlo, hhi, ?_⟩
  intro marker fast proposed V
  have h := hmass
    (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d).1
    w.1.2 marker fast proposed V
  rw [ReferencePostInvocationCollectionNativeLaw.sourceOutcome_mass
    rate rewards C_star C_h control0 q _ _ _ _] at h
  have hp' : (readPrefix d.val.val.val).1 =
      some (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d) :=
    (Option.some_get d.property.1).symm
  simpa only [nativeMass, hp', dite_eq_right hl, dite_eq_left hc] using h

/-- Native coefficients are Borel in the actual supported observer, as a
consequence of their proved fibre characterization and joint measurability. -/
theorem measurable_nativeMass (o : Outcome p) :
    Measurable (fun d : Observer => nativeMass rate rewards C_star C_h control0 b u t q htq i d o) := by
  have hm := measurable_measure_prodMk_left (ν := μ)
    ((measurable_outcomeOnSupported rate rewards C_star C_h control0 b u t q htq i)
      (measurableSet_singleton o))
  have he : (fun d : Observer => nativeMass rate rewards C_star C_h control0 b u t q htq i d o) =
      fun d => μ (Prod.mk d ⁻¹'
        (outcomeOnSupported rate rewards C_star C_h control0 b u t q htq i ⁻¹' {o})) := by
    funext d
    exact nativeMass_eq_fibreMass rate rewards C_star C_h control0 b u t q htq i d o
  rw [he]
  exact hm

/-- The explicit conditional lift to the ORIGINAL literal source/array/vector
carrier. It samples the finite outcome and its whole innovation fibre together;
the inserted source is still computed by the original transition. -/
def nativeLiftFibre (d : Observer) (o : Outcome p) :
    Measure (BranchLift rate rewards C_star C_h b u t) :=
  (FiniteFibreLift.fibreMeasure μ (fun ω => outcome (d, ω)) o).map
    (fun ω => restore (d, ω))

instance nativeLiftFibre_probability (d : Observer) (o : Outcome p) :
    IsProbabilityMeasure (nativeLiftFibre rate rewards C_star C_h control0 b u t q htq i d o) := by
  unfold nativeLiftFibre
  exact (Measure.isProbabilityMeasure_map_iff
    ((measurable_restoreSupported rate rewards C_star C_h control0 b u t q htq i).comp
      (measurable_const.prodMk measurable_id)).aemeasurable).mpr inferInstance

/-- Genuine source-preserving conditional reconstruction for the next
consumer. Every original private array, J, V, and original produced append is
carried by the literal restoration, even on zero atoms and zero index strata. -/
theorem nativeLiftFibre_reconstruction (d : Observer) :
    (∑ o, nativeMass rate rewards C_star C_h control0 b u t q htq i d o •
      nativeLiftFibre rate rewards C_star C_h control0 b u t q htq i d o) =
      (μ).map (fun ω => restore (d, ω)) := by
  have hm : Measurable (fun ω : Innovation p => restore (d, ω)) :=
    (measurable_restoreSupported rate rewards C_star C_h control0 b u t q htq i).comp
      (measurable_const.prodMk measurable_id)
  have h := congrArg (fun ν : Measure (Innovation p) => ν.map (fun ω => restore (d, ω)))
    (native_fibre_reconstruction rate rewards C_star C_h control0 b u t q htq i d)
  rw [Measure.map_finset_sum' hm.aemeasurable] at h
  simp only [Measure.map_smul (R := ℝ≥0∞) _ hm.aemeasurable] at h
  exact h

/-- The q-control already present in the inserted full-source field of the
canonical observation. It is available even in a PRE-q full observation. -/
def exposedCurrentControl (n : Fin (p.T + 1)) (o : PrefixObservation rate t n) : Control p :=
  ReferenceFirstCollectionRenewalVectorInsertion.c q o.1.1.1.2

/-- Reading full sources and restoring innovations use the SAME q-control,
at either PRE or POST boundaries. -/
theorem exposedCurrentControl_restored (n : Fin (p.T + 1)) (d : Observer) (ω : Innovation p) :
    exposedCurrentControl rate t q n
      (branchObservation rate rewards C_star C_h control0 b u t n (restore (d, ω))) = ω.1 := by
  have hsource : (branchObservation rate rewards C_star C_h control0 b u t n (restore (d, ω))).1.1.1.2 =
      insertedPhysicalSource rate (transition (restore (d, ω))) := by
    cases b <;> rfl
  unfold exposedCurrentControl
  rw [hsource]
  exact congrArg Prod.snd
    (restoreSupported_coordinates rate rewards C_star C_h control0 b u t q htq i d ω).1

/-- A replay on a full observation uses its source-dependent Dirac physical
control. Fresh auxiliary coordinates must be supplied separately; no physical
control is independently resampled while that full source is retained. -/
def replayControlLaw (n : Fin (p.T + 1)) (o : PrefixObservation rate t n) : Measure (Control p) :=
  Measure.dirac (exposedCurrentControl rate t q n o)

theorem replayControlLaw_restored (n : Fin (p.T + 1)) (d : Observer) (ω : Innovation p) :
    replayControlLaw rate t q n
      (branchObservation rate rewards C_star C_h control0 b u t n (restore (d, ω))) =
      Measure.dirac ω.1 := by
  unfold replayControlLaw
  rw [exposedCurrentControl_restored]

/-- The conditional source lift retains this deterministic control graph.
This identity applies to the entire source lift, rather than a logical marginal. -/
theorem native_fibre_control_graph (n : Fin (p.T + 1)) (d : Observer) (o : Outcome p) :
    (FiniteFibreLift.fibreMeasure μ (fun ω => outcome (d, ω)) o).map
      (fun ω => (branchObservation rate rewards C_star C_h control0 b u t n (restore (d, ω)), ω.1)) =
    (FiniteFibreLift.fibreMeasure μ (fun ω => outcome (d, ω)) o).map
      (fun ω =>
        let observation := branchObservation rate rewards C_star C_h control0 b u t n (restore (d, ω))
        (observation, exposedCurrentControl rate t q n observation)) := by
  congr 1
  funext ω
  exact Prod.ext rfl (exposedCurrentControl_restored rate rewards C_star C_h control0 b u t q htq i n d ω).symm

/-- LIVE never has an absent-cell atom, even on its frozen PRE branch. -/
theorem nativeMass_live_absent (d : Survivor)
    (hl : referenceSource rate rewards C_star C_h control0 b u t q htq i d.val ∈ liveDomain) :
    nativeMass rate rewards C_star C_h control0 b u t q htq i d.val (Sum.inl ()) = 0 := by
  have hp : (readPrefix d.val.val.val).1 =
      some (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d) :=
    (Option.some_get d.property.1).symm
  simp only [nativeMass, hp, dite_eq_left hl]
  exact ReferencePostInvocationLiveNativeLaw.nativeLaw_absent rate rewards C_star C_h q ⟨_, hl⟩

/-- PRE-overflow LIVE coefficients are exactly its effective frozen atom.
The physical record and complete numerical word remain in the joint test. -/
theorem nativeMass_live_overflow (d : Survivor)
    (hl : referenceSource rate rewards C_star C_h control0 b u t q htq i d.val ∈ liveDomain)
    (hpre : (continuingBefore rate rewards C_star C_h q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hl⟩).overflow = true)
    (o : Outcome p) :
    nativeMass rate rewards C_star C_h control0 b u t q htq i d.val o =
      (Measure.dirac (Sum.inr (none, frozenFastArm p, false, frozenSlowSet p) : Outcome p)) {o} := by
  have hp : (readPrefix d.val.val.val).1 =
      some (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d) :=
    (Option.some_get d.property.1).symm
  simp only [nativeMass, hp, dite_eq_left hl]
  exact congrArg (fun ν : Measure (Outcome p) => ν {o})
    (ReferencePostInvocationLiveNativeLaw.nativeLaw_overflow rate rewards C_star C_h q ⟨_, hl⟩ hpre)

/-- A disabled COLLECTION date has precisely the Unit atom, independently
of PRE overflow and without discarding that calendar date's physical word. -/
theorem nativeMass_collection_disabled (d : Survivor)
    (hl : referenceSource rate rewards C_star C_h control0 b u t q htq i d.val ∉ liveDomain)
    (hc : referenceSource rate rewards C_star C_h control0 b u t q htq i d.val ∈ collectionDomain)
    (hen : (collectionInput rate rewards C_star C_h q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hc⟩).enabled = false)
    (o : Outcome p) :
    nativeMass rate rewards C_star C_h control0 b u t q htq i d.val o =
      (Measure.dirac (Sum.inl () : Outcome p)) {o} := by
  have hp : (readPrefix d.val.val.val).1 =
      some (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d) :=
    (Option.some_get d.property.1).symm
  simp only [nativeMass, hp, dite_eq_right hl, dite_eq_left hc]
  let z : CollectionDateSource rate rewards C_star C_h q := ⟨_, hc⟩
  let U := (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d).1
  let a := (restore (d.val, referenceInnovation control0)).1.2
  exact (ReferencePostInvocationCollectionNativeLaw.sourceOutcome_mass
    rate rewards C_star C_h control0 q z U a o).symm.trans
      (congrArg (fun ν : Measure (Outcome p) => ν {o})
        (ReferencePostInvocationCollectionNativeLaw.sourceOutcome_disabled_law
          rate rewards C_star C_h control0 q z U a hen))

/-- Enabled COLLECTION with frozen PRE has the prescribed frozen tuple.
No POST-clear condition suppresses the first detecting update or its refresh. -/
theorem nativeMass_collection_overflow (d : Survivor)
    (hl : referenceSource rate rewards C_star C_h control0 b u t q htq i d.val ∉ liveDomain)
    (hc : referenceSource rate rewards C_star C_h control0 b u t q htq i d.val ∈ collectionDomain)
    (hen : (collectionInput rate rewards C_star C_h q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hc⟩).enabled = true)
    (hpre : (collectionBefore rate rewards C_star C_h q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hc⟩).overflow = true)
    (o : Outcome p) :
    nativeMass rate rewards C_star C_h control0 b u t q htq i d.val o =
      (Measure.dirac (Sum.inr (none, frozenFastArm p, false, frozenSlowSet p) : Outcome p)) {o} := by
  have hp : (readPrefix d.val.val.val).1 =
      some (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d) :=
    (Option.some_get d.property.1).symm
  simp only [nativeMass, hp, dite_eq_right hl, dite_eq_left hc]
  let z : CollectionDateSource rate rewards C_star C_h q := ⟨_, hc⟩
  let U := (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d).1
  let a := (restore (d.val, referenceInnovation control0)).1.2
  exact (ReferencePostInvocationCollectionNativeLaw.sourceOutcome_mass
    rate rewards C_star C_h control0 q z U a o).symm.trans
      (congrArg (fun ν : Measure (Outcome p) => ν {o})
        (ReferencePostInvocationCollectionNativeLaw.sourceOutcome_overflow_law
          rate rewards C_star C_h control0 q z U a hen hpre))

/-- Full LIVE cell equality consumes the accepted all-control cell producer;
the effective finite outcome never replaces the actual appended cell. -/
theorem currentCell_live (d : Survivor)
    (hl : referenceSource rate rewards C_star C_h control0 b u t q htq i d.val ∈ liveDomain)
    (ω : Innovation p) :
    currentCell rate rewards C_star C_h control0 b u t q (restore (d.val, ω)) =
      some (ReferencePostInvocationLiveNativeLaw.controlledCell rate rewards C_star C_h q
        ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hl⟩ ω.1 ω.2.2) := by
  unfold currentCell
  dsimp only
  rw [incomingPrefix_readout rate rewards C_star C_h control0 b u t q htq i d ω, Option.bind_some]
  have hl' := (restored_live_iff rate rewards C_star C_h control0 b u t q htq i d.val ω).mpr hl
  rw [noncallDateCell, dite_eq_left hl']
  have hz : (⟨insertedPhysicalSource rate (transition (restore (d.val, ω))), hl'⟩ :
      ContinuingLiveSource rate rewards C_star C_h q) =
      ReferencePostInvocationLiveNativeLaw.sourceAt rate rewards C_star C_h control0 q
        ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hl⟩ ω.1 := by
    apply Subtype.ext
    exact restored_source rate rewards C_star C_h control0 b u t q htq i d.val ω
  rw [hz, restoreSupported_auxiliary rate rewards C_star C_h control0 b u t q htq i
    d.val ω (referenceInnovation control0),
    ReferencePostInvocationLiveNativeLaw.sourceAt_logicalCell]

/-- The actual nonrenewed law restricted to its surviving POST-q prefix.
The original produced append and all original/inserted full-source fields
remain inside every arbitrary bounded Borel test. -/
theorem nonrenewed_surviving_native_joint_integral
    (Phi : PrefixObservation rate t q.succ → ℝ)
    (hPhi : Measurable Phi) (B : ℝ) (hB : ∀ o, ‖Phi o‖ ≤ B) :
    (∫ w, Phi (nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t q.succ w)
      ∂(ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw
        rate rewards C_star C_h u t control0).restrict
          {w | (nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t q.succ w).2.2.2.isSome = true}) =
    ∑ j : Fin (M p),
      ∫ d in observerGate rate rewards C_star C_h control0 false u t q htq j,
        ∑ o, (nativeMass rate rewards C_star C_h control0 false u t q htq j d o).toReal *
          ∫ ω, Phi (nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t q.succ
            (restoreSupported rate rewards C_star C_h control0 false u t q htq j (d, ω)))
            ∂FiniteFibreLift.fibreMeasure μ
              (fun ω => outcomeOnSupported rate rewards C_star C_h control0 false u t q htq j (d, ω)) o
        ∂supportedObserverLaw rate rewards C_star C_h control0 false u t q htq j := by
  have hE : {w : BranchLift rate rewards C_star C_h false u t |
      (nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t q.succ w).2.2.2.isSome = true} =
      survivingDomain rate rewards C_star C_h control0 false u t q := by
    ext w
    exact (survivingDomain_iff_next_prefix rate rewards C_star C_h control0 false u t q htq w).symm
  have h := congrArg (fun E : Set (BranchLift rate rewards C_star C_h false u t) =>
    ∫ w, Phi (branchObservation rate rewards C_star C_h control0 false u t q.succ w)
      ∂(branchLaw rate rewards C_star C_h control0 false u t).restrict E) hE
  exact h.trans (surviving_native_joint_integral
    rate rewards C_star C_h control0 false u t q htq Phi hPhi B hB)

/-- The same actual finite-fibre identity for the literal renewed law, with
the same rewards, constants, original arrays and unnormalized index masses. -/
theorem renewed_surviving_native_joint_integral
    (Phi : PrefixObservation rate t q.succ → ℝ)
    (hPhi : Measurable Phi) (B : ℝ) (hB : ∀ o, ‖Phi o‖ ≤ B) :
    (∫ w, Phi (renewedGeneratedObservation rate rewards C_star C_h control0 u t q.succ w)
      ∂(ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw
        rate rewards C_star C_h u t).restrict
          {w | (renewedGeneratedObservation rate rewards C_star C_h control0 u t q.succ w).2.2.2.isSome = true}) =
    ∑ j : Fin (M p),
      ∫ d in observerGate rate rewards C_star C_h control0 true u t q htq j,
        ∑ o, (nativeMass rate rewards C_star C_h control0 true u t q htq j d o).toReal *
          ∫ ω, Phi (renewedGeneratedObservation rate rewards C_star C_h control0 u t q.succ
            (restoreSupported rate rewards C_star C_h control0 true u t q htq j (d, ω)))
            ∂FiniteFibreLift.fibreMeasure μ
              (fun ω => outcomeOnSupported rate rewards C_star C_h control0 true u t q htq j (d, ω)) o
        ∂supportedObserverLaw rate rewards C_star C_h control0 true u t q htq j := by
  have hE : {w : BranchLift rate rewards C_star C_h true u t |
      (renewedGeneratedObservation rate rewards C_star C_h control0 u t q.succ w).2.2.2.isSome = true} =
      survivingDomain rate rewards C_star C_h control0 true u t q := by
    ext w
    exact (survivingDomain_iff_next_prefix rate rewards C_star C_h control0 true u t q htq w).symm
  have h := congrArg (fun E : Set (BranchLift rate rewards C_star C_h true u t) =>
    ∫ w, Phi (branchObservation rate rewards C_star C_h control0 true u t q.succ w)
      ∂(branchLaw rate rewards C_star C_h control0 true u t).restrict E) hE
  exact h.trans (surviving_native_joint_integral
    rate rewards C_star C_h control0 true u t q htq Phi hPhi B hB)

/-- On an actual disabled supported COLLECTION fibre, the complete stored
word advances with the false zero record. Absence of an appended logical cell
does not replace the numerical PRE by the last enabled cell's POST. -/
theorem supported_collection_disabled_word (d : Observer)
    (hc : referenceSource rate rewards C_star C_h control0 b u t q htq i d ∈ collectionDomain)
    (hen : (collectionInput rate rewards C_star C_h q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d, hc⟩).enabled = false)
    (ω : Innovation p) :
    let z := ReferencePostInvocationCollectionNativeLaw.replaceCollectionSource rate rewards C_star C_h control0 q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d, hc⟩ ω.1
    let W := collectionNumericalWord rate rewards C_star C_h q z
    let S := collectionBefore rate rewards C_star C_h q z
    let S' := RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (W.take (q.val + 1 - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h))
    insertedPhysicalSource rate (transition (restore (d, ω))) = z.val ∧
      ∀ j, S'.registers j = S.registers j ∧ S'.records j = S.records j ++ [(false, 0)] := by
  dsimp only
  let z := ReferencePostInvocationCollectionNativeLaw.replaceCollectionSource rate rewards C_star C_h control0 q
    ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d, hc⟩ ω.1
  refine ⟨restored_source rate rewards C_star C_h control0 b u t q htq i d ω, ?_⟩
  have hen' : (collectionInput rate rewards C_star C_h q z).enabled = false :=
    (ReferencePostInvocationCollectionNativeLaw.collectionEnabled_replace_control
      rate rewards C_star C_h control0 q _ ω.1).trans hen
  have hgrid := (ReferencePostInvocationGeneratedAlignment.collectionInput_oldGrid
    rate rewards C_star C_h q z).2
  have hdec := hgrid.symm.trans hen'
  have hboundary := Nat.le_of_not_gt (of_decide_eq_false hdec)
  exact (ReferencePostInvocationGeneratedAlignment.collection_disabled_word_step
    rate rewards C_star C_h q z hboundary).2

/-- A clear enabled bottom marker still services every actual queue on the
supported source family. There is no POST-overflow test on this update. -/
theorem supported_collection_bottom_service (d : Survivor) (ω : Innovation p)
    (hc : referenceSource rate rewards C_star C_h control0 b u t q htq i d.val ∈ collectionDomain)
    (hen : (collectionInput rate rewards C_star C_h q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hc⟩).enabled = true)
    (hpre : (collectionBefore rate rewards C_star C_h q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hc⟩).overflow = false)
    (hmarker : (collectionInput rate rewards C_star C_h q
      (ReferencePostInvocationCollectionNativeLaw.replaceCollectionSource rate rewards C_star C_h control0 q
        ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hc⟩ ω.1)).recordedArm = none) :
    let z := ReferencePostInvocationCollectionNativeLaw.replaceCollectionSource rate rewards C_star C_h control0 q
      ⟨referenceSource rate rewards C_star C_h control0 b u t q htq i d.val, hc⟩ ω.1
    let S := collectionBefore rate rewards C_star C_h q z
    let e := laterCollectionCell rate rewards C_star C_h q z
      (incomingPrefix rate rewards C_star C_h control0 b u t q htq i d).1 (restore (d.val, ω)).1.2
    ∀ j, e.arrivals j = (true, 0) ∧
      e.service j = min (4 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).n) (S.registers j).2 := by
  dsimp only
  apply ReferencePostInvocationCollectionNativeLaw.laterCollection_enabled_bottom_service
    rate rewards C_star C_h q _ _ _ _ _ hmarker
  · exact (ReferencePostInvocationCollectionNativeLaw.collectionEnabled_replace_control
      rate rewards C_star C_h control0 q _ ω.1).trans hen
  · exact congrArg RecordedQueueRun.RunState.overflow
      (ReferencePostInvocationCollectionNativeLaw.collectionBefore_replace_control
        rate rewards C_star C_h control0 q _ ω.1) |>.trans hpre

end Bandits.Support.ReferencePostInvocationNativeJointLaw

end
