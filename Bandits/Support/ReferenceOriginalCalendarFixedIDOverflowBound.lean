/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarNumericalOverflowBound
public import Bandits.Support.ReferenceFirstCollectionRenewalFixedIDOriginalPrefixLearning

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Original-calendar carried energy and fixed-ID overflow

The carried energy is localized on the original ID section at every date.
The same section is used in the initial selected-index update, each predictable
calendar continuation, and the actual successful renewed-birth cancellation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceOriginalCalendarFixedIDOverflowBound

variable {p : Parameters}
  (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)
  (ids : CompletePublicTable.IDArray p)

local notation "X" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "D" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids
local notation "ν" => ReferenceFixedIDSourceSection.fixedIDSourceLaw ids
local notation "CE" => ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
  rate rewards C_star C_h

private theorem fixedIDSourceSection_measurable (ids : CompletePublicTable.IDArray p) :
    MeasurableSet (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) :=
  ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids

private theorem fixedIDSourceSection_predictable (q : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (q.val + 1)] D :=
  ReferenceFirstCollectionPrecallFixedIDMean.measurableSet_fixedIDSourceSection_prefix
    control0 ids q.val

private theorem carriedStoppedEnergy_increment_integrable (q : Fin p.T) (a : Fin p.K) :
    Integrable (fun z : X => CE (q.val + 1) a z - CE q.val a z) mu := by
  exact (ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
    rate rewards C_star C_h (q.val + 1) (by omega) a).sub
    (ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
      rate rewards C_star C_h q.val q.isLt.le a)

include control0 in
private theorem firstSelector_increment_le_fixedID_mass (q : Fin p.T) (a : Fin p.K) :
    (∫ z in D,
      ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorIncrement
        rate rewards C_star C_h q a z ∂mu) ≤
      (mu).real (D ∩ ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
        rate rewards C_star C_h q) := by
  classical
  let F := ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
    rate rewards C_star C_h q
  let f := fun z : X => CE (q.val + 1) a z - CE q.val a z
  have hF : MeasurableSet F :=
    ReferenceOriginalCalendarFirstBranchIncrementTransport.measurableSet_firstSelectorEvent
      rate rewards C_star C_h control0 q a
  have hD : MeasurableSet D := fixedIDSourceSection_measurable ids
  have hEq : ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorIncrement
      rate rewards C_star C_h q a = Set.indicator F f := rfl
  have hIndicator : Set.indicator D (Set.indicator F f) = Set.indicator (D ∩ F) f := by
    funext z
    by_cases hzD : z ∈ D <;> by_cases hzF : z ∈ F <;>
      simp [Set.indicator, hzD, hzF]
  have hIntegral :
      (∫ z in D,
        ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorIncrement
          rate rewards C_star C_h q a z ∂mu) = ∫ z in D ∩ F, f z ∂mu := by
    calc
      _ = ∫ z, Set.indicator D
        (ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorIncrement
          rate rewards C_star C_h q a) z ∂mu :=
        (integral_indicator hD).symm
      _ = ∫ z, Set.indicator (D ∩ F) f z ∂mu := by rw [hEq, hIndicator]
      _ = ∫ z in D ∩ F, f z ∂mu :=
        integral_indicator (hD.inter hF)
  rw [hIntegral]
  let phase := ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 2
  rw [ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent_eq_sourcePhase
    rate rewards C_star C_h control0 q a]
  have hFphase : F = phase :=
    ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent_eq_sourcePhase
      rate rewards C_star C_h control0 q a
  let S : Fin (M p) → Set X := fun j =>
    ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h q
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)
  have hUnion : phase = ⋃ j : Fin (M p), S j :=
    ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_birth_iUnion
      rate rewards C_star C_h q
  have hSmeas (j : Fin (M p)) : MeasurableSet (S j) :=
    ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h q control0
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)
  have hSdis : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    apply ReferenceTotalSourcePairCoupling.sourceStratumEvent_disjoint
    intro h
    exact hij (congrArg Prod.fst h)
  have hIntegrable := carriedStoppedEnergy_increment_integrable
    rate rewards C_star C_h q a
  have hDunion : D ∩ phase = ⋃ j : Fin (M p), D ∩ S j := by
    rw [hUnion]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨hzD, j, hzS⟩
      exact ⟨j, hzD, hzS⟩
    · rintro ⟨j, hzD, hzS⟩
      exact ⟨hzD, j, hzS⟩
  have hDstrata (j : Fin (M p)) : MeasurableSet (D ∩ S j) :=
    hD.inter (hSmeas j)
  have hDdis : Pairwise (fun i j => Disjoint (D ∩ S i) (D ∩ S j)) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun z hz₁ hz₂ =>
      (Set.disjoint_left.mp (hSdis hij) hz₁.2 hz₂.2).elim
  have hIntegralUnion : (∫ z in D ∩ phase, f z ∂mu) =
      ∑ j : Fin (M p), ∫ z in D ∩ S j, f z ∂mu := by
    rw [hDunion, integral_iUnion_fintype hDstrata hDdis
      (fun _ => hIntegrable.integrableOn)]
  have hMassUnion : (mu).real (D ∩ phase) =
      ∑ j : Fin (M p), (mu).real (D ∩ S j) := by
    rw [hDunion, measureReal_iUnion_fintype hDdis hDstrata]
  rw [hFphase, hIntegralUnion, hMassUnion]
  apply Finset.sum_le_sum
  intro j _hj
  let Z := ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
    (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)
  let μZ := ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
    (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)
  let DJ : Set Z := {z | z.val ∈ D}
  have hS : MeasurableSet (S j) := hSmeas j
  have htransport (z : Z) :=
    ReferenceOriginalCalendarFirstDispatchEnergyTransport.carried_initial_first_update_transport
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (control0 := control0) (t := q) (a := a) (q := j) z
  let expAt := fun (n : ℕ) (z : X) => Real.exp
    (CanonicalRecordingRates.beta p rate.eta.val *
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
        rate rewards C_star C_h a n z)
  have hpoint : (fun z : Z => f z.val) =
      (fun z : Z => expAt (q.val + 1) z.val - expAt q.val z.val) := by
    funext z
    obtain ⟨_, _, _, _, hbefore, hafter, _, _⟩ := htransport z
    dsimp only [f, expAt]
    rw [hbefore, hafter,
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt_birth_before
        rate rewards C_star C_h j q z a,
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt_birth_after
        rate rewards C_star C_h j q control0 z a]
    rw [ReferenceFirstLaunchEnergyInitialization.birthBacklogExponential]
    simp [ReferenceFirstLiveCalendarPrefixReadout.queueParameters, Real.exp_zero]
  have hbirth := ReferenceFirstLiveRetainedIDExponentialStep.integral_exp_birth_originalID_step
    rate rewards C_star C_h j q control0 a ({ids}) (measurableSet_singleton ids)
  have hDJ : DJ = {z : Z | z.val.1.1 ∈ ({ids} : Set (CompletePublicTable.IDArray p))} := by
    ext z
    simp [DJ, ReferenceFixedIDSourceSection.fixedIDSourceSection]
  have hsetIntegral :
      (∫ z in D ∩ S j, f z ∂mu) = (∫ z in DJ, f z.val ∂μZ) := by
    have hfun : Set.indicator (D ∩ S j) f =
        Set.indicator (S j) (Set.indicator D f) := by
      funext z
      by_cases hzD : z ∈ D <;> by_cases hzS : z ∈ S j <;>
        simp [Set.indicator, hzD, hzS]
    calc
      _ = ∫ z, Set.indicator (D ∩ S j) f z ∂mu :=
        (integral_indicator (hD.inter hS)).symm
      _ = ∫ z, Set.indicator (S j) (Set.indicator D f) z ∂mu := by
        exact congrArg (fun g : X → ℝ => ∫ z, g z ∂mu) hfun
      _ = ∫ z in S j, Set.indicator D f z ∂mu := integral_indicator hS
      _ = ∫ z : Z, Set.indicator D f z.val ∂μZ := by
        exact (integral_subtype_comap hS (Set.indicator D f)).symm
      _ = ∫ z in DJ, f z.val ∂μZ := by
        have hsub : (fun z : Z => Set.indicator D f z.val) =
            Set.indicator DJ (fun z : Z => f z.val) := by
          funext z
          by_cases hz : z.val ∈ D <;> simp [DJ, Set.indicator, hz]
        have hDJmeas : MeasurableSet DJ :=
          hD.preimage measurable_subtype_coe
        exact (congrArg (fun g : Z → ℝ => ∫ z, g z ∂μZ) hsub).trans
          (integral_indicator hDJmeas)
  have hstep : (∫ z in DJ, f z.val ∂μZ) ≤ (μZ).real DJ := by
    calc
      _ = ∫ z in {z : Z | z.val.1.1 ∈ ({ids} : Set (CompletePublicTable.IDArray p))},
          expAt (q.val + 1) z.val - expAt q.val z.val ∂μZ := by
        rw [hDJ, hpoint]
      _ ≤ (μZ).real
          {z : Z | z.val.1.1 ∈ ({ids} : Set (CompletePublicTable.IDArray p))} := hbirth
      _ = (μZ).real DJ := by rw [← hDJ]
  have hmass : (μZ).real DJ = (mu).real (D ∩ S j) := by
    let f0 : Z → X := Subtype.val
    have hmap := ReferenceTotalSourceDisintegration.sourceStratumMeasure_map
      rate rewards C_star C_h q control0
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)
    calc
      _ = (μZ.map f0).real D := by
        symm
        rw [map_measureReal_apply (measurable_subtype_coe : Measurable f0) hD]
        rfl
      _ = ((sourceInputLaw p).restrict (S j)).real D := by
        rw [show μZ.map f0 = (sourceInputLaw p).restrict (S j) by
          simpa [f0, μZ] using hmap]
      _ = (sourceInputLaw p).real (D ∩ S j) := by
        rw [measureReal_restrict_apply hD]
  calc
    _ = ∫ z in DJ, f z.val ∂μZ := hsetIntegral
    _ ≤ (μZ).real DJ := hstep
    _ = (mu).real (D ∩ S j) := hmass

private theorem setIntegral_indicator_one (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫ z in A, B.indicator (fun _ : X => (1 : ℝ)) z ∂mu) =
      (sourceInputLaw p).real (A ∩ B) := by
  have hfun : Set.indicator A (B.indicator (fun _ : X => (1 : ℝ))) =
      Set.indicator (A ∩ B) (fun _ => (1 : ℝ)) := by
    funext z
    by_cases hzA : z ∈ A <;> by_cases hzB : z ∈ B <;>
      simp [Set.indicator, hzA, hzB]
  calc
    _ = ∫ z, Set.indicator A (B.indicator (fun _ : X => (1 : ℝ))) z ∂mu :=
      (integral_indicator hA).symm
    _ = ∫ z, Set.indicator (A ∩ B) (fun _ : X => (1 : ℝ)) z ∂mu := by
      exact congrArg (fun f : X → ℝ => ∫ z, f z ∂mu) hfun
    _ = ∫ z in A ∩ B, (1 : ℝ) ∂mu := integral_indicator (hA.inter hB)
    _ = (sourceInputLaw p).real (A ∩ B) := by
      simp only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ]

include control0 in
private theorem activeBirth_increment_fixedID_le_mass
    (q : Fin p.T) (a : Fin p.K) :
    (∫ z in D,
      ReferenceOriginalCalendarBirthExcessEnergyReduction.activeBirthIncrement
        rate rewards C_star C_h a q z ∂mu) ≤
      (sourceInputLaw p).real
        (D ∩ ReferenceOriginalCalendarBirthExcessEnergyReduction.activeBirthEvent
          rate rewards C_star C_h q) := by
  let S := ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet
    rate rewards C_star C_h q
  let δ := fun z : X => CE (q.val + 1) a z - CE q.val a z
  have hDfield :=
    ReferenceFirstCollectionPrecallFixedIDMean.measurableSet_fixedIDSourceSection_prefix
      control0 ids q.val
  have hFle : (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (q.val + 1) ≤ (inferInstance : MeasurableSpace X) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (q.val + 1)
  have hSameEvent :
      ReferenceOriginalCalendarBirthExcessEnergyReduction.activeBirthEvent
        rate rewards C_star C_h q = S := rfl
  have hSameFunction :
      ReferenceOriginalCalendarBirthExcessEnergyReduction.activeBirthIncrement
        rate rewards C_star C_h a q = Set.indicator S δ := by
    change (ReferenceOriginalCalendarBirthExcessEnergyReduction.activeBirthEvent
      rate rewards C_star C_h q).indicator δ = _
    rw [hSameEvent]
  have hDeltaInt :=
    ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdate_carriedIncrement_integrable
      rate rewards C_star C_h control0 q a
  have hMassCond :=
    ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdate_mass_condExp
      rate rewards C_star C_h control0 q
  have hCond :=
    ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdate_increment_condExp_le_mass
      rate rewards C_star C_h control0 q a
  have hSmeas : MeasurableSet S := by
    rw [← hSameEvent]
    exact ReferenceOriginalCalendarBirthExcessEnergyReduction.measurableSet_activeBirthEvent
      rate rewards C_star C_h q
  have hMass :
      (∫ z in D, Set.indicator S (fun _ : X => (1 : ℝ)) z ∂mu) =
        (sourceInputLaw p).real (D ∩ S) :=
    setIntegral_indicator_one D S
      (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids) hSmeas
  rw [hSameFunction]
  calc
    _ = ∫ z in D,
        mu[Set.indicator S δ |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)]
          z ∂mu :=
      (setIntegral_condExp hFle hDeltaInt hDfield).symm
    _ ≤ ∫ z in D,
        mu[Set.indicator S (fun _ : X => (1 : ℝ)) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)]
          z ∂mu := by
      apply integral_mono_ae integrable_condExp.integrableOn
        integrable_condExp.integrableOn
      exact ae_restrict_of_ae hCond
    _ = ∫ z in D, Set.indicator S (fun _ : X => (1 : ℝ)) z ∂mu :=
      setIntegral_condExp hFle hMassCond.1 hDfield
    _ = (sourceInputLaw p).real
        (D ∩ ReferenceOriginalCalendarBirthExcessEnergyReduction.activeBirthEvent
          rate rewards C_star C_h q) := by
      rw [hMass, hSameEvent]

include control0 in
private theorem continuingLive_branchContribution_fixedID_nonpos
    (q : Fin p.T) (a : Fin p.K) :
    (∫ z in D,
      ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
        rate rewards C_star C_h q a z
        (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
          rate rewards C_star C_h q z) ∂mu) ≤ 0 := by
  have hDfield :=
    ReferenceFirstCollectionPrecallFixedIDMean.measurableSet_fixedIDSourceSection_prefix
      control0 ids q.val
  have hFle : (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (q.val + 1) ≤ (inferInstance : MeasurableSpace X) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (q.val + 1)
  have hCond := ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.signedInheritedTerm_condExp
    rate rewards C_star C_h control0 q a
  have hEq := ReferenceOriginalCalendarLiveCollectionIncrementTransport.continuingLive_branchContribution_eq_signedInheritedTerm
    rate rewards C_star C_h q a
  rw [hEq]
  calc
    _ = ∫ z in D,
        mu[ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.signedInheritedTerm
          rate rewards C_star C_h q a |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)]
          z ∂mu :=
      (setIntegral_condExp hFle hCond.1 hDfield).symm
    _ ≤ ∫ z in D, (0 : ℝ) ∂mu := by
      apply integral_mono_ae integrable_condExp.integrableOn (integrable_const _).integrableOn
      exact ae_restrict_of_ae hCond.2
    _ = 0 := by simp

include control0 in
private theorem collectionOrCutoff_branchContribution_fixedID_nonpos
    (q : Fin p.T) (a : Fin p.K) :
    (∫ z in D,
      ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
        rate rewards C_star C_h q a z
        (ReferenceOriginalCalendarRetainedBranchPartition.collectionOrCutoffSelector
          rate rewards C_star C_h q z) ∂mu) ≤ 0 := by
  let W := ReferenceOriginalCalendarCollectionRetainedEnergyStep.W rate rewards C_star C_h q a
  let E := ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX rate rewards C_star C_h q a
  let A := fun z : X => E z - 1
  let term := fun z : X => W z * A z
  have hDfield :=
    ReferenceFirstCollectionPrecallFixedIDMean.measurableSet_fixedIDSourceSection_prefix
      control0 ids q.val
  have hFle : (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (q.val + 1) ≤ (inferInstance : MeasurableSpace X) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (q.val + 1)
  have hEInt := ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX_integrable
    rate rewards C_star C_h q a control0
  have hAInt : Integrable A mu := hEInt.sub (integrable_const (1 : ℝ))
  have hWMeas := ReferenceOriginalCalendarCollectionRetainedEnergyStep.W_measurable
    rate rewards C_star C_h control0 q a
  have hWBounds : ∀ z, 0 ≤ W z ∧ W z ≤
      Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
        (2 * (1 / (32 * rate.eta.val)))) := by
    intro z
    by_cases hz : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.B
        rate rewards C_star C_h q
    · simpa only [W, ReferenceOriginalCalendarCollectionRetainedEnergyStep.W,
        Set.indicator_of_mem hz] using
        (ReferenceOriginalCalendarCollectionRetainedEnergyStep.queueExp_bounds
          rate rewards C_star C_h a q.val z)
    · simp only [W, ReferenceOriginalCalendarCollectionRetainedEnergyStep.W,
        Set.indicator_of_notMem hz]
      exact ⟨le_rfl, Real.exp_nonneg _⟩
  have htermInt : Integrable term mu := by
    have hAW : Integrable (fun z : X => A z * W z) mu := by
      apply hAInt.mul_bdd (hWMeas.mono hFle le_rfl).aestronglyMeasurable
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (hWBounds z).1]
      exact hWBounds z |>.2
    have hcomm : (fun z : X => A z * W z) = term := by
      funext z
      simp only [term]
      ring
    rw [← hcomm]
    exact hAW
  have hBranchEq :=
    ReferenceOriginalCalendarLiveCollectionIncrementTransport.collectionOrCutoff_branchContribution_eq_retainedEnergyTerm
      rate rewards C_star C_h q a
  have hPull := condExp_mul_of_aestronglyMeasurable_left
    hWMeas.aestronglyMeasurable htermInt hAInt
  have hSub := condExp_sub hEInt (integrable_const (1 : ℝ))
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1))
  have hOne := condExp_const (μ := mu) hFle (1 : ℝ)
  rw [hOne] at hSub
  have hELe := ReferenceOriginalCalendarCollectionRetainedEnergyStep.condExp_expX_le_one
    rate rewards C_star C_h control0 q a
  have hTermCond : mu[term |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)]
      ≤ᵐ[mu] (fun _ => (0 : ℝ)) := by
    filter_upwards [hPull, hSub, hELe] with z hp hs he
    change mu[W * A |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] z ≤ 0
    rw [hp]
    have hAcond : mu[A |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] z =
        mu[E | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
          (q.val + 1)] z - 1 := by
      change mu[(ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX
          rate rewards C_star C_h q a - fun _ : X => (1 : ℝ)) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
            (q.val + 1)] z =
        (mu[ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX
            rate rewards C_star C_h q a |
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
              (q.val + 1)] - fun _ : X => (1 : ℝ)) z
      exact hs
    have hAcondNonpos : mu[A |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
          (q.val + 1)] z ≤ 0 := by
      rw [hAcond]
      exact sub_nonpos.mpr he
    exact mul_nonpos_of_nonneg_of_nonpos (hWBounds z).1 hAcondNonpos
  rw [hBranchEq]
  calc
    _ = ∫ z in D,
        mu[term | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
          (q.val + 1)] z ∂mu :=
      (setIntegral_condExp hFle htermInt hDfield).symm
    _ ≤ ∫ z in D, (0 : ℝ) ∂mu := by
      apply integral_mono_ae integrable_condExp.integrableOn (integrable_const _).integrableOn
      exact ae_restrict_of_ae hTermCond
    _ = 0 := by simp

include control0 in
private theorem carriedStoppedEnergy_fixedID_increment_le_mass
    (q : Fin p.T) (a : Fin p.K) :
    (∫ z in D, CE (q.val + 1) a z - CE q.val a z ∂mu) ≤
      (sourceInputLaw p).real D := by
  let F := ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
    rate rewards C_star C_h q
  let B := ReferenceOriginalCalendarBirthExcessEnergyReduction.activeBirthEvent
    rate rewards C_star C_h q
  let C := (F ∪ B)ᶜ
  let first := ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorIncrement
    rate rewards C_star C_h q a
  let birth := ReferenceOriginalCalendarBirthExcessEnergyReduction.activeBirthIncrement
    rate rewards C_star C_h a q
  let complement := C.indicator (fun _ : X => (1 : ℝ))
  let live := fun z : X =>
    ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
      rate rewards C_star C_h q a z
      (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
        rate rewards C_star C_h q z)
  let collection := fun z : X =>
    ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
      rate rewards C_star C_h q a z
      (ReferenceOriginalCalendarRetainedBranchPartition.collectionOrCutoffSelector
        rate rewards C_star C_h q z)
  let sumBranches := fun z : X => first z + birth z + complement z +
    (live z + collection z)
  have hD : MeasurableSet D :=
    ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hF : MeasurableSet F :=
    ReferenceOriginalCalendarFirstBranchIncrementTransport.measurableSet_firstSelectorEvent
      rate rewards C_star C_h control0 q a
  have hB : MeasurableSet B :=
    ReferenceOriginalCalendarBirthExcessEnergyReduction.measurableSet_activeBirthEvent
      rate rewards C_star C_h q
  have hC : MeasurableSet C := (hF.union hB).compl
  have hfirstInt :=
    ReferenceOriginalCalendarFirstBranchIncrementTransport.integrable_firstSelectorIncrement
      rate rewards C_star C_h control0 q a
  have hbirthInt :=
    ReferenceOriginalCalendarBirthExcessEnergyReduction.integrable_activeBirthIncrement
      rate rewards C_star C_h a q
  have hcompInt : Integrable complement mu :=
    (integrable_const (1 : ℝ)).indicator hC
  have hliveInt :=
    ReferenceOriginalCalendarLiveCollectionIncrementTransport.continuingLive_branchContribution_integrable
      rate rewards C_star C_h control0 q a
  have hcollectionInt :=
    ReferenceOriginalCalendarLiveCollectionIncrementTransport.collectionOrCutoff_branchContribution_integrable
      rate rewards C_star C_h control0 q a
  have hdeltaInt := carriedStoppedEnergy_increment_integrable
    rate rewards C_star C_h q a
  have hsumInt : Integrable sumBranches mu := by
    exact (((hfirstInt.add hbirthInt).add hcompInt).add
      (hliveInt.add hcollectionInt))
  have hpoint (z : X) : CE (q.val + 1) a z - CE q.val a z ≤ sumBranches z := by
    exact ReferenceOriginalCalendarBirthExcessEnergyReduction.carriedStoppedEnergy_increment_le_branch_reduction
      rate rewards C_star C_h a q z
  have hmon := integral_mono (μ := (sourceInputLaw p).restrict D)
    hdeltaInt.integrableOn hsumInt.integrableOn hpoint
  have hsplit : (∫ z in D, sumBranches z ∂mu) =
      (∫ z in D, first z ∂mu) + (∫ z in D, birth z ∂mu) +
        (∫ z in D, complement z ∂mu) +
        ((∫ z in D, live z ∂mu) + (∫ z in D, collection z ∂mu)) := by
    let μD := (sourceInputLaw p).restrict D
    change (∫ z, ((first z + birth z) + complement z) +
        (live z + collection z) ∂μD) = _
    calc
      _ = (∫ z, (first z + birth z) + complement z ∂
            μD) + (∫ z, live z + collection z ∂μD) :=
        integral_add (((hfirstInt.add hbirthInt).add hcompInt).integrableOn)
          ((hliveInt.add hcollectionInt).integrableOn)
      _ = ((∫ z, first z ∂((sourceInputLaw p).restrict D)) +
            ∫ z, birth z ∂μD) + ∫ z, complement z ∂μD +
          (∫ z, live z ∂μD + ∫ z, collection z ∂μD) := by
        have hleft : (∫ z, (first z + birth z) + complement z ∂μD) =
            (∫ z, first z + birth z ∂μD) + (∫ z, complement z ∂μD) :=
          integral_add ((hfirstInt.add hbirthInt).integrableOn) hcompInt.integrableOn
        have hright : (∫ z, live z + collection z ∂μD) =
            (∫ z, live z ∂μD) + (∫ z, collection z ∂μD) :=
          integral_add hliveInt.integrableOn hcollectionInt.integrableOn
        have hfirstBirth : (∫ z, first z + birth z ∂μD) =
            (∫ z, first z ∂μD) + (∫ z, birth z ∂μD) :=
          integral_add hfirstInt.integrableOn hbirthInt.integrableOn
        rw [hleft, hright, hfirstBirth]
  have hfirst := firstSelector_increment_le_fixedID_mass
    rate rewards C_star C_h control0 ids q a
  have hbirth := activeBirth_increment_fixedID_le_mass
    rate rewards C_star C_h control0 ids q a
  have hlive := continuingLive_branchContribution_fixedID_nonpos
    rate rewards C_star C_h control0 ids q a
  have hcollection := collectionOrCutoff_branchContribution_fixedID_nonpos
    rate rewards C_star C_h control0 ids q a
  let Aset := D ∩ F
  let Bset := D ∩ B
  let Cset := D ∩ C
  let FBset := Aset ∪ Bset
  let allSet := FBset ∪ Cset
  have hAmeas : MeasurableSet Aset := hD.inter hF
  have hBmeas : MeasurableSet Bset := hD.inter hB
  have hCmeas : MeasurableSet Cset := hD.inter hC
  have hABdis : Disjoint Aset Bset := by
    apply Set.disjoint_left.mpr
    intro z hzA hzB
    exact (Set.disjoint_left.mp
      (ReferenceOriginalCalendarBirthExcessEnergyReduction.firstSelectorEvent_disjoint_activeBirthEvent
        rate rewards C_star C_h q) hzA.2 hzB.2).elim
  have hAllDis : Disjoint FBset Cset := by
    apply Set.disjoint_left.mpr
    intro z hzFB hzC
    rcases hzFB with hzA | hzB
    · exact hzC.2 (Or.inl hzA.2)
    · exact hzC.2 (Or.inr hzB.2)
  have hFBmeas : MeasurableSet FBset := hAmeas.union hBmeas
  have hAllmeas : MeasurableSet allSet := hFBmeas.union hCmeas
  have hFBmass : (sourceInputLaw p).real FBset =
      (sourceInputLaw p).real Aset + (sourceInputLaw p).real Bset :=
    measureReal_union hABdis hBmeas
  have hAllMass : (sourceInputLaw p).real allSet =
      (sourceInputLaw p).real FBset + (sourceInputLaw p).real Cset :=
    measureReal_union hAllDis hCmeas
  have hAllSub : allSet ⊆ D := by
    intro z hz
    rcases hz with hz | hz
    · rcases hz with hz | hz
      · exact hz.1
      · exact hz.1
    · exact hz.1
  have hMassSum :
      (sourceInputLaw p).real (D ∩ F) +
        (sourceInputLaw p).real (D ∩ B) +
        (sourceInputLaw p).real (D ∩ (F ∪ B)ᶜ) ≤
      (sourceInputLaw p).real D := by
    calc
      _ = (sourceInputLaw p).real FBset + (sourceInputLaw p).real Cset := by
        dsimp [Aset, Bset, Cset, FBset]
        rw [hFBmass]
      _ = (sourceInputLaw p).real allSet := by
        dsimp [allSet]
        rw [hAllMass]
      _ ≤ (sourceInputLaw p).real D := measureReal_mono hAllSub
  have hfirstMass := firstSelector_increment_le_fixedID_mass
    rate rewards C_star C_h control0 ids q a
  have hbirthMass := activeBirth_increment_fixedID_le_mass
    rate rewards C_star C_h control0 ids q a
  have hcompMass : (∫ z in D, complement z ∂mu) =
      (sourceInputLaw p).real (D ∩ (F ∪ B)ᶜ) := by
    exact setIntegral_indicator_one D C hD hC
  calc
    _ ≤ ∫ z in D, sumBranches z ∂mu := hmon
    _ = _ := hsplit
    _ ≤ (sourceInputLaw p).real (D ∩ F) +
        (sourceInputLaw p).real (D ∩ B) +
        (sourceInputLaw p).real (D ∩ (F ∪ B)ᶜ) := by
      rw [hcompMass]
      linarith [hfirst, hbirth, hlive, hcollection]
    _ ≤ (sourceInputLaw p).real D := hMassSum

include control0 in
/-- Every original carried stopped energy prefix is bounded after restricting
the integral to the same literal fixed-ID section at each calendar date. -/
public theorem integral_carriedStoppedEnergy_prefix_fixedID_le
    (n : ℕ) (hn : n ≤ p.T) (a : Fin p.K) :
    (∫ z in D, CE n a z ∂mu) ≤ ((n : ℝ) + 1) * (sourceInputLaw p).real D := by
  induction n with
  | zero =>
      have hzero : CE 0 a = fun _ : X => (1 : ℝ) := by
        funext z
        exact ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy_zero
          rate rewards C_star C_h a z
      rw [hzero]
      simp only [integral_const, smul_eq_mul, mul_one,
        measureReal_restrict_apply_univ, Nat.cast_zero, zero_add, one_mul, le_rfl]
  | succ n ih =>
      have hnt : n < p.T := by omega
      have hprev := ih (by omega)
      let q : Fin p.T := ⟨n, hnt⟩
      have hstep := carriedStoppedEnergy_fixedID_increment_le_mass
        rate rewards C_star C_h control0 ids q a
      have hnextInt := ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
        rate rewards C_star C_h (n + 1) (by omega) a
      have hcurInt := ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
        rate rewards C_star C_h n (by omega) a
      have hstepEq : (∫ z in D, CE (n + 1) a z ∂mu) =
          (∫ z in D, CE n a z ∂mu) +
            (∫ z in D, CE (n + 1) a z - CE n a z ∂mu) := by
        rw [integral_sub hnextInt.integrableOn hcurInt.integrableOn]
        ring
      calc
        _ = (∫ z in D, CE n a z ∂mu) +
            (∫ z in D, CE (n + 1) a z - CE n a z ∂mu) := hstepEq
        _ ≤ ((n : ℝ) + 1) * (sourceInputLaw p).real D +
              (sourceInputLaw p).real D := add_le_add hprev hstep
        _ = (((n + 1 : ℕ) : ℝ) + 1) * (sourceInputLaw p).real D := by
          push_cast
          ring

private theorem beta_mul_backlogCap_eq_L_stab :
    CanonicalRecordingRates.beta p rate.eta.val *
        ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate =
      (CanonicalRecordingRates.L_stab p : ℝ) := by
  rw [CanonicalRecordingRates.beta,
    ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap]
  field_simp [ne_of_gt rate.eta.property]

private theorem fixedID_terminal_factor_le_inv_N_sq :
    (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) ≤
      1 / (N p : ℝ) ^ 2 := by
  have hArgNat : 0 < 2 * p.K * (p.T + 1) * (N p) ^ 2 := by
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide)
      (ConstructorDimensions.K_pos p)) (Nat.zero_lt_succ p.T))
      (Nat.pow_pos (ConstructorDimensions.N_pos p))
  have hlog := CanonicalRecordingRates.log_stabArgument_le_L_stab p
  have hexpNat :
      (((2 * p.K * (p.T + 1) * (N p) ^ 2 : ℕ) : ℝ)) ≤
        Real.exp (CanonicalRecordingRates.L_stab p : ℝ) := by
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by exact_mod_cast hArgNat)] at hexp
    exact hexp
  have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hT : 0 < (p.T : ℝ) + 1 := by positivity
  have hN : 0 < (N p : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.N_pos p)
  have hN2 : 0 < (N p : ℝ) ^ 2 := sq_pos_of_pos hN
  have hden : 0 < Real.exp (CanonicalRecordingRates.L_stab p : ℝ) := Real.exp_pos _
  have hlarge :
      ((p.K : ℝ) * ((p.T : ℝ) + 1)) * (N p : ℝ) ^ 2 ≤
        Real.exp (CanonicalRecordingRates.L_stab p : ℝ) := by
    have hcast :
        2 * (p.K : ℝ) * ((p.T : ℝ) + 1) * (N p : ℝ) ^ 2 ≤
          Real.exp (CanonicalRecordingRates.L_stab p : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
        Nat.cast_pow] using hexpNat
    nlinarith
  have hnum :
      ((p.K : ℝ) * ((p.T : ℝ) + 1)) *
          Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) ≤
        1 / (N p : ℝ) ^ 2 := by
    rw [Real.exp_neg]
    field_simp [ne_of_gt hden, ne_of_gt hN2]
    nlinarith [hlarge]
  exact hnum

include control0 in
private theorem terminalArm_fixedID_measureReal_le_exp (a : Fin p.K) :
    (sourceInputLaw p).real
        (D ∩ {z : X | Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) <
          CE p.T a z}) ≤
      ((p.T : ℝ) + 1) * (sourceInputLaw p).real D *
        Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
  let level := Real.exp (CanonicalRecordingRates.L_stab p : ℝ)
  let upper := {z : X | level ≤ CE p.T a z}
  let overflow := {z : X | Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
    ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) < CE p.T a z}
  have hscale := beta_mul_backlogCap_eq_L_stab rate
  have hlevel : Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
      ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) = level :=
    congrArg Real.exp hscale
  have hupperMeas : MeasurableSet upper :=
    measurableSet_le measurable_const
      (ReferenceOriginalCalendarCarriedStoppedEnergy.measurable_carriedStoppedEnergy
        rate rewards C_star C_h p.T a)
  have hsubset : D ∩ overflow ⊆ D ∩ upper := by
    intro z hz
    rcases hz with ⟨hzD, hzOverflow⟩
    refine ⟨hzD, ?_⟩
    change Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
      ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) < CE p.T a z at hzOverflow
    rw [hlevel] at hzOverflow
    exact hzOverflow.le
  have hnonnegMu : 0 ≤ᵐ[mu] CE p.T a := by
    filter_upwards [] with z
    exact le_trans (by norm_num)
      (ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy_bounds
        rate rewards C_star C_h p.T le_rfl a z).1
  have hnonneg : 0 ≤ᵐ[(sourceInputLaw p).restrict D] CE p.T a :=
    ae_restrict_of_ae hnonnegMu
  have hCEInt :=
    ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
      rate rewards C_star C_h p.T le_rfl a
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hCEInt.integrableOn level
  have hterminal := integral_carriedStoppedEnergy_prefix_fixedID_le
    rate rewards C_star C_h control0 ids p.T le_rfl a
  have hmarkov' : level * ((sourceInputLaw p).restrict D).real upper ≤
      ((p.T : ℝ) + 1) * (sourceInputLaw p).real D := by
    calc
      _ ≤ ∫ z, CE p.T a z ∂((sourceInputLaw p).restrict D) := hmarkov
      _ = ∫ z in D, CE p.T a z ∂mu := rfl
      _ ≤ ((p.T : ℝ) + 1) * (sourceInputLaw p).real D := hterminal
  have hupper : ((sourceInputLaw p).restrict D).real upper ≤
      (((p.T : ℝ) + 1) * (sourceInputLaw p).real D) / level := by
    apply (le_div_iff₀ (Real.exp_pos _)).2
    nlinarith [hmarkov']
  have hrestrict : ((sourceInputLaw p).restrict D).real upper =
      (sourceInputLaw p).real (D ∩ upper) := by
    rw [measureReal_restrict_apply hupperMeas, Set.inter_comm]
  have hbound : (sourceInputLaw p).real (D ∩ overflow) ≤
      (((p.T : ℝ) + 1) * (sourceInputLaw p).real D) / level := by
    calc
      _ ≤ (sourceInputLaw p).real (D ∩ upper) := measureReal_mono hsubset
      _ = ((sourceInputLaw p).restrict D).real upper := hrestrict.symm
      _ ≤ _ := hupper
  calc
    _ ≤ (((p.T : ℝ) + 1) * (sourceInputLaw p).real D) / level := hbound
    _ = ((p.T : ℝ) + 1) * (sourceInputLaw p).real D *
        Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
      rw [div_eq_mul_inv]
      dsimp [level]
      rw [← Real.exp_neg]

private theorem fixedIDSourceLaw_localized_event_bound
    (E : Set X) (hE : MeasurableSet E)
    (hLocal : (sourceInputLaw p).real (D ∩ E) ≤
      (sourceInputLaw p).real D / (N p : ℝ) ^ 2) :
    (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).real E ≤
      1 / (N p : ℝ) ^ 2 := by
  have hsection := ReferenceFixedIDSourceSection.sourceInputLaw_real_fixedIDSourceSection ids
  have hpos : 0 < (sourceInputLaw p).real D := by
    rw [hsection]
    exact ReferenceFixedIDSourceSection.idArrayAtom_positive ids
  have hlocal' :
      (CompletePublicTable.idArrayMeasure p).real {ids} *
          (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).real E ≤
        (CompletePublicTable.idArrayMeasure p).real {ids} / (N p : ℝ) ^ 2 := by
    have htransport := hLocal
    rw [ReferenceFixedIDSourceSection.sourceInputLaw_real_inter_fixedIDSourceSection
      ids E hE] at htransport
    rw [hsection] at htransport
    exact htransport
  apply le_of_mul_le_mul_left _
    (ReferenceFixedIDSourceSection.idArrayAtom_positive ids)
  calc
    _ ≤ (CompletePublicTable.idArrayMeasure p).real {ids} / (N p : ℝ) ^ 2 := hlocal'
    _ = (CompletePublicTable.idArrayMeasure p).real {ids} *
        (1 / (N p : ℝ) ^ 2) := by ring

include control0 in
/-- The numerical detector tail under the original source law, localized to
the same fixed identification section throughout the calendar. -/
public theorem observedNumericalOverflowEvent_fixedID_measureReal_le_inv_N_sq :
    (sourceInputLaw p).real
        (D ∩ ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
          rate rewards C_star C_h) ≤
      (sourceInputLaw p).real D / (N p : ℝ) ^ 2 := by
  let terminalArm := fun a : Fin p.K => {z : X |
    Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
      ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) < CE p.T a z}
  have hUnion : {z : X | ∃ a : Fin p.K,
      Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
        ReferenceOriginalCalendarCarriedStoppedEnergy.backlogCap rate) < CE p.T a z} =
      ⋃ a : Fin p.K, terminalArm a := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, terminalArm]
  have hDUnion : D ∩ (⋃ a : Fin p.K, terminalArm a) =
      ⋃ a : Fin p.K, D ∩ terminalArm a := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨hzD, a, hz⟩
      exact ⟨a, hzD, hz⟩
    · rintro ⟨a, hzD, hz⟩
      exact ⟨hzD, a, hz⟩
  rw [ReferenceOriginalCalendarCarriedStoppedEnergy.observedNumericalOverflowEvent_eq_terminalCarriedEnergy
      rate rewards C_star C_h, hUnion, hDUnion]
  have haID : 0 ≤ (sourceInputLaw p).real D := measureReal_nonneg
  calc
    _ ≤ ∑ a : Fin p.K, (sourceInputLaw p).real (D ∩ terminalArm a) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _a : Fin p.K,
        ((p.T : ℝ) + 1) * (sourceInputLaw p).real D *
          Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
      apply Finset.sum_le_sum
      intro a _ha
      simpa only [terminalArm] using
        terminalArm_fixedID_measureReal_le_exp rate rewards C_star C_h control0 ids a
    _ = (p.K : ℝ) * ((p.T : ℝ) + 1) * (sourceInputLaw p).real D *
          Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ (sourceInputLaw p).real D / (N p : ℝ) ^ 2 := by
      have hfactor := fixedID_terminal_factor_le_inv_N_sq (p := p)
      calc
        _ = ((p.K : ℝ) * ((p.T : ℝ) + 1) *
              Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ))) *
              (sourceInputLaw p).real D := by ring
        _ ≤ (1 / (N p : ℝ) ^ 2) * (sourceInputLaw p).real D :=
          mul_le_mul_of_nonneg_right hfactor haID
        _ = (sourceInputLaw p).real D / (N p : ℝ) ^ 2 := by ring

include control0 in
/-- The physical first-crossing tail on the fixed-ID section follows from the
accepted pointwise identity with the numerical detector. -/
public theorem physicalFirstOverflowEvent_fixedID_measureReal_le_inv_N_sq :
    (sourceInputLaw p).real
        (D ∩ ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
          rate rewards C_star C_h) ≤
      (sourceInputLaw p).real D / (N p : ℝ) ^ 2 := by
  rw [ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent_eq_observedNumericalOverflowEvent
    rate rewards C_star C_h]
  exact observedNumericalOverflowEvent_fixedID_measureReal_le_inv_N_sq
    rate rewards C_star C_h control0 ids

include control0 in
/-- The fixed-ID section law inherits the numerical tail after dividing by the
positive atom of the original identification array. -/
public theorem observedNumericalOverflowEvent_fixedIDSourceLaw_le_inv_N_sq :
    (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).real
        (ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
          rate rewards C_star C_h) ≤
      1 / (N p : ℝ) ^ 2 := by
  exact fixedIDSourceLaw_localized_event_bound ids
    (ReferenceOriginalNumericalFirstOverflowLocator.observedNumericalOverflowEvent
      rate rewards C_star C_h)
    (ReferenceOriginalCalendarNumericalOverflowBound.measurableSet_observedNumericalOverflowEvent
      rate rewards C_star C_h)
    (observedNumericalOverflowEvent_fixedID_measureReal_le_inv_N_sq
      rate rewards C_star C_h control0 ids)

include control0 in
/-- The fixed-ID section law inherits the physical first-crossing tail through
the accepted pointwise source-event identity. -/
public theorem physicalFirstOverflowEvent_fixedIDSourceLaw_le_inv_N_sq :
    (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids).real
        (ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
          rate rewards C_star C_h) ≤
      1 / (N p : ℝ) ^ 2 := by
  have hPhysicalMeas : MeasurableSet
      (ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
        rate rewards C_star C_h) := by
    rw [ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent_eq_observedNumericalOverflowEvent
      rate rewards C_star C_h]
    exact ReferenceOriginalCalendarNumericalOverflowBound.measurableSet_observedNumericalOverflowEvent
      rate rewards C_star C_h
  exact fixedIDSourceLaw_localized_event_bound ids
    (ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
      rate rewards C_star C_h)
    hPhysicalMeas
    (physicalFirstOverflowEvent_fixedID_measureReal_le_inv_N_sq
      rate rewards C_star C_h control0 ids)

end Bandits.Support.ReferenceOriginalCalendarFixedIDOverflowBound

end
