/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarLiveCollectionWeightedDrift
public import Bandits.Support.ReferenceOriginalCalendarLaterBirthWeightedDrift
public import Bandits.Support.ReferenceOriginalCalendarBirthBranchIncrementTransport
public import Bandits.Support.ReferenceFirstCollectionRenewalFixedIDOriginalPrefixLearning
public import Bandits.Support.ReferenceCompleteOriginalCalendarRateFeasibility

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Fixed-ID nonfirst original-calendar learning observations

These estimates localize the actual retained LIVE, renewed-birth, and
unrestricted collection updates to a fixed original shared-ID section before
integration. They use the same full optional queue prefix and the literal
source branch at the current calendar date.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) :=
  ReferenceOriginalCalendarCollectionRetainedEnergyStep.optionMeasurableSpace

variable {p : Parameters}
  (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)
  (ids : CompletePublicTable.IDArray p)
  (S : ProductSetLaw.ProductSet p.K p.m) (q : Fin p.T)

local notation "X" => SourceInput p
local notation "μ" => sourceInputLaw p
local notation "D" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids
local notation "F" => ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
  control0 (q.val + 1)
local notation "PI" => ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
  rate rewards C_star C_h
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "cell" => ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
  rate rewards C_star C_h q
local notation "θ" => ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
  rate rewards C_star C_h
local notation "V" => ReferenceOriginalCalendarLiveCollectionWeightedDrift.V
  rate rewards C_star C_h
local notation "C" => ReferenceOriginalCalendarLiveCollectionWeightedDrift.C
  rate rewards C_star C_h
local notation "ΔV" => ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV
  rate rewards C_star C_h

/-- Accepted normalized queue arrival from the same optional full numerical
prefix and optional current cell. Either missing observation contributes zero. -/
public def acceptedArrivalAt (t : Fin p.T) (i : Fin p.K) (z : X) : ℝ :=
  match PI t.val z, ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
      rate rewards C_star C_h t z with
  | some past, some c =>
      (RecordedQueueRun.acceptedArrival
        (RecordedQueueRun.acceptedRecord Q (RecordedQueueRun.run Q past) c i) : ℝ) /
        (rate.n : ℝ)
  | _, _ => 0

/-- Current-prefix weighted accepted arrival, with the same full θ vector as
the square-potential observation. -/
public def weightedAcceptedArrival (t : Fin p.T) (z : X) : ℝ :=
  ∑ i : Fin p.K,
    ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
      rate rewards C_star C_h t.val i z * acceptedArrivalAt rate rewards C_star C_h t i z

/-- Comparator-minus-current-marginal gap for the accepted raw arrivals. -/
public def acceptedArrivalComparatorGap (t : Fin p.T) (z : X) : ℝ :=
  (∑ i ∈ S.1, acceptedArrivalAt rate rewards C_star C_h t i z) -
    weightedAcceptedArrival rate rewards C_star C_h t z

/-- Rounded reward at the original calendar date from the fixed whole table. -/
public def roundedRewardAt (t : Fin p.T) (i : Fin p.K) : ℝ :=
  ReferenceFirstCollectionOldRecorderFoundation.roundedReward rewards t i

/-- The signed reward comparison is zero off the actual retained update. -/
public def retainedRewardGap (t : Fin p.T) (z : X) : ℝ :=
  ({z | ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h t z}).indicator (fun z =>
    (∑ i ∈ S.1, roundedRewardAt rewards t i) -
      ∑ i : Fin p.K,
        ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
          rate rewards C_star C_h t.val i z *
          roundedRewardAt rewards t i) z

/-- The actual selected-cell rate floor, zero when the optional cell is absent. -/
public def retainedRateFloor (t : Fin p.T) (z : X) : ℝ :=
  ({z | ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h t z}).indicator (fun z =>
    match ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
        rate rewards C_star C_h t z with
    | none => 0
    | some c => ∑ i ∈ S.1, c.rate i / (rate.n : ℝ)) z

public def liveBranch : Set X :=
  ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveRetainedGate
    rate rewards C_star C_h q

public def renewedBirthBranch : Set X :=
  ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet
    rate rewards C_star C_h q

public def collectionBranch : Set X :=
  ReferenceOriginalCalendarCollectionRetainedEnergyStep.G
    rate rewards C_star C_h q

/-- The fixed-ID cylinder is predictable in the accepted pre-assignment field. -/
public theorem measurableSet_fixedIDSourceSection_prefix :
    MeasurableSet[F] D :=
  ReferenceFirstCollectionPrecallFixedIDMean.measurableSet_fixedIDSourceSection_prefix
    control0 ids q.val

private theorem local_condExp_le {A : Set X}
    (hA : MeasurableSet[F] A) {f g : X → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : μ[f | F] ≤ᵐ[μ] g) :
    (∫ x in A, f x ∂μ) ≤ ∫ x in A, g x ∂μ := by
  calc
    (∫ x in A, f x ∂μ) = ∫ x in A, μ[f | F] x ∂μ :=
      (setIntegral_condExp
        ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
          (q.val + 1)) hf hA).symm
    _ ≤ ∫ x in A, g x ∂μ := by
      apply integral_mono_ae integrable_condExp.integrableOn hg.integrableOn
      exact ae_restrict_of_ae hfg

/-- A bounded predictable full-prefix weight turns a branchwise conditional
first-moment bound into a fixed-ID set-integral estimate. -/
private theorem weightedArrival_fixedID_bound (A G : Set X)
    (hA : MeasurableSet[F] A) (hAambient : MeasurableSet A) (hAG : A ⊆ G)
    (raw : Fin p.K → X → ℝ)
    (hraw : ∀ i : Fin p.K, Integrable (raw i) μ)
    (hmean : ∀ i : Fin p.K, ∀ᵐ z ∂μ, z ∈ G →
      μ[raw i | F] z ≤ 1)
    (hpast : ∀ z ∈ G, ∃ past, PI q.val z = some past) :
    Integrable ((A).indicator (fun z => ∑ i : Fin p.K,
      ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
        rate rewards C_star C_h q.val i z * raw i z)) μ ∧
    (∫ z in A, ∑ i : Fin p.K,
      ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
        rate rewards C_star C_h q.val i z * raw i z ∂μ) ≤
      (p.m : ℝ) * (μ).real A := by
  have hF := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (q.val + 1)
  have ht i := ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt_measurable
    rate rewards C_star C_h control0 q i
  have hb i z : ‖θ q.val i z‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt_bounds
      rate rewards C_star C_h q.val i z).1]
    exact (ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt_bounds
      rate rewards C_star C_h q.val i z).2
  have hprod (i : Fin p.K) (f : X → ℝ) (hf : Integrable f μ) :
      Integrable (fun z => θ q.val i z * f z) μ :=
    hf.bdd_mul ((ht i).mono hF le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall (hb i))
  have hi := integrable_finsetSum Finset.univ (fun i _ => hprod i _ (hraw i))
  have hci := integrable_finsetSum Finset.univ (fun i _ =>
    hprod i _ (integrable_condExp (f := raw i) (m := F)))
  have hterm i : (∫ z in A, θ q.val i z * raw i z ∂μ) =
      ∫ z in A, θ q.val i z * μ[raw i | F] z ∂μ := by
    rw [← setIntegral_condExp hF (hprod i _ (hraw i)) hA]
    exact integral_congr_ae (ae_restrict_of_ae
      (condExp_mul_of_aestronglyMeasurable_left (ht i).aestronglyMeasurable
        (hprod i _ (hraw i)) (hraw i)))
  refine ⟨hi.indicator hAambient, ?_⟩
  calc
    _ = ∫ z in A, ∑ i : Fin p.K, θ q.val i z * μ[raw i | F] z ∂μ := by
      rw [integral_finsetSum _ (fun i _ => (hprod i _ (hraw i)).integrableOn),
        integral_finsetSum _ (fun i _ => (hprod i _ integrable_condExp).integrableOn)]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ ≤ ∫ _z in A, (p.m : ℝ) ∂μ := by
      apply integral_mono_ae hci.integrableOn (integrable_const _)
      filter_upwards [ae_restrict_mem hAambient,
        ae_restrict_of_ae (Filter.eventually_all.mpr hmean)] with z hz hm
      obtain ⟨past, hp⟩ := hpast z (hAG hz)
      calc
        _ ≤ ∑ i : Fin p.K, θ q.val i z := Finset.sum_le_sum fun i _ => by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (hm i (hAG hz))
            (ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt_bounds
              rate rewards C_star C_h q.val i z).1
        _ = (p.m : ℝ) := by
          simp only [ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt, hp, Option.elim_some]
          exact RecordedMarginalGrowth.state_sum_theta_eq_m Q (RecordedQueueRun.run Q past)
            (Nat.zero_lt_of_lt p.two_le_m) p.m_lt_K
    _ = (p.m : ℝ) * (μ).real A := by simp only [integral_const, smul_eq_mul,
        measureReal_restrict_apply_univ]; ring

private def stateFromReadout
    (r : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K) :
    RecordedQueueRun.RunState p.K :=
  { registers := r.1, overflow := r.2.1, records := r.2.2 }

private theorem stateFromReadout_stateReadout
    (state : RecordedQueueRun.RunState p.K) :
    stateFromReadout (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      state) = state := by
  cases state
  rfl

private theorem C_measurable : Measurable[F] (C q.val) := by
  let obs : Option (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K) → ℝ :=
    fun o => o.elim 0 (fun r => RecordedWeightedDrift.weightedBacklog p.m Q
      (stateFromReadout r))
  have hstate : Measurable (fun r : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K =>
      RecordedWeightedDrift.weightedBacklog p.m Q (stateFromReadout r)) := by
    unfold RecordedWeightedDrift.weightedBacklog stateFromReadout
      RecordedQueueRun.scoreWeight ProductSetLaw.theta FiniteNormalization.mass
      FiniteNormalization.normalizedWeight FiniteNormalization.totalMass
      ProductSetLaw.setWeight ProductSetLaw.support ScoreWeights.scoreWeight
      StoppedQueueBound.normalizedBacklog
    fun_prop
  have hobs : Measurable obs := by
    convert (hstate.sumElim measurable_const).comp
      (comap_measurable (Equiv.optionEquivSumPUnit
        (ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K))) using 1
    funext o
    cases o <;> rfl
  have hp := ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.P_measurable
    rate rewards C_star C_h control0 q
  have heq : C q.val = obs ∘
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h q.val := by
    funext z
    cases h : PI q.val z with
    | none => simp [ReferenceOriginalCalendarLiveCollectionWeightedDrift.C, obs, h,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout]
    | some past =>
        simp only [ReferenceOriginalCalendarLiveCollectionWeightedDrift.C,
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
          h, Option.map_some, obs, Option.elim_some, Function.comp_apply]
        exact congrArg (RecordedWeightedDrift.weightedBacklog p.m Q)
          (stateFromReadout_stateReadout (RecordedQueueRun.run Q past))
  rw [heq]
  exact hobs.comp hp

private theorem C_bounds (z : X) :
    0 ≤ C q.val z ∧ C q.val z ≤ (p.m : ℝ) * (2 * (1 / (32 * rate.eta.val))) := by
  cases hpast : PI q.val z with
  | none =>
    simp only [ReferenceOriginalCalendarLiveCollectionWeightedDrift.C, hpast, Option.elim_none]
    exact ⟨le_rfl, by positivity [rate.eta.property]⟩
  | some past =>
    let b := StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q past)
    let w := ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q past))
    have hread : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h q.val z = some
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (RecordedQueueRun.run Q past)) := by
      simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hpast, Option.map_some]
    have hb i : 0 ≤ b i ∧ b i ≤ 2 * (1 / (32 * rate.eta.val)) := by
      simpa only [b, StoppedQueueBound.normalizedBacklog,
        ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout] using
        ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.prefixReadout_backlog_bounds
          rate rewards C_star C_h q.val z _ hread i
    have hw i : 0 ≤ w i ∧ w i ≤ 1 := by
      simpa [w, ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt, hpast] using
        ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt_bounds rate rewards C_star C_h q.val i z
    have hs : (∑ i : Fin p.K, w i) = (p.m : ℝ) :=
      RecordedMarginalGrowth.state_sum_theta_eq_m Q (RecordedQueueRun.run Q past)
        (Nat.zero_lt_of_lt p.two_le_m) p.m_lt_K
    simp only [ReferenceOriginalCalendarLiveCollectionWeightedDrift.C, hpast, Option.elim_some,
      RecordedWeightedDrift.weightedBacklog]
    change 0 ≤ ∑ i : Fin p.K, w i * b i ∧ _
    refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).1 (hb i).1), ?_⟩
    calc
      _ ≤ ∑ i : Fin p.K, w i * (2 * (1 / (32 * rate.eta.val))) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hb i).2 (hw i).1
      _ = _ := by rw [← Finset.sum_mul, hs]

include control0 in
private theorem C_integrable : Integrable (C q.val) μ := by
  let bound := (p.m : ℝ) * (2 * (1 / (32 * rate.eta.val)))
  have hconst : Integrable (fun _ : X => bound) μ := integrable_const bound
  apply hconst.mono'
    ((C_measurable rate rewards C_star C_h control0 q).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
        (q.val + 1)) le_rfl).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (C_bounds rate rewards C_star C_h q z).1]
  exact (C_bounds rate rewards C_star C_h q z).2

private theorem actual_active_rate_sum_le (t : Fin p.T) (z : X)
    (past : List (RecordedQueueRun.RoundInput p.K))
    (hpast : PI t.val z = some past)
    (c : RecordedQueueRun.RoundInput p.K)
    (hcell : ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
      rate rewards C_star C_h t z = some c)
    (hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h t z) :
    (∑ i : Fin p.K,
      ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
        rate rewards C_star C_h t.val i z / c.rate i) ≤ CanonicalRecordingRates.R p := by
  obtain ⟨o, c', hread, hcell', hclear, henabled⟩ := hactive
  have hcc : c' = c := Option.some.inj (hcell'.symm.trans hcell)
  subst c'
  have hrunRead :
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h t.val z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q past)) := by
    simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hpast, Option.map_some]
  have hreadEq : o =
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run Q past) :=
    Option.some.inj (hread.symm.trans hrunRead)
  have hstop : (RecordedQueueRun.run Q past).overflow = false := by
    rw [hreadEq] at hclear
    exact hclear
  have hcell' : ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
      rate rewards C_star C_h t z = some c := hcell
  change (ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z).bind
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some c at hcell'
  obtain ⟨record, hrecord, hcell0⟩ := Option.bind_eq_some_iff.mp hcell'
  have hfeas :=
    ReferenceCompleteOriginalCalendarRateFeasibility.actual_original_calendar_rate_feasibility
      rate rewards C_star C_h z t
  simp only [hpast, hrecord, hcell0] at hfeas
  have hbound := hfeas henabled hstop
  simpa only [ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt,
    hpast, Option.elim_some] using hbound

private theorem live_driftRHS_bound (z : X)
    (hz : z ∈ liveBranch rate rewards C_star C_h q) :
    ReferenceOriginalCalendarLiveCollectionWeightedDrift.liveDriftRHS
        rate rewards C_star C_h q z ≤
      -(11 / 2 : ℝ) * C q.val z +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) := by
  have hactive :=
    (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveGate_iff_activeUpdate
      rate rewards C_star C_h q z).mp hz
  obtain ⟨past, c, hpast, hcell, _hdelta⟩ :=
    ReferenceOriginalCalendarLiveCollectionWeightedDrift.live_deltaV_transition
      rate rewards C_star C_h q z hz
  obtain ⟨r, cDomain, _hrecord, _hread, _hcell0, hactualCell, _henable,
      hactualCellAt⟩ :=
    ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveDomain_cell0
      rate rewards C_star C_h q z hactive.1
  have hdomain : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q := by
    simpa [ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveDomain] using
      hactive.1
  have hdomainCell : cDomain = c :=
    Option.some.inj (hactualCellAt.symm.trans hcell)
  subst cDomain
  have hactual :=
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell_data
      rate rewards C_star C_h q z hdomain
  obtain ⟨_r', _regs, _owned, _base, c', _selected, _hr, _hcoord, _hlive,
      hactualCell', _hEnabled, _hselected, _hrate, _hreward, _hquantized⟩ := hactual
  have hcc : c' = c := Option.some.inj (hactualCell'.symm.trans hactualCell)
  subst c'
  have hrate (i : Fin p.K) :
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate
        rate rewards C_star C_h q i z = c.rate i := by
    simp [ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate,
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualParameters,
      hdomain, hactualCell']
  have hsum := actual_active_rate_sum_le rate rewards C_star C_h q
    z past hpast c hcell hactive.2
  change ReferenceOriginalCalendarLiveCollectionWeightedDrift.liveDriftRHS
      rate rewards C_star C_h q z ≤ _
  rw [ReferenceOriginalCalendarLiveCollectionWeightedDrift.liveDriftRHS]
  simp only [hrate]
  linarith [hsum]

private theorem collection_driftRHS_bound (z : X)
    (hz : z ∈ collectionBranch rate rewards C_star C_h q) :
    ReferenceOriginalCalendarLiveCollectionWeightedDrift.collectionDriftRHS
        rate rewards C_star C_h q z ≤
      -(11 / 2 : ℝ) * C q.val z +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) := by
  have hactiveSome := (ReferenceOriginalCalendarRetainedBranchPartition.activeCollectionSelector_iff_G
    rate rewards C_star C_h q (⟨0, by
      have hm : 0 < p.m := Nat.zero_lt_of_lt p.two_le_m
      exact Nat.lt_trans hm p.m_lt_K⟩ : Fin p.K) z).mpr hz
  obtain ⟨hactive, hsome⟩ := hactiveSome
  obtain ⟨data, hselector⟩ := Option.isSome_iff_exists.mp hsome
  rcases data with ⟨record, cp⟩
  rcases cp with ⟨c, payload⟩
  have hselectorCell := ReferenceOriginalCalendarRetainedBranchPartition.collectionSelector_eq_collectionRecorder
    rate rewards C_star C_h q z record c payload hselector
  have hbranch := ReferenceOriginalCalendarRetainedBranchPartition.collectionBranch_matches_retainedStep
    rate rewards C_star C_h q (⟨0, by
      have hm : 0 < p.m := Nat.zero_lt_of_lt p.two_le_m
      exact Nat.lt_trans hm p.m_lt_K⟩ : Fin p.K) z record c payload hactive hselector
  have hpresent := ReferenceOriginalCalendarCollectionRetainedEnergyStep.presentCell_recordingMap
    rate rewards C_star C_h q z
    hz.1.1.1
  obtain ⟨record', c', payload', hrecord', hcell', hpayload', hrate', _⟩ := hpresent
  have hcc' : some c' = some c := by
    calc
      some c' = ReferenceOriginalCalendarCollectionRetainedEnergyStep.C
          rate rewards C_star C_h q z := hcell'.symm
      _ = some c := hselectorCell.1
  have hcc : c' = c := Option.some.inj hcc'
  subst c'
  have hpastCell :=
    ReferenceOriginalCalendarLiveCollectionWeightedDrift.collection_deltaV_transition
      rate rewards C_star C_h q z hbranch.1
  obtain ⟨past, oldCell, hpast, holdCell, _⟩ := hpastCell
  have holdCell' : ReferenceFirstCollectionOldRecorderFoundation.oldCell?
      rate rewards C_star C_h q z = some c := by
    simpa only [ReferenceOriginalCalendarCollectionRetainedEnergyStep.C] using hselectorCell.1
  have hold : oldCell = c := Option.some.inj (holdCell.symm.trans holdCell')
  subst oldCell
  have hsum := actual_active_rate_sum_le rate rewards C_star C_h q z past hpast c
    hselectorCell.2 hactive
  have hrateCell :
      ReferenceFirstCollectionOldRecorderFoundation.incomingRates?
        rate rewards C_star C_h q z = some c.rate := by
    rw [ReferenceFirstCollectionOldRecorderFoundation.incomingRates?, hpayload']
    simp only [Option.map_some, hrate']
  rw [ReferenceOriginalCalendarLiveCollectionWeightedDrift.collectionDriftRHS]
  rw [hrateCell]
  simp only [Option.getD_some, div_eq_mul_inv]
  have hsum' : (∑ i : Fin p.K,
      ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
        rate rewards C_star C_h q.val i z / c.rate i) ≤ CanonicalRecordingRates.R p := by
    simpa only [ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt,
      hpast, Option.elim_some] using hsum
  have hsum'' : (∑ i : Fin p.K,
      ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
        rate rewards C_star C_h q.val i z * (c.rate i)⁻¹) ≤ CanonicalRecordingRates.R p := by
    simpa only [div_eq_mul_inv] using hsum'
  linarith

private theorem acceptedRecord_arrival_eq_quantized
    (past : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hclear : (RecordedQueueRun.run Q past).overflow = false)
    (henabled : c.enabled = true) (i : Fin p.K) :
    RecordedQueueRun.acceptedArrival
        (RecordedQueueRun.acceptedRecord Q (RecordedQueueRun.run Q past) c i) =
      RecordedQueueRun.quantizedArrival Q c i := by
  unfold RecordedQueueRun.acceptedArrival RecordedQueueRun.acceptedRecord
  have hnot : ¬ ((RecordedQueueRun.run Q past).overflow = true) := by simp [hclear]
  rw [ite_eq_right hnot]
  simp [henabled]

private theorem acceptedArrivalAt_eq_quantized (z : X) (c : RecordedQueueRun.RoundInput p.K)
    (hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt rate rewards C_star C_h q z)
    (hc : ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt rate rewards C_star C_h q z = some c)
    (i : Fin p.K) : acceptedArrivalAt rate rewards C_star C_h q i z =
      RecordedRoundMoments.normalizedQuantizedArrival Q c i := by
  obtain ⟨o, c', hread, hc', hclear, he⟩ := hactive
  have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  cases hp : PI q.val z with
  | none => simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hp] at hread
  | some past =>
    have ho : o = ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run Q past) := by
      simpa [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hp] using hread.symm
    subst o
    simp only [acceptedArrivalAt, hp, hc]
    rw [acceptedRecord_arrival_eq_quantized rate past c hclear he i]
    rfl

private theorem acceptedArrival_eq_oldRaw_collection (z : X)
    (hz : z ∈ collectionBranch rate rewards C_star C_h q) (i : Fin p.K) :
    acceptedArrivalAt rate rewards C_star C_h q i z =
      ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q i z := by
  obtain ⟨hactive, hs⟩ := (ReferenceOriginalCalendarRetainedBranchPartition.activeCollectionSelector_iff_G
    rate rewards C_star C_h q ⟨0, by have := p.two_le_m; have := p.m_lt_K; omega⟩ z).mpr hz
  obtain ⟨⟨r, c, payload⟩, hs⟩ := Option.isSome_iff_exists.mp hs
  have hc := ReferenceOriginalCalendarRetainedBranchPartition.collectionSelector_eq_collectionRecorder
    rate rewards C_star C_h q z r c payload hs
  rw [acceptedArrivalAt_eq_quantized rate rewards C_star C_h q z c hactive hc.2 i]
  simp only [ReferenceFirstCollectionOldRecorderFoundation.oldRaw,
    show ReferenceFirstCollectionOldRecorderFoundation.oldCell? rate rewards C_star C_h q z = some c from hc.1]

private theorem acceptedArrival_eq_actualArrival_live (z : X)
    (hz : z ∈ liveBranch rate rewards C_star C_h q) (i : Fin p.K) :
    acceptedArrivalAt rate rewards C_star C_h q i z =
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival rate rewards C_star C_h q i z := by
  obtain ⟨r, c, _, _, _, hc, _, hcell⟩ :=
    ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveDomain_cell0 rate rewards C_star C_h q z hz.1.1
  have hactive := ((ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveGate_iff_activeUpdate
    rate rewards C_star C_h q z).mp hz).2
  have hd : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q := by
    simpa [ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveDomain] using hz.1.1
  rw [acceptedArrivalAt_eq_quantized rate rewards C_star C_h q z c hactive hcell i]
  simp [ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival, hd, hc,
    RecordedRoundMoments.normalizedQuantizedArrival, ReferenceFirstLaunchNumericalCell.queueParameters]

include control0 in
/-- The accepted collection arrival estimate is localized to this fixed-ID
section on the unrestricted present collection/cutoff branch. -/
public theorem collection_weightedArrival_fixedID :
    Integrable ((D ∩ collectionBranch rate rewards C_star C_h q).indicator
      (weightedAcceptedArrival rate rewards C_star C_h q)) μ ∧
    (∫ z in D ∩ collectionBranch rate rewards C_star C_h q,
      weightedAcceptedArrival rate rewards C_star C_h q z ∂μ) ≤
      (p.m : ℝ) * (μ).real (D ∩ collectionBranch rate rewards C_star C_h q) := by
  let G := collectionBranch rate rewards C_star C_h q
  let A := D ∩ G
  have hA := (measurableSet_fixedIDSourceSection_prefix control0 ids q).inter
    ((ReferenceOriginalCalendarCollectionRetainedEnergyStep.measurableSet_G
      rate rewards C_star C_h control0 q))
  have hFle :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (q.val + 1)
  have hGambient := hFle _
    (ReferenceOriginalCalendarCollectionRetainedEnergyStep.measurableSet_G
      rate rewards C_star C_h control0 q)
  have hAambient := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).inter
    hGambient
  have hlocal := weightedArrival_fixedID_bound rate rewards C_star C_h control0 q
    A G hA hAambient Set.inter_subset_right
    (ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q)
    (fun i => ReferenceFirstCollectionOldRecorderFoundation.oldRaw_integrable
      rate rewards C_star C_h q i)
    (fun i => ReferenceOriginalCalendarLiveCollectionWeightedDrift.collection_oldRaw_condExp_upper_on_G
      rate rewards C_star C_h control0 q i)
    (fun z hz => by
      obtain ⟨past, _, hpast, _⟩ :=
        ReferenceOriginalCalendarLiveCollectionWeightedDrift.collection_deltaV_transition
          rate rewards C_star C_h q z hz
      exact ⟨past, hpast⟩)
  have heq : (A).indicator (weightedAcceptedArrival rate rewards C_star C_h q) =
      (A).indicator (fun z => ∑ i : Fin p.K,
        ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
          rate rewards C_star C_h q.val i z *
        ReferenceFirstCollectionOldRecorderFoundation.oldRaw
          rate rewards C_star C_h q i z) := by
    funext z
    by_cases hz : z ∈ A
    · simp only [Set.indicator_of_mem hz, weightedAcceptedArrival]
      congr 1
      funext i
      rw [acceptedArrival_eq_oldRaw_collection rate rewards C_star C_h q z hz.2 i]
    · simp [Set.indicator_of_notMem hz]
  refine ⟨?_, ?_⟩
  · exact hlocal.1.congr
      (Filter.Eventually.of_forall fun z => (congrFun heq z).symm)
  · calc
      (∫ z in A, weightedAcceptedArrival rate rewards C_star C_h q z ∂μ) =
          ∫ z in A, ∑ i : Fin p.K,
            ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
              rate rewards C_star C_h q.val i z *
            ReferenceFirstCollectionOldRecorderFoundation.oldRaw
              rate rewards C_star C_h q i z ∂μ := by
        apply setIntegral_congr_fun hAambient
        intro z hz
        unfold weightedAcceptedArrival
        apply Finset.sum_congr rfl
        intro i hi
        rw [acceptedArrival_eq_oldRaw_collection rate rewards C_star C_h q z hz.2 i]
      _ ≤ (p.m : ℝ) * (μ).real A := hlocal.2

include control0 in
/-- The actual LIVE accepted arrivals have conditional total at most `m`
inside every original fixed-ID section. -/
public theorem live_weightedArrival_fixedID :
    Integrable ((D ∩ liveBranch rate rewards C_star C_h q).indicator
      (weightedAcceptedArrival rate rewards C_star C_h q)) μ ∧
    (∫ z in D ∩ liveBranch rate rewards C_star C_h q,
      weightedAcceptedArrival rate rewards C_star C_h q z ∂μ) ≤
      (p.m : ℝ) * (μ).real (D ∩ liveBranch rate rewards C_star C_h q) := by
  let G := liveBranch rate rewards C_star C_h q
  let A := D ∩ G
  have hA := (measurableSet_fixedIDSourceSection_prefix control0 ids q).inter
    (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.measurableSet_liveRetainedGate
      rate rewards C_star C_h control0 q)
  have hFle :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (q.val + 1)
  have hGambient := hFle _
    (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.measurableSet_liveRetainedGate
      rate rewards C_star C_h control0 q)
  have hAambient := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).inter
    hGambient
  have hlocal := weightedArrival_fixedID_bound rate rewards C_star C_h control0 q
    A G hA hAambient Set.inter_subset_right
    (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
      rate rewards C_star C_h q)
    (fun i => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival_integrable
      rate rewards C_star C_h control0 q i)
    (fun i => by
      filter_upwards [ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival_condExp_bounds
        rate rewards C_star C_h control0 q i] with z hm
      intro hz
      have hdomain : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
          rate rewards C_star C_h q := by
        simpa [ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveDomain] using
          hz.1.1
      exact (hm hdomain).2.trans
        (ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds rewards q i).2)
    (fun z hz => by
      obtain ⟨past, _, hpast, _⟩ :=
        ReferenceOriginalCalendarLiveCollectionWeightedDrift.live_deltaV_transition
          rate rewards C_star C_h q z hz
      exact ⟨past, hpast⟩)
  have heq : (A).indicator (weightedAcceptedArrival rate rewards C_star C_h q) =
      (A).indicator (fun z => ∑ i : Fin p.K,
        ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
          rate rewards C_star C_h q.val i z *
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
          rate rewards C_star C_h q i z) := by
    funext z
    by_cases hz : z ∈ A
    · simp only [Set.indicator_of_mem hz, weightedAcceptedArrival]
      congr 1
      funext i
      rw [acceptedArrival_eq_actualArrival_live rate rewards C_star C_h q z hz.2 i]
    · simp [Set.indicator_of_notMem hz]
  refine ⟨?_, ?_⟩
  · exact hlocal.1.congr
      (Filter.Eventually.of_forall fun z => (congrFun heq z).symm)
  · calc
      (∫ z in A, weightedAcceptedArrival rate rewards C_star C_h q z ∂μ) =
          ∫ z in A, ∑ i : Fin p.K,
            ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
              rate rewards C_star C_h q.val i z *
            ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
              rate rewards C_star C_h q i z ∂μ := by
        apply setIntegral_congr_fun hAambient
        intro z hz
        unfold weightedAcceptedArrival
        apply Finset.sum_congr rfl
        intro i hi
        rw [acceptedArrival_eq_actualArrival_live rate rewards C_star C_h q z hz.2 i]
      _ ≤ (p.m : ℝ) * (μ).real A := hlocal.2

private theorem predictable_drift_fixedID (G : Set X) (rhs : X → ℝ)
    (hG : MeasurableSet[F] G)
    (hΔ : Integrable (G.indicator (ΔV q)) μ)
    (hrhs : Integrable (G.indicator rhs) μ)
    (hcond : μ[G.indicator (ΔV q) | F] ≤ᵐ[μ] G.indicator rhs)
    (hbound : ∀ z ∈ G, rhs z ≤ -(11 / 2 : ℝ) * C q.val z +
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m)) :
    Integrable ((D ∩ G).indicator (ΔV q)) μ ∧
    Integrable ((D ∩ G).indicator (C q.val)) μ ∧
    (∫ z in D ∩ G, ΔV q z ∂μ) ≤
      -(11 / 2 : ℝ) * (∫ z in D ∩ G, C q.val z ∂μ) +
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) * (μ).real (D ∩ G) := by
  let c := CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m
  have hD := ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hGa := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
    (q.val + 1) _ hG
  have hC := C_integrable rate rewards C_star C_h control0 q
  have hc : Integrable (G.indicator (fun _ : X => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hGa
  have hCg := hC.indicator hGa
  have hsplit : G.indicator (fun z => -(11 / 2 : ℝ) * C q.val z + c) =
      (fun z => -(11 / 2 : ℝ) * G.indicator (C q.val) z +
        c * G.indicator (fun _ : X => (1 : ℝ)) z) := by
    funext z
    by_cases hz : z ∈ G <;> simp [Set.indicator, hz]
  have hbint : Integrable (G.indicator
      (fun z => -(11 / 2 : ℝ) * C q.val z + c)) μ := by
    rw [hsplit]
    exact (hCg.const_mul _).add (hc.const_mul c)
  refine ⟨?_, hC.indicator (hD.inter hGa), ?_⟩
  · simpa only [Set.indicator_indicator] using hΔ.indicator hD
  · have hloc := local_condExp_le control0 q
      (measurableSet_fixedIDSourceSection_prefix control0 ids q) hΔ hrhs hcond
    have hmono : (∫ z in D, G.indicator rhs z ∂μ) ≤
        ∫ z in D, G.indicator
          (fun z => -(11 / 2 : ℝ) * C q.val z + c) z ∂μ := by
      apply integral_mono_ae hrhs.integrableOn hbint.integrableOn
      apply ae_of_all
      intro z
      by_cases hz : z ∈ G
      · simpa only [Set.indicator_of_mem hz] using hbound z hz
      · simp only [Set.indicator_of_notMem hz, le_refl]
    have hle := hloc.trans hmono
    rw [hsplit, integral_add (hCg.const_mul _).integrableOn
      (hc.const_mul c).integrableOn, integral_const_mul, integral_const_mul,
      setIntegral_indicator hGa, setIntegral_indicator hGa,
      setIntegral_indicator hGa] at hle
    simpa only [integral_const, smul_eq_mul, mul_one,
      measureReal_restrict_apply_univ] using hle

include control0 in
/-- Conditional LIVE drift localized on the original fixed-ID section before
integration. The same retained gate supplies the actual-cell feasibility bound. -/
public theorem live_retained_weightedSquare_fixedID :
    Integrable ((D ∩ liveBranch rate rewards C_star C_h q).indicator
      (ΔV q)) μ ∧
    Integrable ((D ∩ liveBranch rate rewards C_star C_h q).indicator
      (C q.val)) μ ∧
    (∫ z in D ∩ liveBranch rate rewards C_star C_h q,
      ΔV q z ∂μ) ≤
      -(11 / 2 : ℝ) *
        (∫ z in D ∩ liveBranch rate rewards C_star C_h q,
          C q.val z ∂μ) +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) *
          (μ).real (D ∩ liveBranch rate rewards C_star C_h q) := by
  obtain ⟨hΔ, hrhs, hcond, _⟩ :=
    ReferenceOriginalCalendarLiveCollectionWeightedDrift.live_retained_weightedSquare_drift
      rate rewards C_star C_h control0 q
  exact predictable_drift_fixedID rate rewards C_star C_h control0 ids q
    (liveBranch rate rewards C_star C_h q) _
    (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.measurableSet_liveRetainedGate
      rate rewards C_star C_h control0 q) hΔ hrhs hcond
    (fun z hz => live_driftRHS_bound rate rewards C_star C_h q z hz)

include control0 in
/-- Conditional unrestricted collection drift localized to the fixed-ID
section on its literal actual collection/cutoff selector. -/
public theorem collection_retained_weightedSquare_fixedID :
    Integrable ((D ∩ collectionBranch rate rewards C_star C_h q).indicator
      (ΔV q)) μ ∧
    Integrable ((D ∩ collectionBranch rate rewards C_star C_h q).indicator
      (C q.val)) μ ∧
    (∫ z in D ∩ collectionBranch rate rewards C_star C_h q,
      ΔV q z ∂μ) ≤
      -(11 / 2 : ℝ) *
        (∫ z in D ∩ collectionBranch rate rewards C_star C_h q,
          C q.val z ∂μ) +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) *
          (μ).real (D ∩ collectionBranch rate rewards C_star C_h q) := by
  obtain ⟨hΔ, hrhs, hcond, _⟩ :=
    ReferenceOriginalCalendarLiveCollectionWeightedDrift.collection_retained_weightedSquare_drift
      rate rewards C_star C_h control0 q
  exact predictable_drift_fixedID rate rewards C_star C_h control0 ids q
    (collectionBranch rate rewards C_star C_h q) _
    (ReferenceOriginalCalendarCollectionRetainedEnergyStep.measurableSet_G
      rate rewards C_star C_h control0 q) hΔ hrhs hcond
    (fun z hz => collection_driftRHS_bound rate rewards C_star C_h q z hz)

private theorem birth_observations (z : X)
    (hz : z ∈ renewedBirthBranch rate rewards C_star C_h q) :
    ∃ past c, PI q.val z = some past ∧
      ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
        rate rewards C_star C_h q z = some c ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h q z = some c ∧
      (RecordedQueueRun.run Q past).overflow = false ∧ c.enabled = true := by
  have hs := hz
  rw [renewedBirthBranch,
    ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet_eq_sourceEvent]
    at hs
  obtain ⟨past, c, hpast, _, hc, he, hclear, _⟩ :=
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirth_prefix_energy_step
      rate rewards C_star C_h q z hs.1.1 hs.2
  have hc' := hc
  unfold ReferenceFirstCollectionCurrentNumericalCell.currentCell at hc'
  obtain ⟨r, hr, hread⟩ := Option.bind_eq_some_iff.mp hc'
  obtain ⟨selected, ho, hselected, hstrict, hlive, hsource⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some _ r c hread
  have hzero : 0 < selected.view.payload.sigma.val := by omega
  have hread0 : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
    simp only [ReferenceLaterLiveNumericalReadout.laterLiveReadout, hselected,
      hzero, hlive, and_self, ite_true, dite_eq_left ho]
    rw [hsource]
  refine ⟨past, c, hpast, ?_, hc, hclear.mp hs.1.2, he⟩
  change (ReferenceSourcePrefixHistoryFiltration.actualRecord
    rate rewards C_star C_h q z).bind
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some c
  simp only [hr, Option.bind_some, ReferenceFirstCollectionCurrentRetainedGate.cell0, hread0]
  rfl

private theorem acceptedArrival_eq_currentRaw_birth (z : X)
    (hz : z ∈ renewedBirthBranch rate rewards C_star C_h q) (i : Fin p.K) :
    acceptedArrivalAt rate rewards C_star C_h q i z =
      ReferenceFirstCollectionCurrentRawMoments.currentRaw rate rewards C_star C_h q i z := by
  obtain ⟨past, c, hpast, hc, hcurrent, hclear, he⟩ :=
    birth_observations rate rewards C_star C_h q z hz
  simp only [acceptedArrivalAt, hpast, hc,
    ReferenceFirstCollectionCurrentRawMoments.currentRaw, hcurrent]
  rw [acceptedRecord_arrival_eq_quantized rate past c hclear he i]
  rfl

include control0 in
private theorem measurableSet_renewedBirthBranch :
    MeasurableSet (renewedBirthBranch rate rewards C_star C_h q) := by
  rw [renewedBirthBranch,
    ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet_eq_sourceEvent]
  have hle := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
    (q.val + 1)
  refine ((hle _ (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet_measurable
    rate rewards C_star C_h control0 q)).inter
    (hle _ (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
      rate rewards C_star C_h control0 q))).inter ?_
  change MeasurableSet ((ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker
    rate rewards C_star C_h q) ⁻¹' {o | o.isSome = true})
  exact (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker_measurable
    rate rewards C_star C_h q) (by simp)

include control0 in
/-- The whole-vector birth success remains inside conditional expectation;
the original fixed-ID section is imposed before integration. -/
public theorem renewedBirth_weightedArrival_fixedID :
    Integrable ((D ∩ renewedBirthBranch rate rewards C_star C_h q).indicator
      (weightedAcceptedArrival rate rewards C_star C_h q)) μ ∧
    (∫ z in D ∩ renewedBirthBranch rate rewards C_star C_h q,
      weightedAcceptedArrival rate rewards C_star C_h q z ∂μ) ≤
      (p.m : ℝ) * (μ).real (D ∩ renewedBirthBranch rate rewards C_star C_h q) := by
  let A := renewedBirthBranch rate rewards C_star C_h q
  let W := ReferenceOriginalCalendarLaterBirthWeightedDrift.actualRetainedLaterBirthWeightedArrival
    rate rewards C_star C_h q
  let mass := (A).indicator (fun _ : X => (1 : ℝ))
  have hA := measurableSet_renewedBirthBranch rate rewards C_star C_h control0 q
  have hD := ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hevent : ReferenceOriginalCalendarLaterBirthWeightedDrift.actualRetainedLaterBirthEvent
      rate rewards C_star C_h q = A := by
    exact (ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet_eq_sourceEvent
      rate rewards C_star C_h q).symm
  have hW : W = (A).indicator (weightedAcceptedArrival rate rewards C_star C_h q) := by
    funext z
    dsimp only [W, ReferenceOriginalCalendarLaterBirthWeightedDrift.actualRetainedLaterBirthWeightedArrival]
    rw [hevent]
    by_cases hz : z ∈ A
    · simp only [Set.indicator_of_mem hz, weightedAcceptedArrival]
      apply Finset.sum_congr rfl
      intro i _
      rw [acceptedArrival_eq_currentRaw_birth rate rewards C_star C_h q z hz i]
      congr 1
      cases hp : PI q.val z <;>
        simp [ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt,
          ReferenceOriginalCalendarLaterBirthWeightedDrift.originalPrefixTheta, hp]
    · simp only [Set.indicator_of_notMem hz]
  have hw := ReferenceOriginalCalendarLaterBirthWeightedDrift.originalLaterBirth_weightedArrival_condExp
    rate rewards C_star C_h control0 q
  change Integrable W μ ∧
    (∀ᵐ z ∂μ, μ[W | F] z ≤ (p.m : ℝ) *
      μ[(ReferenceOriginalCalendarLaterBirthWeightedDrift.actualRetainedLaterBirthEvent
        rate rewards C_star C_h q).indicator (fun _ => (1 : ℝ)) | F] z) at hw
  rw [hevent] at hw
  have hm : Integrable mass μ := (integrable_const (1 : ℝ)).indicator hA
  have hle := local_condExp_le control0 q
    (measurableSet_fixedIDSourceSection_prefix control0 ids q) hw.1
    ((integrable_condExp (f := mass)).const_mul (p.m : ℝ)) hw.2
  have hmass : (∫ z in D, μ[mass | F] z ∂μ) = (μ).real (D ∩ A) := by
    rw [setIntegral_condExp
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (q.val + 1))
      hm (measurableSet_fixedIDSourceSection_prefix control0 ids q), setIntegral_indicator hA]
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ]
    rfl
  constructor
  · rw [hW] at hw
    have heq : (D ∩ A).indicator (weightedAcceptedArrival rate rewards C_star C_h q) =
        (D).indicator ((A).indicator (weightedAcceptedArrival rate rewards C_star C_h q)) := by
      funext z
      by_cases hd : z ∈ D <;> by_cases ha : z ∈ A <;> simp [Set.indicator, hd, ha]
    rw [heq]
    exact hw.1.indicator hD
  · calc
      _ = ∫ z in D, W z ∂μ := by rw [hW, setIntegral_indicator hA]
      _ ≤ (p.m : ℝ) * (∫ z in D, μ[mass | F] z ∂μ) := by
        simpa only [integral_const_mul] using hle
      _ = _ := by rw [hmass]

private theorem signed_fixedID_of_moments (B : Set X) (hB : MeasurableSet B)
    (raw floor : Fin p.K → X → ℝ)
    (ha : ∀ i, Integrable (B.indicator (raw i)) μ)
    (he : ∀ i, Integrable (B.indicator (floor i)) μ)
    (hlo : ∀ i, ∀ᵐ z ∂μ,
      μ[B.indicator (fun _ => roundedRewardAt rewards q i) | F] z ≤
        μ[B.indicator (raw i) | F] z + μ[B.indicator (floor i) | F] z)
    (hup : ∀ i, ∀ᵐ z ∂μ, μ[B.indicator (raw i) | F] z ≤
      μ[B.indicator (fun _ => roundedRewardAt rewards q i) | F] z)
    (hactive : ∀ z ∈ B, ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z)
    (hraw : ∀ z ∈ B, ∀ i, acceptedArrivalAt rate rewards C_star C_h q i z = raw i z)
    (hfloor : ∀ z ∈ B,
      (match ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
        rate rewards C_star C_h q z with
      | none => 0 | some c => ∑ i ∈ S.1, c.rate i / (rate.n : ℝ)) =
        ∑ i ∈ S.1, floor i z) :
    Integrable ((D ∩ B).indicator (acceptedArrivalComparatorGap rate rewards C_star C_h S q)) μ ∧
    Integrable ((D ∩ B).indicator (retainedRewardGap rate rewards C_star C_h S q)) μ ∧
    Integrable ((D ∩ B).indicator (retainedRateFloor rate rewards C_star C_h S q)) μ ∧
    (∫ z in D ∩ B, retainedRewardGap rate rewards C_star C_h S q z ∂μ) ≤
      (∫ z in D ∩ B, acceptedArrivalComparatorGap rate rewards C_star C_h S q z ∂μ) +
      (∫ z in D ∩ B, retainedRateFloor rate rewards C_star C_h S q z ∂μ) := by
  let a := fun i => B.indicator (raw i)
  let r := fun i => B.indicator (fun _ : X => roundedRewardAt rewards q i)
  let e := fun i => B.indicator (floor i)
  have hr i : Integrable (r i) μ := (integrable_const _).indicator hB
  have hFle := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (q.val + 1)
  have ht i := ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt_measurable
    rate rewards C_star C_h control0 q i
  have hb i z : ‖θ q.val i z‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt_bounds
      rate rewards C_star C_h q.val i z).1]
    exact (ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt_bounds
      rate rewards C_star C_h q.val i z).2
  have hprod (i : Fin p.K) (f : X → ℝ) (hf : Integrable f μ) :
      Integrable (fun z => θ q.val i z * f z) μ :=
    hf.bdd_mul ((ht i).mono hFle le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall (hb i))
  have hweight (i : Fin p.K) (f : X → ℝ) (hf : Integrable f μ) :
      (∫ z in D, θ q.val i z * f z ∂μ) =
        ∫ z in D, θ q.val i z * μ[f | F] z ∂μ := by
    rw [← setIntegral_condExp hFle (hprod i f hf)
      (measurableSet_fixedIDSourceSection_prefix control0 ids q)]
    apply integral_congr_ae
    exact ae_restrict_of_ae (condExp_mul_of_aestronglyMeasurable_left
      (ht i).aestronglyMeasurable (hprod i f hf) hf)
  have low i : (∫ z in D, r i z ∂μ) ≤
      (∫ z in D, a i z ∂μ) + (∫ z in D, e i z ∂μ) := by
    have hh := local_condExp_le control0 q
      (measurableSet_fixedIDSourceSection_prefix control0 ids q) (hr i)
      ((integrable_condExp (f := a i)).add (integrable_condExp (f := e i))) (hlo i)
    change (∫ z in D, r i z ∂μ) ≤ ∫ z in D, μ[a i | F] z + μ[e i | F] z ∂μ at hh
    rw [integral_add integrable_condExp.integrableOn integrable_condExp.integrableOn,
      setIntegral_condExp hFle (ha i) (measurableSet_fixedIDSourceSection_prefix control0 ids q),
      setIntegral_condExp hFle (he i) (measurableSet_fixedIDSourceSection_prefix control0 ids q)] at hh
    exact hh
  have upper i : (∫ z in D, θ q.val i z * a i z ∂μ) ≤
      ∫ z in D, θ q.val i z * r i z ∂μ := by
    rw [hweight i (a i) (ha i), hweight i (r i) (hr i)]
    apply integral_mono_ae (hprod i _ integrable_condExp).integrableOn
      (hprod i _ integrable_condExp).integrableOn
    apply ae_restrict_of_ae
    filter_upwards [hup i] with z hz
    exact mul_le_mul_of_nonneg_left hz
      (ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt_bounds
        rate rewards C_star C_h q.val i z).1
  let g := fun z => (∑ i ∈ S.1, a i z) - ∑ i : Fin p.K, θ q.val i z * a i z
  let rGap := fun z => (∑ i ∈ S.1, r i z) - ∑ i : Fin p.K, θ q.val i z * r i z
  let f := fun z => ∑ i ∈ S.1, e i z
  have hg : Integrable g μ := (integrable_finsetSum _ (fun i _ => ha i)).sub
    (integrable_finsetSum _ (fun i _ => hprod i _ (ha i)))
  have hrGap : Integrable rGap μ := (integrable_finsetSum _ (fun i _ => hr i)).sub
    (integrable_finsetSum _ (fun i _ => hprod i _ (hr i)))
  have hf : Integrable f μ := integrable_finsetSum _ (fun i _ => he i)
  have hgEq : B.indicator (acceptedArrivalComparatorGap rate rewards C_star C_h S q) = g := by
    funext z
    by_cases hz : z ∈ B
    · simp only [Set.indicator_of_mem hz, acceptedArrivalComparatorGap,
        weightedAcceptedArrival, g, a, hraw z hz]
    · simp [Set.indicator_of_notMem hz, g, a]
  have hrEq : B.indicator (retainedRewardGap rate rewards C_star C_h S q) = rGap := by
    funext z
    by_cases hz : z ∈ B
    · have hzActive : z ∈ {z | ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
          rate rewards C_star C_h q z} := hactive z hz
      simp only [Set.indicator_of_mem hz, retainedRewardGap,
        Set.indicator_of_mem hzActive, rGap, r]
    · simp [Set.indicator_of_notMem hz, rGap, r]
  have hfEq : B.indicator (retainedRateFloor rate rewards C_star C_h S q) = f := by
    funext z
    by_cases hz : z ∈ B
    · have hzActive : z ∈ {z | ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
          rate rewards C_star C_h q z} := hactive z hz
      simp only [Set.indicator_of_mem hz, retainedRateFloor,
        Set.indicator_of_mem hzActive, hfloor z hz, f, e]
    · simp [Set.indicator_of_notMem hz, f, e]
  have hD := ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [← hgEq, Set.indicator_indicator] using hg.indicator hD
  · simpa only [← hrEq, Set.indicator_indicator] using hrGap.indicator hD
  · simpa only [← hfEq, Set.indicator_indicator] using hf.indicator hD
  · have hlow := Finset.sum_le_sum (s := S.1) (fun i _ => low i)
    have hupper := Finset.sum_le_sum (s := Finset.univ) (fun i _ => upper i)
    have htotal : (∫ z in D, rGap z ∂μ) ≤ (∫ z in D, g z ∂μ) + ∫ z in D, f z ∂μ := by
      dsimp only [rGap, g, f]
      rw [integral_sub (integrable_finsetSum _ (fun i _ => hr i)).integrableOn
        (integrable_finsetSum _ (fun i _ => hprod i _ (hr i))).integrableOn,
        integral_sub (integrable_finsetSum _ (fun i _ => ha i)).integrableOn
        (integrable_finsetSum _ (fun i _ => hprod i _ (ha i))).integrableOn,
        integral_finsetSum _ (fun i _ => (hr i).integrableOn),
        integral_finsetSum _ (fun i _ => (ha i).integrableOn),
        integral_finsetSum _ (fun i _ => (he i).integrableOn),
        integral_finsetSum _ (fun i _ => (hprod i _ (hr i)).integrableOn),
        integral_finsetSum _ (fun i _ => (hprod i _ (ha i)).integrableOn)]
      rw [Finset.sum_add_distrib] at hlow
      linarith
    rw [← hrEq, ← hgEq, ← hfEq, setIntegral_indicator hB,
      setIntegral_indicator hB, setIntegral_indicator hB] at htotal
    exact htotal

private theorem payload_rate_bounds (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin p.K) :
    0 ≤ payload.rate i ∧ payload.rate i ≤ 1 := by
  refine ⟨(CanonicalRecordingRates.xi_pos p rate.eta.property payload.anchor i).le, ?_⟩
  exact (Finset.single_le_sum (fun j _ =>
    (CanonicalRecordingRates.xi_pos p rate.eta.property payload.anchor j).le)
      (Finset.mem_univ i)).trans
    (CanonicalRecordingRates.sum_xi_le_one p rate.eta.property rate.sourceCap
      payload.anchor payload.anchor_pos)

private theorem signed_predictable_fixedID (B : Set X) (hB : MeasurableSet[F] B)
    (raw floor : Fin p.K → X → ℝ) (ha : ∀ i, Integrable (raw i) μ)
    (he : ∀ i, Integrable (floor i) μ) (hme : ∀ i, Measurable[F] (floor i))
    (hm : ∀ i, ∀ᵐ z ∂μ, z ∈ B →
      roundedRewardAt rewards q i - floor i z ≤ μ[raw i | F] z ∧
      μ[raw i | F] z ≤ roundedRewardAt rewards q i)
    (hactive : ∀ z ∈ B, ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z)
    (hraw : ∀ z ∈ B, ∀ i, acceptedArrivalAt rate rewards C_star C_h q i z = raw i z)
    (hfloor : ∀ z ∈ B,
      (match ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt rate rewards C_star C_h q z with
      | none => 0 | some c => ∑ i ∈ S.1, c.rate i / (rate.n : ℝ)) = ∑ i ∈ S.1, floor i z) :
    Integrable ((D ∩ B).indicator (acceptedArrivalComparatorGap rate rewards C_star C_h S q)) μ ∧
    Integrable ((D ∩ B).indicator (retainedRewardGap rate rewards C_star C_h S q)) μ ∧
    Integrable ((D ∩ B).indicator (retainedRateFloor rate rewards C_star C_h S q)) μ ∧
    (∫ z in D ∩ B, retainedRewardGap rate rewards C_star C_h S q z ∂μ) ≤
      (∫ z in D ∩ B, acceptedArrivalComparatorGap rate rewards C_star C_h S q z ∂μ) +
      (∫ z in D ∩ B, retainedRateFloor rate rewards C_star C_h S q z ∂μ) := by
  have hle := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (q.val + 1)
  have hBa := hle _ hB
  have hr i : μ[B.indicator (fun _ : X => roundedRewardAt rewards q i) | F] =
      B.indicator (fun _ : X => roundedRewardAt rewards q i) :=
    condExp_of_stronglyMeasurable hle (measurable_const.indicator hB).stronglyMeasurable
      ((integrable_const _).indicator hBa)
  have hf i : μ[B.indicator (floor i) | F] = B.indicator (floor i) :=
    condExp_of_stronglyMeasurable hle ((hme i).indicator hB).stronglyMeasurable
      ((he i).indicator hBa)
  apply signed_fixedID_of_moments rate rewards C_star C_h control0 ids S q B hBa raw floor
    (fun i => (ha i).indicator hBa) (fun i => (he i).indicator hBa) _ _ hactive hraw hfloor
  · intro i
    filter_upwards [condExp_indicator (ha i) hB, hm i] with z hz hb
    rw [hr i, hf i, hz]
    by_cases hmem : z ∈ B
    · simp only [Set.indicator_of_mem hmem]
      linarith [(hb hmem).1]
    · simp only [Set.indicator_of_notMem hmem, zero_add, le_refl]
  · intro i
    filter_upwards [condExp_indicator (ha i) hB, hm i] with z hz hb
    rw [hr i, hz]
    by_cases hmem : z ∈ B
    · simpa only [Set.indicator_of_mem hmem] using (hb hmem).2
    · simp only [Set.indicator_of_notMem hmem, le_refl]

include control0 in
/-- Sharp rounded/raw comparison for the actual continuing LIVE branch in every original ID section. -/
public theorem live_signedComparison_fixedID :
    Integrable ((D ∩ liveBranch rate rewards C_star C_h q).indicator
      (acceptedArrivalComparatorGap rate rewards C_star C_h S q)) μ ∧
    Integrable ((D ∩ liveBranch rate rewards C_star C_h q).indicator
      (retainedRewardGap rate rewards C_star C_h S q)) μ ∧
    Integrable ((D ∩ liveBranch rate rewards C_star C_h q).indicator
      (retainedRateFloor rate rewards C_star C_h S q)) μ ∧
    (∫ z in D ∩ liveBranch rate rewards C_star C_h q,
      retainedRewardGap rate rewards C_star C_h S q z ∂μ) ≤
      (∫ z in D ∩ liveBranch rate rewards C_star C_h q,
        acceptedArrivalComparatorGap rate rewards C_star C_h S q z ∂μ) +
      (∫ z in D ∩ liveBranch rate rewards C_star C_h q,
        retainedRateFloor rate rewards C_star C_h S q z ∂μ) := by
  let raw := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival rate rewards C_star C_h q
  let xi := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate rate rewards C_star C_h q
  have hxi i : Measurable[F] (xi i) :=
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate_measurable rate rewards C_star C_h control0 q i
  have hbound i z : 0 ≤ xi i z ∧ xi i z ≤ 1 := by
    by_cases hz : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q
    · obtain ⟨r, regs, owned, base, c, selected, _, _, _, hc, _, _, hrate, _⟩ :=
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell_data rate rewards C_star C_h q z hz
      simpa [xi, ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate,
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualParameters, hz, hc, hrate] using
        payload_rate_bounds rate selected.view.payload i
    · simp [xi, ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate, hz]
  have hi i : Integrable (xi i) μ := (integrable_const (1 : ℝ)).mono'
    ((hxi i).mono ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (q.val + 1))
      le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_of_nonneg (hbound i z).1]; exact (hbound i z).2)
  apply signed_predictable_fixedID rate rewards C_star C_h control0 ids S q
    (liveBranch rate rewards C_star C_h q)
    (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.measurableSet_liveRetainedGate
      rate rewards C_star C_h control0 q) raw (fun i z => xi i z / (rate.n : ℝ))
    (fun i => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival_integrable
      rate rewards C_star C_h control0 q i)
    (fun i => (hi i).div_const _) (fun i => (hxi i).div_const _) _ _
    (fun z hz i => acceptedArrival_eq_actualArrival_live rate rewards C_star C_h q z hz i) _
  · intro i
    filter_upwards [ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival_condExp_bounds
      rate rewards C_star C_h control0 q i] with z hm
    intro hz
    apply hm
    simpa [ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveDomain] using hz.1.1
  · intro z hz
    exact ((ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveGate_iff_activeUpdate
      rate rewards C_star C_h q z).mp hz).2
  · intro z hz
    obtain ⟨r, c, _, _, _, hc, _, hcell⟩ :=
      ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveDomain_cell0 rate rewards C_star C_h q z hz.1.1
    have hd : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q := by
      simpa [ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveDomain] using hz.1.1
    simp [hcell, xi, ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRate,
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualParameters, hd, hc]

private def collectionRate (i : Fin p.K) (z : X) : ℝ :=
  (ReferenceFirstCollectionOldRecorderFoundation.incomingRates? rate rewards C_star C_h q z).getD (fun _ => 0) i

private theorem collection_moment_bounds (i : Fin p.K) :
    ∀ᵐ z ∂μ, z ∈ collectionBranch rate rewards C_star C_h q →
      roundedRewardAt rewards q i - collectionRate rate rewards C_star C_h q i z / (rate.n : ℝ) ≤
        μ[ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q i | F] z ∧
      μ[ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q i | F] z ≤
        roundedRewardAt rewards q i := by
  filter_upwards [ReferenceOriginalCalendarLiveCollectionWeightedDrift.collection_oldRaw_condExp_factor
    rate rewards C_star C_h control0 q i,
    ReferenceOriginalCalendarCollectionRetainedEnergyStep.presentCell_marker_condExp
      rate rewards C_star C_h control0 q (some i)] with z hfactor hmarker
  intro hz
  obtain ⟨r, c, payload, _, _, hp, _, _⟩ :=
    ReferenceOriginalCalendarCollectionRetainedEnergyStep.presentCell_recordingMap rate rewards C_star C_h q z hz.1.1.1
  have hxipos := CanonicalRecordingRates.xi_pos p rate.eta.property payload.anchor i
  have hr := ReferenceFirstCollectionOldRecorderFoundation.roundedReward_bounds rewards q i
  have hl := QuantizedRecordingMoments.quantizedValue_roundingError (ConstructorDimensions.D p)
    rate.eta.val (payload.rate i) _ (ConstructorDimensions.D_pos p) rate.eta.property hxipos hr
  have hu := QuantizedRecordingMoments.quantizedValue_firstMoment_le (ConstructorDimensions.D p)
    rate.eta.val (payload.rate i) _ (ConstructorDimensions.D_pos p) rate.eta.property hxipos hr
  have hen : ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
      rate rewards C_star C_h q z = some true := hz.2.2
  rw [hfactor]
  simp only [Pi.mul_apply, hmarker, Set.indicator_of_mem hz.1.1.1,
    hen, ite_true, ReferenceFirstCollectionOldRecorderFoundation.incomingAmplitude?, hp,
    ReferenceFirstCollectionOldRecorderFoundation.incomingRates?, Option.map_some, Option.getD_some]
  simpa only [roundedRewardAt, collectionRate,
    ReferenceFirstCollectionOldRecorderFoundation.incomingRates?, hp, Option.map_some,
    Option.getD_some, rate.n_scale, mul_comm] using And.intro hl hu

include control0 in
/-- The unrestricted collection branch has the sharp signed comparison,
localized before integration to each original fixed-ID section. -/
public theorem collection_signedComparison_fixedID :
    Integrable ((D ∩ collectionBranch rate rewards C_star C_h q).indicator
      (acceptedArrivalComparatorGap rate rewards C_star C_h S q)) μ ∧
    Integrable ((D ∩ collectionBranch rate rewards C_star C_h q).indicator
      (retainedRewardGap rate rewards C_star C_h S q)) μ ∧
    Integrable ((D ∩ collectionBranch rate rewards C_star C_h q).indicator
      (retainedRateFloor rate rewards C_star C_h S q)) μ ∧
    (∫ z in D ∩ collectionBranch rate rewards C_star C_h q,
      retainedRewardGap rate rewards C_star C_h S q z ∂μ) ≤
      (∫ z in D ∩ collectionBranch rate rewards C_star C_h q,
        acceptedArrivalComparatorGap rate rewards C_star C_h S q z ∂μ) +
      (∫ z in D ∩ collectionBranch rate rewards C_star C_h q,
        retainedRateFloor rate rewards C_star C_h S q z ∂μ) := by
  let xi := collectionRate rate rewards C_star C_h q
  have hxi i : Measurable[F] (xi i) := by
    convert (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim 0
      (fun v : Fin p.K → ℝ => v i) (measurable_pi_apply i)).comp
      (ReferenceFirstCollectionOldRecorderFoundation.incomingRates_measurable rate rewards C_star C_h control0 q) using 1
    funext z
    cases hp : ReferenceFirstCollectionOldRecorderFoundation.incomingRates? rate rewards C_star C_h q z <;>
      simp [xi, collectionRate, ReferenceCollectionOutcomeMeasurability.optionalElim, hp]
  have hb i z : 0 ≤ xi i z ∧ xi i z ≤ 1 := by
    cases hp : ReferenceFirstCollectionOldRecorderFoundation.incomingPayload? rate rewards C_star C_h q z with
    | none => simp [xi, collectionRate, ReferenceFirstCollectionOldRecorderFoundation.incomingRates?, hp]
    | some payload => simpa [xi, collectionRate, ReferenceFirstCollectionOldRecorderFoundation.incomingRates?, hp]
        using payload_rate_bounds rate payload i
  have hi i : Integrable (xi i) μ := (integrable_const (1 : ℝ)).mono'
    ((hxi i).mono ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (q.val + 1))
      le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_of_nonneg (hb i z).1]; exact (hb i z).2)
  apply signed_predictable_fixedID rate rewards C_star C_h control0 ids S q
    (collectionBranch rate rewards C_star C_h q)
    (ReferenceOriginalCalendarCollectionRetainedEnergyStep.measurableSet_G rate rewards C_star C_h control0 q)
    (ReferenceFirstCollectionOldRecorderFoundation.oldRaw rate rewards C_star C_h q)
    (fun i z => xi i z / (rate.n : ℝ))
    (fun i => ReferenceFirstCollectionOldRecorderFoundation.oldRaw_integrable rate rewards C_star C_h q i)
    (fun i => (hi i).div_const _) (fun i => (hxi i).div_const _)
    (fun i => collection_moment_bounds rate rewards C_star C_h control0 q i) _
    (fun z hz i => acceptedArrival_eq_oldRaw_collection rate rewards C_star C_h q z hz i) _
  · intro z hz
    exact ((ReferenceOriginalCalendarRetainedBranchPartition.activeCollectionSelector_iff_G
      rate rewards C_star C_h q ⟨0, by have := p.two_le_m; have := p.m_lt_K; omega⟩ z).mpr hz).1
  · intro z hz
    obtain ⟨hactive, hs⟩ := (ReferenceOriginalCalendarRetainedBranchPartition.activeCollectionSelector_iff_G
      rate rewards C_star C_h q ⟨0, by have := p.two_le_m; have := p.m_lt_K; omega⟩ z).mpr hz
    obtain ⟨⟨r, c, payload⟩, hs⟩ := Option.isSome_iff_exists.mp hs
    have hc := ReferenceOriginalCalendarRetainedBranchPartition.collectionSelector_eq_collectionRecorder
      rate rewards C_star C_h q z r c payload hs
    obtain ⟨r', c', payload', _, hc', hp, hrate, _⟩ :=
      ReferenceOriginalCalendarCollectionRetainedEnergyStep.presentCell_recordingMap rate rewards C_star C_h q z hz.1.1.1
    have hcc : c' = c := Option.some.inj (hc'.symm.trans hc.1)
    subst c'
    simp [hc.2, xi, collectionRate, ReferenceFirstCollectionOldRecorderFoundation.incomingRates?, hp, hrate]

section Birth

local notation "A" => renewedBirthBranch rate rewards C_star C_h q
local notation "E" => ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet rate rewards C_star C_h q
local notation "H" => ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q
local notation "α" => ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.laterBirthPresenceMass
  rate rewards C_star C_h control0 q
local notation "I" => ReferenceOriginalCalendarLaterBirthWeightedDrift.originalPrefixInverseRateSum
  rate rewards C_star C_h q
local notation "par" => ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h q

private def birthRate (i : Fin p.K) (z : X) : ℝ :=
  (par z).elim 0 (fun theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 i)

private theorem birthRate_measurable (i : Fin p.K) :
    Measurable[F] (birthRate rate rewards C_star C_h q i) := by
  have hp (s : Finset (Fin p.K)) : Measurable (fun v : Fin p.K → ℝ => ProductSetLaw.setWeight v s) := by
    unfold ProductSetLaw.setWeight
    fun_prop
  have ht : Measurable (fun v : Fin p.K → ℝ => ProductSetLaw.theta p.m v i) := by
    unfold ProductSetLaw.theta FiniteNormalization.mass FiniteNormalization.normalizedWeight FiniteNormalization.totalMass
    fun_prop
  have hf : Measurable (fun v : Fin p.K → ℝ => CanonicalRecordingRates.f p v i) := by
    unfold CanonicalRecordingRates.f
    fun_prop
  have hxi : Measurable (fun theta : AssignmentParameterFibreKernel.Theta p =>
      CanonicalRecordingRates.xi p rate.eta.val theta.2 i) :=
    (AssignmentPayloadDerivedMeasurability.measurable_dyadicCeiling.comp
    (measurable_const.max hf)).comp measurable_snd
  convert (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim 0 _ hxi).comp
    (ReferenceCalendarLaterSamplerPredictability.calendarParameters_measurable rate rewards C_star C_h control0 q) using 1
  funext z
  cases hp : par z <;> simp [birthRate, hp, ReferenceCollectionOutcomeMeasurability.optionalElim]

private theorem birth_rate_cell (z : X) (hz : z ∈ A) :
    ∃ past c, PI q.val z = some past ∧ cell z = some c ∧
      (∀ i, birthRate rate rewards C_star C_h q i z = c.rate i) ∧
      (∀ i, 0 ≤ c.rate i ∧ c.rate i ≤ 1) := by
  obtain ⟨past, c, hpast, hc, hcurrent, _, _⟩ := birth_observations rate rewards C_star C_h q z hz
  have hs := hz
  rw [renewedBirthBranch,
    ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet_eq_sourceEvent] at hs
  obtain ⟨theta, htheta⟩ := Option.isSome_iff_exists.mp hs.1.1
  obtain ⟨r, hr, hparams⟩ := Option.bind_eq_some_iff.mp htheta
  have hread := hcurrent
  simp only [ReferenceFirstCollectionCurrentNumericalCell.currentCell, hr, Option.bind_some] at hread
  obtain ⟨_, selected, hselected, _, hrate, _⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical _ r c hread
  have hanchor := ReferenceFirstCollectionCurrentRecordedCell.selected_anchor rate r theta hparams selected hselected
  refine ⟨past, c, hpast, hc, ?_, ?_⟩
  · intro i
    simp only [birthRate, htheta, Option.elim_some, hrate, AssignmentStartPayload.Input.rate_eq_canonical, hanchor]
  · intro i
    rw [hrate]
    exact payload_rate_bounds rate selected.view.payload i

private theorem inverseRateSum_eq : I = fun z => ∑ i : Fin p.K, θ q.val i z / birthRate rate rewards C_star C_h q i z := by
  funext z
  cases hp : par z <;> cases hpre : PI q.val z <;>
    simp [ReferenceOriginalCalendarLaterBirthWeightedDrift.originalPrefixInverseRateSum,
      ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt, birthRate, hp, hpre]

private theorem inverseRateSum_data : Measurable[F] I ∧
    (∀ z, 0 ≤ I z ∧ I z ≤ (p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val) := by
  rw [inverseRateSum_eq rate rewards C_star C_h q]
  refine ⟨Finset.measurable_fun_sum _ (fun i _ =>
    (ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt_measurable rate rewards C_star C_h control0 q i).div
      (birthRate_measurable rate rewards C_star C_h control0 q i)), ?_⟩
  intro z
  have hb i : 0 ≤ θ q.val i z / birthRate rate rewards C_star C_h q i z ∧
      θ q.val i z / birthRate rate rewards C_star C_h q i z ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := by
    have ht := ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt_bounds rate rewards C_star C_h q.val i z
    cases hp : par z with
    | none => simp [birthRate, hp, (CanonicalRecordingRates.beta_pos p rate.eta.property).le]
    | some theta =>
      simp only [birthRate, hp, Option.elim_some]
      have hx := CanonicalRecordingRates.xi_pos p rate.eta.property theta.2 i
      exact ⟨div_nonneg ht.1 hx.le, (div_le_div_of_nonneg_right ht.2 hx.le).trans
        (one_div_le_one_div_of_le (CanonicalRecordingRates.beta_pos p rate.eta.property)
          (CanonicalRecordingRates.beta_le_xi p rate.eta.property theta.2 i))⟩
  refine ⟨Finset.sum_nonneg (fun i _ => (hb i).1), ?_⟩
  simpa [div_eq_mul_inv] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hb i).2)

private theorem birth_predictable_condExp (f : X → ℝ) (hf : Measurable[F] f)
    (hfi : Integrable ((A).indicator f) μ) :
    μ[(A).indicator f | F] =ᵐ[μ] (E ∩ H).indicator (fun z => α z * f z) := by
  have hm := ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdate_mass_condExp
    rate rewards C_star C_h control0 q
  have heq : (A).indicator f = f * (A).indicator (fun _ : X => (1 : ℝ)) := by
    funext z
    by_cases hz : z ∈ A <;> simp [Set.indicator, hz]
  have hc := condExp_mul_of_aestronglyMeasurable_left hf.aestronglyMeasurable
    (heq ▸ hfi) hm.1
  change μ[f * (A).indicator (fun _ : X => (1 : ℝ)) | F] =ᵐ[μ]
    f * μ[(A).indicator (fun _ : X => (1 : ℝ)) | F] at hc
  rw [← heq] at hc
  filter_upwards [hc, hm.2] with z hcz hmz
  rw [hcz]
  change f z * μ[(A).indicator (fun _ : X => (1 : ℝ)) | F] z = _
  change μ[(A).indicator (fun _ : X => (1 : ℝ)) | F] z = _ at hmz
  rw [hmz]
  by_cases hz : z ∈ E ∩ H <;> simp [Set.indicator, hz, mul_comm]

include control0 in
/-- The actual successful later birth has the canonical drift bound on each ID section.
The inverse-rate allowance is transported through the success conditional law first. -/
public theorem renewedBirth_retained_weightedSquare_fixedID :
    Integrable ((D ∩ A).indicator (ΔV q)) μ ∧
    Integrable ((D ∩ A).indicator (C q.val)) μ ∧
    (∫ z in D ∩ A, ΔV q z ∂μ) ≤ -(11 / 2 : ℝ) * (∫ z in D ∩ A, C q.val z ∂μ) +
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) * (μ).real (D ∩ A) := by
  have hA := measurableSet_renewedBirthBranch rate rewards C_star C_h control0 q
  have hD := ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hDp := measurableSet_fixedIDSourceSection_prefix control0 ids q
  have hle := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (q.val + 1)
  have hdata := inverseRateSum_data rate rewards C_star C_h control0 q
  have hI : Integrable I μ := (integrable_const _).mono'
    (hdata.1.mono hle le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_of_nonneg (hdata.2 z).1]; exact (hdata.2 z).2)
  have hC := C_integrable rate rewards C_star C_h control0 q
  have hΔ0 := (ReferenceOriginalCalendarLiveCollectionWeightedDrift.V_integrable rate rewards C_star C_h (q.val + 1)).sub
    (ReferenceOriginalCalendarLiveCollectionWeightedDrift.V_integrable rate rewards C_star C_h q.val)
  have hΔ : Integrable ((A).indicator (ΔV q)) μ := by
    have heq : V (q.val + 1) - V q.val = ΔV q := by funext z; rfl
    rw [heq] at hΔ0
    exact hΔ0.indicator hA
  have hm := ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdate_mass_condExp
    rate rewards C_star C_h control0 q
  have hc := birth_predictable_condExp rate rewards C_star C_h control0 q _
    (C_measurable rate rewards C_star C_h control0 q) (hC.indicator hA)
  have hi := birth_predictable_condExp rate rewards C_star C_h control0 q I hdata.1 (hI.indicator hA)
  have hd := ReferenceOriginalCalendarLaterBirthWeightedDrift.originalLaterBirth_weightedSquare_condExp
    rate rewards C_star C_h control0 q
  have hevent : ReferenceOriginalCalendarLaterBirthWeightedDrift.actualRetainedLaterBirthEvent
      rate rewards C_star C_h q = A :=
    (ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet_eq_sourceEvent
      rate rewards C_star C_h q).symm
  rw [hevent] at hd
  have hδeq : ReferenceOriginalCalendarLaterBirthWeightedDrift.originalPrefixWeightedSquareDelta
      rate rewards C_star C_h q = ΔV q := by
    funext z
    cases hp : PI q.val z <;> cases hn : PI (q.val + 1) z <;>
      simp [ReferenceOriginalCalendarLaterBirthWeightedDrift.originalPrefixWeightedSquareDelta,
        ReferenceOriginalCalendarLaterBirthWeightedDrift.originalPrefixWeightedSquarePotential,
        ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV,
        ReferenceOriginalCalendarLiveCollectionWeightedDrift.V, hp, hn]
  have hceq : ReferenceOriginalCalendarLaterBirthWeightedDrift.originalPrefixWeightedBacklog
      rate rewards C_star C_h q.val = C q.val := by
    funext z
    cases hp : PI q.val z <;> simp [ReferenceOriginalCalendarLaterBirthWeightedDrift.originalPrefixWeightedBacklog,
      ReferenceOriginalCalendarLiveCollectionWeightedDrift.C, hp]
  rw [hδeq, hceq] at hd
  have hbound : μ[(A).indicator (ΔV q) | F] ≤ᵐ[μ] fun z =>
      -(11 / 2 : ℝ) * μ[(A).indicator (C q.val) | F] z + μ[(A).indicator I | F] z +
        ((33 / 2 : ℝ) * p.m) * μ[(A).indicator (fun _ => (1 : ℝ)) | F] z := by
    filter_upwards [hd, hc, hi, hm.2] with z hdz hcz hiz hmz
    change μ[(A).indicator (fun _ : X => (1 : ℝ)) | F] z = _ at hmz
    rw [hcz, hiz, hmz]
    refine hdz.trans_eq ?_
    by_cases hz : z ∈ E ∩ H
    · simp only [Set.indicator_of_mem hz]
      ring
    · simp only [Set.indicator_of_notMem hz, mul_zero, add_zero, mul_zero]
  have hci : Integrable (μ[(A).indicator (C q.val) | F]) μ := integrable_condExp
  have hii : Integrable (μ[(A).indicator I | F]) μ := integrable_condExp
  have hmi : Integrable (μ[(A).indicator (fun _ : X => (1 : ℝ)) | F]) μ := integrable_condExp
  have hmassInt : Integrable ((A).indicator (fun _ : X => (1 : ℝ))) μ := hm.1
  have hlocal := local_condExp_le control0 q hDp hΔ
    (((hci.const_mul (-(11 / 2 : ℝ))).add hii).add (hmi.const_mul ((33 / 2 : ℝ) * p.m))) hbound
  change (∫ z in D, (A).indicator (ΔV q) z ∂μ) ≤ ∫ z in D,
    -(11 / 2 : ℝ) * μ[(A).indicator (C q.val) | F] z + μ[(A).indicator I | F] z +
      ((33 / 2 : ℝ) * p.m) * μ[(A).indicator (fun _ : X => (1 : ℝ)) | F] z ∂μ at hlocal
  have hfirst : Integrable (fun z => -(11 / 2 : ℝ) * μ[(A).indicator (C q.val) | F] z +
      μ[(A).indicator I | F] z) μ := (hci.const_mul _).add hii
  rw [integral_add hfirst.integrableOn (hmi.const_mul _).integrableOn,
    integral_add (hci.const_mul _).integrableOn hii.integrableOn,
    integral_const_mul, integral_const_mul,
    setIntegral_condExp hle (hC.indicator hA) hDp,
    setIntegral_condExp hle (hI.indicator hA) hDp,
    setIntegral_condExp hle hmassInt hDp] at hlocal
  simp only [setIntegral_indicator hA, integral_const, smul_eq_mul, mul_one,
    measureReal_restrict_apply_univ] at hlocal
  have hIBound : (∫ z in D ∩ A, I z ∂μ) ≤ CanonicalRecordingRates.R p * (μ).real (D ∩ A) := by
    have hmono : (∫ z in D ∩ A, I z ∂μ) ≤ ∫ _z in D ∩ A, CanonicalRecordingRates.R p ∂μ := by
      apply integral_mono_ae hI.integrableOn (integrable_const _)
      filter_upwards [ae_restrict_mem (hD.inter hA)] with z hz
      obtain ⟨past, c, hpast, hcell, hrate, _⟩ := birth_rate_cell rate rewards C_star C_h q z hz.2
      rw [inverseRateSum_eq rate rewards C_star C_h q]
      simp_rw [hrate]
      exact actual_active_rate_sum_le rate rewards C_star C_h q z past hpast c hcell hz.2.2
    simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, mul_comm] using hmono
  refine ⟨?_, hC.indicator (hD.inter hA), ?_⟩
  · simpa only [Set.indicator_indicator] using hΔ.indicator hD
  · nlinarith [hlocal, hIBound]

private theorem birth_signed_moments (i : Fin p.K) :
    let raw := ReferenceFirstCollectionCurrentRawMoments.currentRaw rate rewards C_star C_h q i
    let floor := fun z => birthRate rate rewards C_star C_h q i z / (rate.n : ℝ)
    Integrable ((A).indicator raw) μ ∧ Integrable ((A).indicator floor) μ ∧
    (∀ᵐ z ∂μ, μ[(A).indicator (fun _ => roundedRewardAt rewards q i) | F] z ≤
      μ[(A).indicator raw | F] z + μ[(A).indicator floor | F] z ∧
      μ[(A).indicator raw | F] z ≤ μ[(A).indicator (fun _ => roundedRewardAt rewards q i) | F] z) := by
  let raw := ReferenceFirstCollectionCurrentRawMoments.currentRaw rate rewards C_star C_h q i
  let floor := fun z => birthRate rate rewards C_star C_h q i z / (rate.n : ℝ)
  have hle := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (q.val + 1)
  have hA := measurableSet_renewedBirthBranch rate rewards C_star C_h control0 q
  have hE := ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet_measurable
    rate rewards C_star C_h control0 q
  have hH := ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H rate rewards C_star C_h control0 q
  have hrawE : Integrable ((E).indicator raw) μ := by
    apply (integrable_const (1 / CanonicalRecordingRates.beta p rate.eta.val)).mono'
      ((ReferenceFirstCollectionCurrentRawMoments.currentRaw_measurable rate rewards C_star C_h q i).indicator (hle _ hE)).aestronglyMeasurable
    filter_upwards [] with z
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz]
      rw [ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirthRaw_factor
        rate rewards C_star C_h q i z hz]
      have hb := ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.currentAmplitude_bounds rate rewards C_star C_h q i z
      split_ifs <;> simp only [one_mul, zero_mul, norm_zero]
      · rw [Real.norm_of_nonneg hb.1]
        exact hb.2
      · exact one_div_nonneg.mpr (CanonicalRecordingRates.beta_pos p rate.eta.property).le
    · simp only [Set.indicator_of_notMem hz, norm_zero]
      exact one_div_nonneg.mpr (CanonicalRecordingRates.beta_pos p rate.eta.property).le
  have heq : (A).indicator raw = (H).indicator ((E).indicator raw) := by
    funext z
    by_cases he : z ∈ E
    · have hfactor := ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirthRaw_factor
        rate rewards C_star C_h q i z he
      by_cases hh : z ∈ H <;>
        cases hm : ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker rate rewards C_star C_h q z <;>
        simp [Set.indicator, renewedBirthBranch,
          ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet_eq_sourceEvent,
          he, hh, raw, hfactor, hm]
    · simp [Set.indicator, renewedBirthBranch,
        ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet_eq_sourceEvent, he]
  have hrawA : Integrable ((A).indicator raw) μ := by rw [heq]; exact hrawE.indicator (hle _ hH)
  have hfloorM : Measurable[F] floor := (birthRate_measurable rate rewards C_star C_h control0 q i).div_const _
  have hfloorI : Integrable ((A).indicator floor) μ := by
    apply (integrable_const (1 / (rate.n : ℝ))).mono'
      ((hfloorM.mono hle le_rfl).indicator hA).aestronglyMeasurable
    filter_upwards [] with z
    by_cases hz : z ∈ A
    · obtain ⟨past, c, _, _, hr, hb⟩ := birth_rate_cell rate rewards C_star C_h q z hz
      rw [Set.indicator_of_mem hz]
      dsimp only [floor]
      rw [hr i, Real.norm_of_nonneg (div_nonneg (hb i).1 (Nat.cast_nonneg _))]
      exact div_le_div_of_nonneg_right (hb i).2 (Nat.cast_nonneg _)
    · simp only [Set.indicator_of_notMem hz, norm_zero]
      exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  have haCE : μ[(A).indicator raw | F] =ᵐ[μ] (H).indicator (μ[(E).indicator raw | F]) := by
    rw [heq]
    exact condExp_indicator hrawE hH
  have hfCE := birth_predictable_condExp rate rewards C_star C_h control0 q floor hfloorM hfloorI
  have hrCE := birth_predictable_condExp rate rewards C_star C_h control0 q
    (fun _ : X => roundedRewardAt rewards q i) measurable_const ((integrable_const _).indicator hA)
  refine ⟨hrawA, hfloorI, ?_⟩
  filter_upwards [haCE, hfCE, hrCE,
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirth_moments rate rewards C_star C_h control0 q i,
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirthRaw_condExp rate rewards C_star C_h control0 q i]
    with z haz hfz hrz hm hrawz
  rw [haz, hfz, hrz]
  by_cases hz : z ∈ E ∩ H
  · obtain ⟨theta, hp⟩ := Option.isSome_iff_exists.mp hz.1
    have hb := hm theta hp
    simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hz.2]
    dsimp only [floor]
    simp only [birthRate, hp, Option.elim_some]
    have hn := rate.n_scale
    dsimp only [roundedRewardAt, ReferenceFirstCollectionOldRecorderFoundation.roundedReward]
    rw [hn]
    exact ⟨by nlinarith [hb.2.2.1], hb.2.2.2.1⟩
  · by_cases hh : z ∈ H
    · have he : z ∉ E := fun he => hz ⟨he, hh⟩
      simp only [Set.indicator_of_notMem hz, Set.indicator_of_mem hh]
      change μ[(E).indicator raw | F] z = _ at hrawz
      rw [hrawz, Set.indicator_of_notMem he]
      norm_num
    · simp only [Set.indicator_of_notMem hz, Set.indicator_of_notMem hh, zero_add, le_refl, and_self]

include control0 in
/-- Both signed sides retain the same whole-vector success mass until localization on D. -/
public theorem renewedBirth_signedComparison_fixedID :
    Integrable ((D ∩ A).indicator (acceptedArrivalComparatorGap rate rewards C_star C_h S q)) μ ∧
    Integrable ((D ∩ A).indicator (retainedRewardGap rate rewards C_star C_h S q)) μ ∧
    Integrable ((D ∩ A).indicator (retainedRateFloor rate rewards C_star C_h S q)) μ ∧
    (∫ z in D ∩ A, retainedRewardGap rate rewards C_star C_h S q z ∂μ) ≤
      (∫ z in D ∩ A, acceptedArrivalComparatorGap rate rewards C_star C_h S q z ∂μ) +
      (∫ z in D ∩ A, retainedRateFloor rate rewards C_star C_h S q z ∂μ) := by
  have hm := birth_signed_moments rate rewards C_star C_h control0 q
  apply signed_fixedID_of_moments rate rewards C_star C_h control0 ids S q A
    (measurableSet_renewedBirthBranch rate rewards C_star C_h control0 q)
    (ReferenceFirstCollectionCurrentRawMoments.currentRaw rate rewards C_star C_h q)
    (fun i z => birthRate rate rewards C_star C_h q i z / (rate.n : ℝ))
    (fun i => (hm i).1) (fun i => (hm i).2.1)
    (fun i => (hm i).2.2.mono fun _ h => h.1) (fun i => (hm i).2.2.mono fun _ h => h.2)
    (fun _ hz => hz.2)
    (fun z hz i => acceptedArrival_eq_currentRaw_birth rate rewards C_star C_h q z hz i) _
  intro z hz
  obtain ⟨past, c, _, hc, hr, _⟩ := birth_rate_cell rate rewards C_star C_h q z hz
  simp only [hc]
  simp_rw [hr]

end Birth

end Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning

end
