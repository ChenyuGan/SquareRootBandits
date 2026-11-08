/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning
public import Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport
public import Bandits.Support.ReferenceCompleteOriginalCalendarRawLearningComparison

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Retained rounded learning on the literal original fixed-ID section

This module assembles the four actual retained branches date by date. The
finite observable below is the rounded learning gap from the original
calendar, using the accepted full-prefix cell and the same current marginal
vector as the weighted square potential.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceOriginalCalendarFixedIDLearningMean

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ProductSetLaw (ProductSet)

variable {p : Parameters}

/-- The retained rounded comparator-minus-current-marginal learning sum over
the complete original calendar, with the actual accepted full-prefix
observation at every date. -/
public def retainedRoundedLearningSum
    (rate : RateInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (S : ProductSet p.K p.m)
    (z : SourceInput p) : ℝ :=
  ∑ t : Fin p.T,
    ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRewardGap
      rate rewards C_star C_h S t z

local notation "X" => SourceInput p
local notation "μ" => sourceInputLaw p

/-- On the literal FIRST selector, the first transport observations are the
same accepted full-prefix observations used by the nonfirst branch module.
The empty prefix and the actual first cell are obtained from the selector. -/
private theorem first_observers_align
    (rate : RateInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (S : ProductSet p.K p.m)
    (t : Fin p.T) (z : X)
    (hz : z ∈ Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent rate rewards C_star C_h t) :
    Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstWeightedArrival rate rewards C_star C_h t z =
        Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.weightedAcceptedArrival rate rewards C_star C_h t z ∧
      Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstRawComparatorGap rate rewards C_star C_h S t z =
        Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap rate rewards C_star C_h S t z ∧
      Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstRoundedRewardGap rate rewards C_star C_h S t z =
        Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRewardGap rate rewards C_star C_h S t z ∧
      Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstServiceFloor rate rewards C_star C_h S t z =
        Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor rate rewards C_star C_h S t z := by
  classical
  have hs : (Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.firstChosenSelector rate rewards C_star C_h t z).isSome = true := by
    simpa [Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent] using hz
  obtain ⟨data, hselector⟩ := Option.isSome_iff_exists.mp hs
  rcases data with ⟨r, cp⟩
  rcases cp with ⟨c, payload⟩
  have hfirst := Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.firstSelector_initialPrefix rate rewards C_star C_h t z r c payload hselector
  have hcell := Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.firstSelector_actualCell rate rewards C_star C_h t z r c payload hselector
  have hactive := Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.firstSelector_activeUpdate rate rewards C_star C_h t z r c payload hselector
  have harrival (i : Fin p.K) :
      Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstAcceptedArrival rate rewards C_star C_h t i z =
        Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalAt rate rewards C_star C_h t i z := by
    rw [Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstAcceptedArrival,
      Set.indicator_of_mem hz, hcell]
    unfold Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalAt
    rw [hfirst.2.2.1, hcell]
    rfl
  have hweighted :
      Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstWeightedArrival rate rewards C_star C_h t z =
        Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.weightedAcceptedArrival rate rewards C_star C_h t z := by
    unfold Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstWeightedArrival Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.weightedAcceptedArrival
    apply Finset.sum_congr rfl
    intro i hi
    rw [harrival]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hweighted
  · unfold Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstRawComparatorGap Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap
    rw [hweighted]
    apply congrArg₂ (· - ·)
    · apply Finset.sum_congr rfl
      intro i hi
      exact harrival i
    · rfl
  · simp [Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstRoundedRewardGap, Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRewardGap, hactive,
      Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent, hs, Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.roundedRewardAt,
      Bandits.Support.ReferenceFirstCollectionOldRecorderFoundation.roundedReward]
  · simp [Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstServiceFloor, Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor, hactive,
      Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent, hs, hcell]

/-- The FIRST branch signed comparison on the literal fixed-ID section,
rewritten to the same full-prefix observers used by the nonfirst branches. -/
public theorem first_signed_fixedID
    (rate : RateInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (ids : CompletePublicTable.IDArray p) (S : ProductSet p.K p.m)
    (t : Fin p.T) :
    IntegrableOn
        (Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap
          rate rewards C_star C_h S t)
        (ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
          Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
            rate rewards C_star C_h t) (sourceInputLaw p) ∧
    IntegrableOn
        (Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRewardGap
          rate rewards C_star C_h S t)
        (ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
          Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
            rate rewards C_star C_h t) (sourceInputLaw p) ∧
    IntegrableOn
        (Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor
          rate rewards C_star C_h S t)
        (ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
          Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
            rate rewards C_star C_h t) (sourceInputLaw p) ∧
    (∫ z in ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
        Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
          rate rewards C_star C_h t,
      Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRewardGap
        rate rewards C_star C_h S t z ∂sourceInputLaw p) ≤
      (∫ z in ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
        Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
          rate rewards C_star C_h t,
        Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap
          rate rewards C_star C_h S t z ∂sourceInputLaw p) +
      (∫ z in ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
        Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
          rate rewards C_star C_h t,
        Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor
          rate rewards C_star C_h S t z ∂sourceInputLaw p) := by
  let first := Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
    rate rewards C_star C_h t
  let fixed := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  let domain := fixed ∩ first
  have hfirst := Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.first_fixedID_source_transport
    rate rewards C_star C_h control0 ids S t
  rcases hfirst with ⟨_, _, hraw, hrounded, hfloor, _, _, hsigned, _⟩
  have hfirstMeas : MeasurableSet first :=
    Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport.measurableSet_firstSelectorEvent
      rate rewards C_star C_h control0 t ⟨0, by
        have hm := p.two_le_m
        have hmk := p.m_lt_K
        omega⟩
  have hfixedMeas : MeasurableSet fixed :=
    ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hdomainMeas : MeasurableSet domain := hfixedMeas.inter hfirstMeas
  have hrawEq :
      Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstRawComparatorGap
          rate rewards C_star C_h S t =ᵐ[(sourceInputLaw p).restrict domain]
        Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap
          rate rewards C_star C_h S t := by
    filter_upwards [ae_restrict_mem hdomainMeas] with z hz
    exact (first_observers_align rate rewards C_star C_h S t z hz.2).2.1
  have hroundedEq :
      Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstRoundedRewardGap
          rate rewards C_star C_h S t =ᵐ[(sourceInputLaw p).restrict domain]
        Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRewardGap
          rate rewards C_star C_h S t := by
    filter_upwards [ae_restrict_mem hdomainMeas] with z hz
    exact (first_observers_align rate rewards C_star C_h S t z hz.2).2.2.1
  have hfloorEq :
      Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstServiceFloor
          rate rewards C_star C_h S t =ᵐ[(sourceInputLaw p).restrict domain]
        Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor
          rate rewards C_star C_h S t := by
    filter_upwards [ae_restrict_mem hdomainMeas] with z hz
    exact (first_observers_align rate rewards C_star C_h S t z hz.2).2.2.2
  refine ⟨hraw.congr_fun_ae hrawEq, hrounded.congr_fun_ae hroundedEq,
    hfloor.congr_fun_ae hfloorEq, ?_⟩
  calc
    _ = ∫ z in domain,
        Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstRoundedRewardGap
          rate rewards C_star C_h S t z ∂sourceInputLaw p := by
      apply setIntegral_congr_fun hdomainMeas
      intro z hz
      exact (first_observers_align rate rewards C_star C_h S t z hz.2).2.2.1.symm
    _ ≤ (∫ z in domain,
          Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstRawComparatorGap
            rate rewards C_star C_h S t z ∂sourceInputLaw p) +
        (∫ z in domain,
          Bandits.Support.ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstServiceFloor
            rate rewards C_star C_h S t z ∂sourceInputLaw p) := hsigned
    _ = _ := by
      congr 1
      · apply setIntegral_congr_fun hdomainMeas
        intro z hz
        exact (first_observers_align rate rewards C_star C_h S t z hz.2).2.1
      · apply setIntegral_congr_fun hdomainMeas
        intro z hz
        exact (first_observers_align rate rewards C_star C_h S t z hz.2).2.2.2

private theorem dispatch_live_of_state_live
    (rate : RateInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (regs : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters regs)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : r.input.state.coordinator = .live regs owned base) :
    ∃ outcome, ReferenceActivePhysicalStep.dispatch r.input =
      .live regs owned base outcome := by
  unfold ReferenceActivePhysicalStep.dispatch
  simp only [hstate]
  cases hinner : CoordinatorRoundDispatch.dispatch
      (.live (ReferenceActivePhysicalStep.liveInput r.input regs owned base)) with
  | live outcome => exact ⟨outcome, rfl⟩

private theorem continuingLiveRecordSelector_implies_liveInput
    (rate : RateInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hselector : Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveRecordSelector
      rate r = some (c, payload)) :
    ∃ regs owned base, r.input.state.coordinator = .live regs owned base := by
  have hdispatchLive : ∃ regs owned base outcome,
      ReferenceActivePhysicalStep.dispatch r.input = .live regs owned base outcome := by
    unfold Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveRecordSelector
      at hselector
    rcases Option.bind_eq_some_iff.mp hselector with ⟨readCell, hread, hmatch⟩
    cases hdispatch : ReferenceActivePhysicalStep.dispatch r.input with
    | first outcome => simp [hdispatch] at hmatch
    | live regs owned base outcome =>
        cases outcome with
        | continuingChosen dispatched hstart continuation selected =>
            exact ⟨regs, owned, base,
              CoordinatorRoundDispatch.LiveOutcome.continuingChosen
                dispatched hstart continuation selected, rfl⟩
        | _ => simp [hdispatch] at hmatch
    | collection payload ledger clock cutoff outcome => simp [hdispatch] at hmatch
    | invalidCollectionCutoff => simp [hdispatch] at hmatch
    | dagger => simp [hdispatch] at hmatch
  obtain ⟨regs, owned, base, outcome, hcut⟩ := hdispatchLive
  cases hstate : r.input.state.coordinator with
  | first =>
      have hbad := hcut
      unfold ReferenceActivePhysicalStep.dispatch at hbad
      simp only [hstate] at hbad
      split at hbad
      simp_all
  | live regs owned base => exact ⟨regs, owned, base, rfl⟩
  | collection payload ledger proposal =>
      have hbad := hcut
      unfold ReferenceActivePhysicalStep.dispatch at hbad
      simp only [hstate] at hbad
      split_ifs at hbad with hcutoff
      · split at hbad
        simp_all
  | dagger =>
      have hbad := hcut
      unfold ReferenceActivePhysicalStep.dispatch at hbad
      simp only [hstate] at hbad
      simp_all

private theorem continuingLiveRecordSelector_witness_of_actualLiveReadout
    (rate : RateInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (regs : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters regs)
    (base : Fin (p.m - 1) → ℕ) (hstate : r.input.state.coordinator = .live regs owned base)
    (c : RecordedQueueRun.RoundInput p.K)
    (hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c) :
    (Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveRecordSelector
      rate r).isSome = true := by
  have hcoverage :=
    Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.liveRecordSelector_coverage
      rate r c hread
  obtain ⟨outcome, hcut⟩ := dispatch_live_of_state_live rate r regs owned base hstate
  rcases hcoverage with hfirst | hlive | hbirth
  · have hfalse : False := by
      unfold Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.firstChosenRecordSelector at hfirst
      rw [hcut] at hfirst
      simp at hfirst
    exact False.elim hfalse
  · exact hlive
  · have hfalse : False := by
      unfold Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector at hbirth
      rw [hcut] at hbirth
      simp at hbirth
    exact False.elim hfalse

private theorem continuing_selector_mem_domain
    (rate : RateInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : X)
    (hselector : (Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
      rate rewards C_star C_h t z).isSome = true) :
    z ∈ Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h t := by
  classical
  obtain ⟨data, hsome⟩ := Option.isSome_iff_exists.mp hselector
  rcases data with ⟨r, cp⟩
  rcases cp with ⟨c, payload⟩
  have hparts :
      Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
          rate rewards C_star C_h t z = some r ∧
        Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveRecordSelector
          rate r = some (c, payload) := by
    unfold Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector at hsome
    rcases Option.bind_eq_some_iff.mp hsome with ⟨r', hr, hmap⟩
    rcases Option.map_eq_some_iff.mp hmap with ⟨cp', hcp, heq⟩
    cases heq
    exact ⟨hr, hcp⟩
  rcases hparts with ⟨hr, hrecord⟩
  have hread := Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveRecordSelector_cell
    rate r c payload hrecord
  have hstate := continuingLiveRecordSelector_implies_liveInput
    rate r c payload hrecord
  change ∃ r',
      Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
          rate rewards C_star C_h t z = some r' ∧
        (∃ regs owned base, r'.input.state.coordinator = .live regs owned base) ∧
        (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r').isSome = true
  exact ⟨r, hr, hstate, by rw [hread]; rfl⟩

private theorem live_branch_mem_selector
    (rate : RateInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : X)
    (hz : z ∈ Bandits.Support.ReferenceOriginalCalendarFixedIDNonfirstLearning.liveBranch
      rate rewards C_star C_h t) :
    (Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
      rate rewards C_star C_h t z).isSome = true := by
  have hgate :=
    (Bandits.Support.ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveGate_iff_activeUpdate
      rate rewards C_star C_h t z).mp hz
  rcases hgate with ⟨hdomain, hactive⟩
  change z ∈ Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h t at hdomain
  change ∃ r,
      Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
          rate rewards C_star C_h t z = some r ∧
        (∃ regs owned base, r.input.state.coordinator = .live regs owned base) ∧
        (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).isSome = true at hdomain
  obtain ⟨r, hr, hstate, hreadSome⟩ := hdomain
  obtain ⟨regs, owned, base, hs⟩ := hstate
  obtain ⟨c, hread⟩ := Option.isSome_iff_exists.mp hreadSome
  have hrecord := continuingLiveRecordSelector_witness_of_actualLiveReadout
    rate r regs owned base hs c hread
  change (Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
      rate rewards C_star C_h t z).isSome = true
  unfold Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
  have hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r := by
    simpa only [Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt] using hr
  rw [hr']
  simpa using hrecord


section Assembly

variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "PI" => ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
  rate rewards C_star C_h
local notation "active" => ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt rate rewards C_star C_h
local notation "cell" => ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt rate rewards C_star C_h
local notation "DV" => ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV rate rewards C_star C_h
local notation "cost" => ReferenceOriginalCalendarLiveCollectionWeightedDrift.C rate rewards C_star C_h
local notation "arrival" => ReferenceOriginalCalendarFixedIDNonfirstLearning.weightedAcceptedArrival rate rewards C_star C_h

/-- The four literal retained branches, including FIRST. -/
public def retainedBranch (t : Fin p.T) : Fin 4 → Set X :=
  ![ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent rate rewards C_star C_h t,
    ReferenceOriginalCalendarFixedIDNonfirstLearning.liveBranch rate rewards C_star C_h t,
    ReferenceOriginalCalendarFixedIDNonfirstLearning.renewedBirthBranch rate rewards C_star C_h t,
    ReferenceOriginalCalendarFixedIDNonfirstLearning.collectionBranch rate rewards C_star C_h t]

private theorem live_branch_iff (t : Fin p.T) (z : X) :
    z ∈ ReferenceOriginalCalendarFixedIDNonfirstLearning.liveBranch rate rewards C_star C_h t ↔
      (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector rate rewards C_star C_h t z).isSome = true ∧ active t z := by
  constructor
  · intro hz
    exact ⟨live_branch_mem_selector rate rewards C_star C_h t z hz,
      ((ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveGate_iff_activeUpdate
        rate rewards C_star C_h t z).mp hz).2⟩
  · rintro ⟨hs, ha⟩
    exact (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveGate_iff_activeUpdate
      rate rewards C_star C_h t z).mpr
        ⟨continuing_selector_mem_domain rate rewards C_star C_h t z hs, ha⟩

private theorem branch_mem_active (t : Fin p.T) (j : Fin 4) (z : X)
    (hz : z ∈ retainedBranch rate rewards C_star C_h t j) : active t z := by
  fin_cases j
  · change (ReferenceOriginalCalendarRetainedBranchPartition.firstChosenSelector rate rewards C_star C_h t z).isSome = true at hz
    obtain ⟨⟨r, c, payload⟩, hs⟩ := Option.isSome_iff_exists.mp hz
    exact ReferenceOriginalCalendarRetainedBranchPartition.firstSelector_activeUpdate rate rewards C_star C_h t z r c payload hs
  · exact ((live_branch_iff rate rewards C_star C_h t z).mp hz).2
  · exact hz.2
  · exact ((ReferenceOriginalCalendarRetainedBranchPartition.activeCollectionSelector_iff_G rate rewards C_star C_h t
      ⟨0, by have := p.two_le_m; have := p.m_lt_K; omega⟩ z).mpr hz).1

private theorem branch_membership (t : Fin p.T) (z : X) :
    ((z ∈ retainedBranch rate rewards C_star C_h t 0) ↔
      (ReferenceOriginalCalendarRetainedBranchPartition.firstChosenSelector rate rewards C_star C_h t z).isSome = true) ∧
    ((z ∈ retainedBranch rate rewards C_star C_h t 1) ↔
      (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector rate rewards C_star C_h t z).isSome = true ∧ active t z) ∧
    ((z ∈ retainedBranch rate rewards C_star C_h t 2) ↔
      (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector rate rewards C_star C_h t z).isSome = true ∧ active t z) ∧
    ((z ∈ retainedBranch rate rewards C_star C_h t 3) ↔
      (ReferenceOriginalCalendarRetainedBranchPartition.collectionOrCutoffSelector rate rewards C_star C_h t z).isSome = true ∧ active t z) := by
  refine ⟨Iff.rfl, live_branch_iff rate rewards C_star C_h t z, Iff.rfl, ?_⟩
  exact (ReferenceOriginalCalendarRetainedBranchPartition.activeCollectionSelector_iff_G rate rewards C_star C_h t
    ⟨0, by have := p.two_le_m; have := p.m_lt_K; omega⟩ z).symm.trans and_comm

/-- Each actual retained update has exactly one of the four accepted branches. -/
public theorem retainedBranch_unique (t : Fin p.T) (z : X) :
    active t z ↔ ∃! j : Fin 4, z ∈ retainedBranch rate rewards C_star C_h t j := by
  have hm := branch_membership rate rewards C_star C_h t z
  have hd := ReferenceOriginalCalendarRetainedBranchPartition.branchSelectors_disjoint rate rewards C_star C_h t z
  constructor
  · intro ha
    have hc := ReferenceOriginalCalendarRetainedBranchPartition.activeUpdate_branchCoverage rate rewards C_star C_h t z ha
    have hex : ∃ j : Fin 4, z ∈ retainedBranch rate rewards C_star C_h t j := by
      rcases hc with hf | hl | hb | hc
      · exact ⟨0, hm.1.mpr hf⟩
      · exact ⟨1, hm.2.1.mpr ⟨hl, ha⟩⟩
      · exact ⟨2, hm.2.2.1.mpr ⟨hb, ha⟩⟩
      · exact ⟨3, hm.2.2.2.mpr ⟨hc, ha⟩⟩
    obtain ⟨j, hj⟩ := hex
    refine ⟨j, hj, ?_⟩
    intro k hk
    by_contra hne
    have hsel : ∀ j : Fin 4, z ∈ retainedBranch rate rewards C_star C_h t j →
        ![(ReferenceOriginalCalendarRetainedBranchPartition.firstChosenSelector rate rewards C_star C_h t z).isSome = true,
          (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector rate rewards C_star C_h t z).isSome = true,
          (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector rate rewards C_star C_h t z).isSome = true,
          (ReferenceOriginalCalendarRetainedBranchPartition.collectionOrCutoffSelector rate rewards C_star C_h t z).isSome = true] j := by
      intro j hj
      fin_cases j
      · exact hm.1.mp hj
      · exact (hm.2.1.mp hj).1
      · exact (hm.2.2.1.mp hj).1
      · exact (hm.2.2.2.mp hj).1
    have hj' := hsel j hj
    have hk' := hsel k hk
    clear hj hk hsel hm hc ha
    fin_cases j <;> fin_cases k
    · exact hne rfl
    · exact hd.1 ⟨hj', hk'⟩
    · exact hd.2.1 ⟨hj', hk'⟩
    · exact hd.2.2.1 ⟨hj', hk'⟩
    · exact hd.1 ⟨hk', hj'⟩
    · exact hne rfl
    · exact hd.2.2.2.1 ⟨hj', hk'⟩
    · exact hd.2.2.2.2.1 ⟨hj', hk'⟩
    · exact hd.2.1 ⟨hk', hj'⟩
    · exact hd.2.2.2.1 ⟨hk', hj'⟩
    · exact hne rfl
    · exact hd.2.2.2.2.2 ⟨hj', hk'⟩
    · exact hd.2.2.1 ⟨hk', hj'⟩
    · exact hd.2.2.2.2.1 ⟨hk', hj'⟩
    · exact hd.2.2.2.2.2 ⟨hk', hj'⟩
    · exact hne rfl
  · rintro ⟨j, hj, _⟩
    exact branch_mem_active rate rewards C_star C_h t j z hj

private theorem branch_measurable (control0 : TimeControl p) (t : Fin p.T)
    (j : Fin 4) : MeasurableSet (retainedBranch rate rewards C_star C_h t j) := by
  have hle := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
    (t.val + 1)
  fin_cases j
  · exact ReferenceOriginalCalendarFirstBranchIncrementTransport.measurableSet_firstSelectorEvent rate rewards C_star C_h control0 t
      ⟨0, by have := p.two_le_m; have := p.m_lt_K; omega⟩
  · exact hle _ (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.measurableSet_liveRetainedGate
      rate rewards C_star C_h control0 t)
  · change MeasurableSet (ReferenceOriginalCalendarFixedIDNonfirstLearning.renewedBirthBranch rate rewards C_star C_h t)
    rw [ReferenceOriginalCalendarFixedIDNonfirstLearning.renewedBirthBranch,
      ReferenceOriginalCalendarBirthBranchIncrementTransport.renewedBirthActiveUpdateSet_eq_sourceEvent]
    refine ((hle _ (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet_measurable
      rate rewards C_star C_h control0 t)).inter
      (hle _ (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
        rate rewards C_star C_h control0 t))).inter ?_
    change MeasurableSet ((ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker
      rate rewards C_star C_h t) ⁻¹' {o | o.isSome = true})
    exact (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker_measurable
      rate rewards C_star C_h t) (by simp)
  · exact hle _ (ReferenceOriginalCalendarCollectionRetainedEnergyStep.measurableSet_G
      rate rewards C_star C_h control0 t)

/-- Off the retained update, the literal accepted record has zero arrival.
Enabled zero-arrival service is left untouched by this statement. -/
public theorem acceptedArrival_eq_zero_of_inactive (t : Fin p.T) (i : Fin p.K)
    (z : X) (ha : ¬ active t z) :
    ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalAt rate rewards C_star C_h t i z = 0 := by
  cases hp : PI t.val z with
  | none => simp [ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalAt, hp]
  | some past =>
    cases hc : cell t z with
    | none => simp [ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalAt, hc]
    | some c =>
      have hnot : ¬ ((RecordedQueueRun.run Q past).overflow = false ∧ c.enabled = true) := by
        rintro ⟨ho, he⟩
        apply ha
        refine ⟨ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q past), c, ?_, hc, ho, he⟩
        simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hp]
      simp only [ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalAt, hp, hc]
      cases ho : (RecordedQueueRun.run Q past).overflow <;>
        cases he : c.enabled <;>
        simp_all [RecordedQueueRun.acceptedRecord, RecordedQueueRun.acceptedArrival]

private theorem arrival_zero_of_inactive (t : Fin p.T) (z : X)
    (ha : ¬ active t z) : arrival t z = 0 := by
  unfold ReferenceOriginalCalendarFixedIDNonfirstLearning.weightedAcceptedArrival
  simp only [acceptedArrival_eq_zero_of_inactive rate rewards C_star C_h t _ z ha,
    mul_zero, Finset.sum_const_zero]

/-- Every original date is before launch, the empty launch boundary, or one
append to the complete actual numerical word. -/
private theorem calendar_prefix_step (t : Fin p.T) (z : X) :
    (PI t.val z = none ∧ PI (t.val + 1) z = none) ∨
    (PI t.val z = none ∧ PI (t.val + 1) z = some []) ∨
    ∃ past c, PI t.val z = some past ∧ cell t z = some c ∧
      PI (t.val + 1) z = some (past ++ [c]) := by
  have hcells := ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_cells
    rate rewards C_star C_h z
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
    simp only [hl] at hcells
    exact Or.inl ⟨hcells.2.2 _, hcells.2.2 _⟩
  | some state =>
    simp only [hl] at hcells
    obtain ⟨L, hlen, hmap, hpref, _⟩ := hcells
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    change L.length = R.length at hlen
    change R.map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = L.map some at hmap
    change ∀ h, h ≤ R.length → PI (s + h) z = some (L.take h) at hpref
    have hRlen : R.length = p.T - s :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
    have hbefore (n : ℕ) (hn : n < s) : PI n z = none := by
      apply (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_no_launch
        rate rewards C_star C_h n z ?_).1
      intro hby
      exact (not_le_of_gt hn) hby.2
    by_cases ht : t.val < s
    · by_cases hn : t.val + 1 < s
      · exact Or.inl ⟨hbefore _ ht, hbefore _ hn⟩
      · have heq : t.val + 1 = s := by omega
        right; left
        refine ⟨hbefore _ ht, ?_⟩
        simpa only [Nat.add_zero, List.take_zero, heq] using hpref 0 (Nat.zero_le _)
    · have hs : s ≤ t.val := by omega
      have hk : t.val - s < R.length := by rw [hRlen]; omega
      have hnext : t.val + 1 - s ≤ R.length := by rw [hRlen]; omega
      have hidx : t.val + 1 - s = (t.val - s) + 1 := by omega
      have hcellmap := congrArg (fun xs : List (Option (RecordedQueueRun.RoundInput p.K)) =>
        xs[t.val - s]?) hmap
      have hkL : t.val - s < L.length := by omega
      have hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate R[t.val - s] =
          some L[t.val - s] := by
        simpa only [List.getElem?_map, List.getElem?_eq_getElem hk,
          List.getElem?_eq_getElem hkL, Option.map_some, Option.some.injEq] using hcellmap
      have hactual : cell t z = some L[t.val - s] := by
        unfold ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt ReferenceSourcePrefixHistoryFiltration.actualRecord
        rw [ite_eq_left hs, List.getElem?_eq_getElem hk, Option.bind_some]
        exact hc
      have hp : PI t.val z = some (L.take (t.val - s)) := by
        simpa only [Nat.add_sub_of_le hs] using hpref (t.val - s) (Nat.le_of_lt hk)
      have hn : PI (t.val + 1) z = some (L.take (t.val - s) ++ [L[t.val - s]]) := by
        have htaken := hpref (t.val + 1 - s) hnext
        rw [Nat.add_sub_of_le (by omega : s ≤ t.val + 1), hidx,
          List.take_add_one, List.getElem?_eq_getElem hkL, Option.toList_some] at htaken
        exact htaken
      exact Or.inr (Or.inr ⟨_, _, hp, hactual, hn⟩)

private theorem initial_square_zero :
    RecordedWeightedDrift.weightedSquarePotential p.m Q
      (RecordedQueueRun.run Q ([] : List (RecordedQueueRun.RoundInput p.K))) = 0 := by
  simp [RecordedWeightedDrift.weightedSquarePotential, StoppedQueueBound.normalizedBacklog,
    RecordedQueueRun.run, RecordedQueueRun.execute, RecordedQueueRun.initialState]

/-- Inactive dates preserve the actual full-prefix potential, including
prelaunch boundaries. Overflow is tested before the current update. -/
public theorem deltaV_eq_zero_of_inactive (t : Fin p.T) (z : X)
    (ha : ¬ active t z) : DV t z = 0 := by
  rcases calendar_prefix_step rate rewards C_star C_h t z with h | h | h
  · simp [ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV, ReferenceOriginalCalendarLiveCollectionWeightedDrift.V, h.1, h.2]
  · simp [ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV, ReferenceOriginalCalendarLiveCollectionWeightedDrift.V, h.1, h.2, initial_square_zero rate]
  · obtain ⟨past, c, hp, hc, hn⟩ := h
    have hstop : c.enabled = false ∨ (RecordedQueueRun.run Q past).overflow = true := by
      cases he : c.enabled <;> cases ho : (RecordedQueueRun.run Q past).overflow
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact False.elim (ha ⟨ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q past), c, by
            simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hp],
          hc, ho, he⟩)
      · exact Or.inr rfl
    simp only [ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV, ReferenceOriginalCalendarLiveCollectionWeightedDrift.V, hp, hn, Option.elim_some,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]
    exact sub_eq_zero.mpr
      (RecordedWeightedDrift.weightedSquarePotential_step_eq_of_disabled_or_overflowed
        p.m Q (RecordedQueueRun.run Q past) c hstop)

private theorem branch_indicator_sum (t : Fin p.T) (f : X → ℝ)
    (hf : ∀ z, ¬ active t z → f z = 0) (z : X) :
    (∑ j : Fin 4, (retainedBranch rate rewards C_star C_h t j).indicator f z) = f z := by
  by_cases ha : active t z
  · obtain ⟨j, hj, hu⟩ := (retainedBranch_unique rate rewards C_star C_h t z).mp ha
    rw [Fintype.sum_eq_single j]
    · exact Set.indicator_of_mem hj f
    · intro k hk
      exact Set.indicator_of_notMem (fun h => hk (hu k h)) f
  · have hn (j : Fin 4) : z ∉ retainedBranch rate rewards C_star C_h t j :=
      fun hj => ha (branch_mem_active rate rewards C_star C_h t j z hj)
    simp only [Set.indicator_of_notMem (hn _), Finset.sum_const_zero, hf z ha]

private theorem branch_integral_sum (control0 : TimeControl p)
    (ids : CompletePublicTable.IDArray p) (t : Fin p.T) (f : X → ℝ)
    (hf : ∀ z, ¬ active t z → f z = 0)
    (hi : ∀ j : Fin 4, IntegrableOn f
      (ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
        retainedBranch rate rewards C_star C_h t j) μ) :
    IntegrableOn f (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) μ ∧
    (∫ z in ReferenceFixedIDSourceSection.fixedIDSourceSection ids, f z ∂μ) =
      ∑ j : Fin 4, ∫ z in ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
        retainedBranch rate rewards C_star C_h t j, f z ∂μ := by
  let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  have hm (j : Fin 4) := branch_measurable rate rewards C_star C_h control0 t j
  have hbi (j : Fin 4) : IntegrableOn
      ((retainedBranch rate rewards C_star C_h t j).indicator f) D μ := by
    rw [IntegrableOn, integrable_indicator_iff (hm j), IntegrableOn, Measure.restrict_restrict (hm j),
      Set.inter_comm]
    exact hi j
  have heq : (fun z => ∑ j : Fin 4,
      (retainedBranch rate rewards C_star C_h t j).indicator f z) = f :=
    funext (branch_indicator_sum rate rewards C_star C_h t f hf)
  refine ⟨?_, ?_⟩
  · rw [← heq]
    exact integrable_finsetSum _ (fun j _ => hbi j)
  · rw [← heq]
    rw [integral_finsetSum _ (fun j _ => hbi j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [heq, setIntegral_indicator (hm j)]

private theorem branch_mass_sum_le (control0 : TimeControl p)
    (ids : CompletePublicTable.IDArray p) (t : Fin p.T) :
    (∑ j : Fin 4, (μ).real (ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
      retainedBranch rate rewards C_star C_h t j)) ≤
      (μ).real (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) := by
  let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  have hd : Pairwise (fun j k : Fin 4 => Disjoint
      (D ∩ retainedBranch rate rewards C_star C_h t j)
      (D ∩ retainedBranch rate rewards C_star C_h t k)) := by
    intro j k hne
    apply Set.disjoint_left.mpr
    rintro z ⟨_, hj⟩ ⟨_, hk⟩
    have ha := branch_mem_active rate rewards C_star C_h t j z hj
    obtain ⟨i, _, hu⟩ := (retainedBranch_unique rate rewards C_star C_h t z).mp ha
    exact hne ((hu j hj).trans (hu k hk).symm)
  rw [← measureReal_iUnion_fintype hd (fun j =>
    (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).inter
      (branch_measurable rate rewards C_star C_h control0 t j))]
  exact measureReal_mono (Set.iUnion_subset fun _ => Set.inter_subset_left)

private theorem branch_learning_bounds (control0 : TimeControl p)
    (ids : CompletePublicTable.IDArray p) (S : ProductSet p.K p.m)
    (t : Fin p.T) (j : Fin 4) :
    let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
      retainedBranch rate rewards C_star C_h t j
    IntegrableOn (DV t) D μ ∧ IntegrableOn (cost t.val) D μ ∧
    IntegrableOn (arrival t) D μ ∧
    (∫ z in D, DV t z ∂μ) ≤ -(11 / 2 : ℝ) * (∫ z in D, cost t.val z ∂μ) +
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) * (μ).real D ∧
    (∫ z in D, arrival t z ∂μ) ≤ (p.m : ℝ) * (μ).real D := by
  have hm (k : Fin 4) :=
    (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).inter
      (branch_measurable rate rewards C_star C_h control0 t k)
  have cv (k : Fin 4) (f : X → ℝ)
      (h : Integrable ((ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
        retainedBranch rate rewards C_star C_h t k).indicator f) μ) :
      IntegrableOn f (ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
        retainedBranch rate rewards C_star C_h t k) μ :=
    (integrable_indicator_iff (hm k)).mp h
  fin_cases j
  · obtain ⟨hδ, hw, _, _, _, hδb, hwb, _, hc⟩ :=
      ReferenceOriginalCalendarFirstFixedIDLearningTransport.first_fixedID_source_transport rate rewards C_star C_h control0 ids S t
    have hwae : ReferenceOriginalCalendarFirstFixedIDLearningTransport.firstWeightedArrival rate rewards C_star C_h t =ᵐ[(μ).restrict
        (ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
          retainedBranch rate rewards C_star C_h t 0)] arrival t := by
      filter_upwards [ae_restrict_mem (hm 0)] with z hz
      exact (first_observers_align rate rewards C_star C_h S t z hz.2).1
    have hcae : cost t.val =ᵐ[(μ).restrict
        (ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
          retainedBranch rate rewards C_star C_h t 0)] (fun _ => (0 : ℝ)) := by
      filter_upwards [ae_restrict_mem (hm 0)] with z hz
      exact hc z hz
    refine ⟨hδ, (integrable_const (0 : ℝ)).congr hcae.symm,
      hw.congr hwae, ?_, ?_⟩
    · have hz := integral_congr_ae hcae
      simp only [integral_zero] at hz
      simp only [retainedBranch, Matrix.cons_val_zero, Matrix.cons_val_zero'] at hz ⊢
      rw [hz, mul_zero, zero_add]
      exact hδb
    · exact (integral_congr_ae hwae).symm.trans_le hwb
  · obtain ⟨hδ, hc, hb⟩ := ReferenceOriginalCalendarFixedIDNonfirstLearning.live_retained_weightedSquare_fixedID
      rate rewards C_star C_h control0 ids t
    obtain ⟨hw, hwb⟩ := ReferenceOriginalCalendarFixedIDNonfirstLearning.live_weightedArrival_fixedID rate rewards C_star C_h control0 ids t
    exact ⟨cv 1 _ hδ, cv 1 _ hc, cv 1 _ hw, hb, hwb⟩
  · obtain ⟨hδ, hc, hb⟩ := ReferenceOriginalCalendarFixedIDNonfirstLearning.renewedBirth_retained_weightedSquare_fixedID
      rate rewards C_star C_h control0 ids t
    obtain ⟨hw, hwb⟩ := ReferenceOriginalCalendarFixedIDNonfirstLearning.renewedBirth_weightedArrival_fixedID rate rewards C_star C_h control0 ids t
    exact ⟨cv 2 _ hδ, cv 2 _ hc, cv 2 _ hw, hb, hwb⟩
  · obtain ⟨hδ, hc, hb⟩ := ReferenceOriginalCalendarFixedIDNonfirstLearning.collection_retained_weightedSquare_fixedID
      rate rewards C_star C_h control0 ids t
    obtain ⟨hw, hwb⟩ := ReferenceOriginalCalendarFixedIDNonfirstLearning.collection_weightedArrival_fixedID rate rewards C_star C_h control0 ids t
    exact ⟨cv 3 _ hδ, cv 3 _ hc, cv 3 _ hw, hb, hwb⟩

/-- Retained COST is masked by the original active-update test. -/
public def retainedCostAt (t : Fin p.T) : X → ℝ :=
  {z | active t z}.indicator (cost t.val)

/-- The localized four-branch drift and weighted-arrival estimates. Branch
masses are charged once per date on the literal fixed-ID section. -/
public theorem calendar_fixedID_drift_and_arrival (control0 : TimeControl p)
    (ids : CompletePublicTable.IDArray p) (S : ProductSet p.K p.m) (t : Fin p.T) :
    let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
    IntegrableOn (DV t) D μ ∧
    IntegrableOn (retainedCostAt rate rewards C_star C_h t) D μ ∧
    IntegrableOn (arrival t) D μ ∧
    (∫ z in D, DV t z ∂μ) ≤ -(11 / 2 : ℝ) *
      (∫ z in D, retainedCostAt rate rewards C_star C_h t z ∂μ) +
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) * (μ).real D ∧
    (∫ z in D, arrival t z ∂μ) ≤ (p.m : ℝ) * (μ).real D := by
  let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  have hb := branch_learning_bounds rate rewards C_star C_h control0 ids S t
  have hcost (j : Fin 4) : retainedCostAt rate rewards C_star C_h t =ᵐ[
      (μ).restrict (D ∩ retainedBranch rate rewards C_star C_h t j)] cost t.val := by
    filter_upwards [ae_restrict_mem ((ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).inter
      (branch_measurable rate rewards C_star C_h control0 t j))] with z hz
    exact Set.indicator_of_mem (s := {z | active t z})
      (branch_mem_active rate rewards C_star C_h t j z hz.2) (cost t.val)
  have hd := branch_integral_sum rate rewards C_star C_h control0 ids t (DV t)
    (fun z hz => deltaV_eq_zero_of_inactive rate rewards C_star C_h t z hz)
    (fun j => (hb j).1)
  have hc := branch_integral_sum rate rewards C_star C_h control0 ids t
    (retainedCostAt rate rewards C_star C_h t)
    (fun z hz => Set.indicator_of_notMem (s := {z | active t z}) hz (cost t.val))
    (fun j => (hb j).2.1.congr (hcost j).symm)
  have hw := branch_integral_sum rate rewards C_star C_h control0 ids t (arrival t)
    (fun z hz => arrival_zero_of_inactive rate rewards C_star C_h t z hz)
    (fun j => (hb j).2.2.1)
  have hmass := branch_mass_sum_le rate rewards C_star C_h control0 ids t
  have hR : 0 ≤ CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m := by
    have hmk : (p.m : ℝ) ≤ p.K := by exact_mod_cast Nat.le_of_lt p.m_lt_K
    have hK : (0 : ℝ) ≤ p.K := Nat.cast_nonneg _
    have hdiff : 0 ≤ 2 * (p.K : ℝ) - p.m := by linarith only [hmk, hK]
    unfold CanonicalRecordingRates.R
    positivity
  refine ⟨hd.1, hc.1, hw.1, ?_, ?_⟩
  · rw [hd.2, hc.2]
    calc
      _ ≤ ∑ j : Fin 4, (-(11 / 2 : ℝ) *
          (∫ z in D ∩ retainedBranch rate rewards C_star C_h t j, cost t.val z ∂μ) +
          (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) *
            (μ).real (D ∩ retainedBranch rate rewards C_star C_h t j)) :=
        Finset.sum_le_sum (fun j _ => (hb j).2.2.2.1)
      _ ≤ _ := by
        simp_rw [← integral_congr_ae (hcost _)]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass hR)
  · rw [hw.2]
    calc
      _ ≤ ∑ j : Fin 4, (p.m : ℝ) *
          (μ).real (D ∩ retainedBranch rate rewards C_star C_h t j) :=
        Finset.sum_le_sum (fun j _ => (hb j).2.2.2.2)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg _)

private theorem branch_signed (control0 : TimeControl p)
    (ids : CompletePublicTable.IDArray p) (S : ProductSet p.K p.m)
    (t : Fin p.T) (j : Fin 4) :
    let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
      retainedBranch rate rewards C_star C_h t j
    IntegrableOn (ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap rate rewards C_star C_h S t) D μ ∧
    IntegrableOn (ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRewardGap rate rewards C_star C_h S t) D μ ∧
    IntegrableOn (ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor rate rewards C_star C_h S t) D μ ∧
    (∫ z in D, ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRewardGap rate rewards C_star C_h S t z ∂μ) ≤
      (∫ z in D, ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap rate rewards C_star C_h S t z ∂μ) +
      (∫ z in D, ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor rate rewards C_star C_h S t z ∂μ) := by
  have hm (k : Fin 4) :=
    (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).inter
      (branch_measurable rate rewards C_star C_h control0 t k)
  fin_cases j
  · exact first_signed_fixedID rate rewards C_star C_h control0 ids S t
  · obtain ⟨hr, hh, hf, hb⟩ := ReferenceOriginalCalendarFixedIDNonfirstLearning.live_signedComparison_fixedID
      rate rewards C_star C_h control0 ids S t
    exact ⟨(integrable_indicator_iff (hm 1)).mp hr,
      (integrable_indicator_iff (hm 1)).mp hh, (integrable_indicator_iff (hm 1)).mp hf, hb⟩
  · obtain ⟨hr, hh, hf, hb⟩ := ReferenceOriginalCalendarFixedIDNonfirstLearning.renewedBirth_signedComparison_fixedID
      rate rewards C_star C_h control0 ids S t
    exact ⟨(integrable_indicator_iff (hm 2)).mp hr,
      (integrable_indicator_iff (hm 2)).mp hh, (integrable_indicator_iff (hm 2)).mp hf, hb⟩
  · obtain ⟨hr, hh, hf, hb⟩ := ReferenceOriginalCalendarFixedIDNonfirstLearning.collection_signedComparison_fixedID
      rate rewards C_star C_h control0 ids S t
    exact ⟨(integrable_indicator_iff (hm 3)).mp hr,
      (integrable_indicator_iff (hm 3)).mp hh, (integrable_indicator_iff (hm 3)).mp hf, hb⟩

/-- Signed comparison on the full fixed-ID section with the same raw,
rounded, and floor observers on all four branches. -/
public theorem calendar_fixedID_signed (control0 : TimeControl p)
    (ids : CompletePublicTable.IDArray p) (S : ProductSet p.K p.m) (t : Fin p.T) :
    let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
    IntegrableOn (ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap rate rewards C_star C_h S t) D μ ∧
    IntegrableOn (ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRewardGap rate rewards C_star C_h S t) D μ ∧
    IntegrableOn (ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor rate rewards C_star C_h S t) D μ ∧
    (∫ z in D, ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRewardGap rate rewards C_star C_h S t z ∂μ) ≤
      (∫ z in D, ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap rate rewards C_star C_h S t z ∂μ) +
      (∫ z in D, ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor rate rewards C_star C_h S t z ∂μ) := by
  have hb := branch_signed rate rewards C_star C_h control0 ids S t
  have hr := branch_integral_sum rate rewards C_star C_h control0 ids t
    (ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap rate rewards C_star C_h S t) (fun z hz => by
      simp [ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap,
        acceptedArrival_eq_zero_of_inactive rate rewards C_star C_h t _ z hz,
        arrival_zero_of_inactive rate rewards C_star C_h t z hz]) (fun j => (hb j).1)
  have hh := branch_integral_sum rate rewards C_star C_h control0 ids t
    (ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRewardGap rate rewards C_star C_h S t) (fun z hz => by
      exact Set.indicator_of_notMem (s := {z | active t z}) hz _) (fun j => (hb j).2.1)
  have hf := branch_integral_sum rate rewards C_star C_h control0 ids t
    (ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor rate rewards C_star C_h S t) (fun z hz => by
      exact Set.indicator_of_notMem (s := {z | active t z}) hz _) (fun j => (hb j).2.2.1)
  refine ⟨hr.1, hh.1, hf.1, ?_⟩
  rw [hr.2, hh.2, hf.2, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun j _ => (hb j).2.2.2)

private theorem sum_successive_difference (f : ℕ → ℝ) (n : ℕ) :
    (∑ t : Fin n, (f (t.val + 1) - f t.val)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    ring

private theorem V_zero (z : X) : ReferenceOriginalCalendarLiveCollectionWeightedDrift.V rate rewards C_star C_h 0 z = 0 := by
  unfold ReferenceOriginalCalendarLiveCollectionWeightedDrift.V ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
  split_ifs <;> simp [initial_square_zero rate]

private theorem V_nonneg (n : ℕ) (z : X) : 0 ≤ ReferenceOriginalCalendarLiveCollectionWeightedDrift.V rate rewards C_star C_h n z := by
  cases hp : PI n z with
  | none => simp [ReferenceOriginalCalendarLiveCollectionWeightedDrift.V, hp]
  | some past =>
    simp only [ReferenceOriginalCalendarLiveCollectionWeightedDrift.V, hp, Option.elim_some, RecordedWeightedDrift.weightedSquarePotential]
    exact Finset.sum_nonneg fun i _ => mul_nonneg
      (RecordedMarginalGrowth.state_theta_pos Q (RecordedQueueRun.run Q past) i
        (Nat.zero_lt_of_lt p.two_le_m) p.m_lt_K).le (sq_nonneg _)

/-- The finite localized telescope starts at the actual zero score/queue
prefix and includes the first overflow update before numerical freezing. -/
public theorem calendar_fixedID_finite_bounds (control0 : TimeControl p)
    (ids : CompletePublicTable.IDArray p) (S : ProductSet p.K p.m) :
    let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
    IntegrableOn (fun z => ∑ t : Fin p.T, retainedCostAt rate rewards C_star C_h t z) D μ ∧
    IntegrableOn (fun z => ∑ t : Fin p.T, arrival t z) D μ ∧
    (∫ z in D, ∑ t : Fin p.T, retainedCostAt rate rewards C_star C_h t z ∂μ) ≤
      (2 / 11 : ℝ) * (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) * p.T * (μ).real D ∧
    (∫ z in D, ∑ t : Fin p.T, arrival t z ∂μ) ≤
      (p.m : ℝ) * p.T * (μ).real D := by
  let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  have hb := calendar_fixedID_drift_and_arrival rate rewards C_star C_h control0 ids S
  have hci := integrable_finsetSum Finset.univ (fun t _ => (hb t).2.1)
  have hwi := integrable_finsetSum Finset.univ (fun t _ => (hb t).2.2.1)
  have hd : 0 ≤ ∑ t : Fin p.T, ∫ z in D, DV t z ∂μ := by
    rw [← integral_finsetSum _ (fun t _ => (hb t).1)]
    apply integral_nonneg
    intro z
    change 0 ≤ ∑ t : Fin p.T,
      (ReferenceOriginalCalendarLiveCollectionWeightedDrift.V rate rewards C_star C_h (t.val + 1) z - ReferenceOriginalCalendarLiveCollectionWeightedDrift.V rate rewards C_star C_h t.val z)
    rw [sum_successive_difference (fun n => ReferenceOriginalCalendarLiveCollectionWeightedDrift.V rate rewards C_star C_h n z), V_zero rate rewards C_star C_h z, sub_zero]
    exact V_nonneg rate rewards C_star C_h p.T z
  have hδ := Finset.sum_le_sum (s := Finset.univ) (fun t _ => (hb t).2.2.2.1)
  have hw := Finset.sum_le_sum (s := Finset.univ) (fun t _ => (hb t).2.2.2.2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hδ hw
  refine ⟨hci, hwi, ?_, ?_⟩
  · rw [integral_finsetSum _ (fun t _ => (hb t).2.1)]
    nlinarith only [hd, hδ]
  · rw [integral_finsetSum _ (fun t _ => (hb t).2.2.1)]
    calc
      _ ≤ _ := hw
      _ = _ := by ring

private theorem sum_suffix {s l n : ℕ} (h : s + l = n)
    (f : Fin n → ℝ) (g : Fin l → ℝ)
    (hpre : ∀ t, t.val < s → f t = 0)
    (hsuf : ∀ k : Fin l, f ⟨s + k.val, by omega⟩ = g k) :
    (∑ t, f t) = ∑ k, g k := by
  subst n
  rw [Fin.sum_univ_add]
  have hz : (∑ i : Fin s, f (Fin.castAdd l i)) = 0 :=
    Finset.sum_eq_zero (fun i _ => hpre _ i.isLt)
  rw [hz, zero_add]
  exact Finset.sum_congr rfl (fun k _ => hsuf k)

private theorem active_iff_prefix_cell (t : Fin p.T) (z : X)
    (past : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K)
    (hp : PI t.val z = some past) (hc : cell t z = some c) :
    active t z ↔ c.enabled = true ∧ (RecordedQueueRun.run Q past).overflow = false := by
  have hr : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate rewards C_star C_h t.val z = some
        (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q past)) := by
    simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hp]
  constructor
  · rintro ⟨o, c', ho, hc', hclear, hen⟩
    have heq := Option.some.inj (ho.symm.trans hr)
    have hceq := Option.some.inj (hc'.symm.trans hc)
    subst o; subst c'
    exact ⟨hen, hclear⟩
  · rintro ⟨hen, hclear⟩
    exact ⟨_, c, hr, hc, hclear, hen⟩

/-- The three complete-word observers are the finite original-calendar
sums, with no reset at installation or grid boundaries. -/
public theorem original_calendar_sums (S : ProductSet p.K p.m) (z : X) :
    ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarBacklogCost rate rewards C_star C_h z =
      ∑ t : Fin p.T, retainedCostAt rate rewards C_star C_h t z ∧
    ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarWeightedRawArrival rate rewards C_star C_h z =
      ∑ t : Fin p.T, arrival t z ∧
    ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarRawGap rate rewards C_star C_h S z =
      ∑ t : Fin p.T, ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap rate rewards C_star C_h S t z := by
  have hcells := ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_cells
    rate rewards C_star C_h z
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
    simp only [hl] at hcells
    have hactive (t : Fin p.T) : ¬ active t z := by
      rintro ⟨o, c, hp, _, _, _⟩
      simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hcells.2.2] at hp
    simp [ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarBacklogCost, ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarWeightedRawArrival,
      ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarRawGap, hcells.2.2, retainedCostAt, hactive,
      ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap, ReferenceOriginalCalendarFixedIDNonfirstLearning.weightedAcceptedArrival, ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalAt]
  | some state =>
    simp only [hl] at hcells
    obtain ⟨L, hlen, hmap, hpref, _⟩ := hcells
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    change L.length = R.length at hlen
    change R.map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = L.map some at hmap
    change ∀ h, h ≤ R.length → PI (s + h) z = some (L.take h) at hpref
    have hspan : s + L.length = p.T := by
      have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
      have hr := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
      change R.length = p.T - s at hr
      omega
    have hterminal : PI p.T z = some L := by
      simpa only [← hspan, List.take_length] using hpref L.length (by omega)
    have hpre (t : Fin p.T) (ht : t.val < s) : PI t.val z = none ∧ ¬ active t z := by
      have hp : PI t.val z = none :=
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_no_launch
          rate rewards C_star C_h t.val z (fun h => (not_le_of_gt ht) h.2)).1
      refine ⟨hp, ?_⟩
      rintro ⟨o, c, hr, _, _, _⟩
      simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hp] at hr
    have hsuf (k : Fin L.length) :
        PI (s + k.val) z = some (L.take k.val) ∧
        cell ⟨s + k.val, by omega⟩ z = some L[k.val] := by
      refine ⟨hpref k.val (by omega), ?_⟩
      have hk : k.val < R.length := by omega
      have hmapk := congrArg (fun xs : List (Option (RecordedQueueRun.RoundInput p.K)) => xs[k.val]?) hmap
      have hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate R[k.val] = some L[k.val] := by
        simpa only [List.getElem?_map, List.getElem?_eq_getElem hk,
          List.getElem?_eq_getElem k.isLt, Option.map_some, Option.some.injEq] using hmapk
      change ((if s ≤ s + k.val then R[s + k.val - s]? else none).bind
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)) = some L[k.val]
      rw [ite_eq_left (Nat.le_add_right s k.val), Nat.add_sub_cancel_left,
        List.getElem?_eq_getElem hk, Option.bind_some]
      exact hc
    have hcost := sum_suffix hspan
      (fun t => retainedCostAt rate rewards C_star C_h t z)
      (fun k : Fin L.length => if L[k.val].enabled = true ∧
          (RecordedQueueRun.run Q (L.take k.val)).overflow = false then
        ∑ i : Fin p.K, RecordedQueueSummation.runMarginal Q p.m L k.val i *
          StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q (L.take k.val)) i
        else 0) (fun t ht => by simp [retainedCostAt, (hpre t ht).2]) (fun k => by
          have ha := active_iff_prefix_cell rate rewards C_star C_h
            ⟨s + k.val, by omega⟩ z _ _ (hsuf k).1 (hsuf k).2
          simp [retainedCostAt, Set.indicator, ha, ReferenceOriginalCalendarLiveCollectionWeightedDrift.C, (hsuf k).1,
            RecordedWeightedDrift.weightedBacklog, RecordedQueueSummation.runMarginal])
    have hw := sum_suffix hspan (fun t => arrival t z)
      (fun k : Fin L.length => ∑ i : Fin p.K, RecordedQueueSummation.runMarginal Q p.m L k.val i *
        ((RecordedQueueRun.acceptedArrival (RecordedQueueRun.acceptedRecord Q
          (RecordedQueueRun.run Q (L.take k.val)) L[k.val] i) : ℝ) / (rate.n : ℝ)))
      (fun t ht => arrival_zero_of_inactive rate rewards C_star C_h t z (hpre t ht).2)
      (fun k => by simp [ReferenceOriginalCalendarFixedIDNonfirstLearning.weightedAcceptedArrival, ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalAt, ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt,
        (hsuf k).1, (hsuf k).2, RecordedQueueSummation.runMarginal])
    have hg := sum_suffix hspan
      (fun t => ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap rate rewards C_star C_h S t z)
      (fun k : Fin L.length =>
        (∑ i ∈ S.1, (RecordedQueueRun.acceptedArrival (RecordedQueueRun.acceptedRecord Q
          (RecordedQueueRun.run Q (L.take k.val)) L[k.val] i) : ℝ) / (rate.n : ℝ)) -
        ∑ i : Fin p.K, RecordedQueueSummation.runMarginal Q p.m L k.val i *
          ((RecordedQueueRun.acceptedArrival (RecordedQueueRun.acceptedRecord Q
            (RecordedQueueRun.run Q (L.take k.val)) L[k.val] i) : ℝ) / (rate.n : ℝ)))
      (fun t ht => by simp [ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap,
        acceptedArrival_eq_zero_of_inactive rate rewards C_star C_h t _ z (hpre t ht).2,
        arrival_zero_of_inactive rate rewards C_star C_h t z (hpre t ht).2])
      (fun k => by simp [ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap, ReferenceOriginalCalendarFixedIDNonfirstLearning.weightedAcceptedArrival,
        ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalAt, ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt, (hsuf k).1, (hsuf k).2,
        RecordedQueueSummation.runMarginal])
    exact ⟨by simpa only [ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarBacklogCost, hterminal, Fin.getElem_fin,
      ReferenceCompleteOriginalCalendarRawLearningComparison.calendarQueue] using hcost.symm,
      by simpa only [ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarWeightedRawArrival, hterminal, Fin.getElem_fin, ReferenceFirstLaunchNumericalCell.queueParameters, ReferenceCompleteOriginalCalendarRawLearningComparison.calendarQueue] using hw.symm,
      by simpa only [ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarRawGap, hterminal, Fin.getElem_fin, ReferenceFirstLaunchNumericalCell.queueParameters, ReferenceCompleteOriginalCalendarRawLearningComparison.calendarQueue] using hg.symm⟩

private theorem payload_rate_le_one (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin p.K) : payload.rate i ≤ 1 :=
  (Finset.single_le_sum (fun j _ =>
    (CanonicalRecordingRates.xi_pos p rate.eta.property payload.anchor j).le)
      (Finset.mem_univ i)).trans
    (CanonicalRecordingRates.sum_xi_le_one p rate.eta.property rate.sourceCap
      payload.anchor payload.anchor_pos)

private theorem cell_rate_le_one (t : Fin p.T) (z : X)
    (c : RecordedQueueRun.RoundInput p.K) (hc : cell t z = some c) (i : Fin p.K) :
    c.rate i ≤ 1 := by
  obtain ⟨r, _, hread⟩ := Option.bind_eq_some_iff.mp hc
  change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).or
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r) = some c at hread
  cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
  | none =>
    simp only [hl, Option.none_or] at hread
    obtain ⟨payload, _, _, _, _, _, _, _, _, _, hr, _⟩ :=
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 r c hread
    rw [congrFun hr i]
    exact payload_rate_le_one rate payload i
  | some c' =>
    have heq : c' = c := Option.some.inj (by simpa only [hl, Option.some_or] using hread)
    subst c'
    obtain ⟨_, selected, _, _, hr, _⟩ :=
      ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical 0 r c hl
    rw [congrFun hr i]
    exact payload_rate_le_one rate selected.view.payload i

private theorem floor_le (S : ProductSet p.K p.m) (t : Fin p.T) (z : X) :
    ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor rate rewards C_star C_h S t z ≤ (p.m : ℝ) / rate.n := by
  have hn : (0 : ℝ) < rate.n := Nat.cast_pos.mpr ((Q).n_pos)
  by_cases ha : active t z
  · unfold ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor
    rw [Set.indicator_of_mem (s := {z | active t z}) ha]
    cases hc : cell t z with
    | none => simp only; positivity
    | some c =>
      simp only
      calc
        _ ≤ ∑ i ∈ S.1, (1 : ℝ) / rate.n := Finset.sum_le_sum fun i _ =>
          div_le_div_of_nonneg_right (cell_rate_le_one rate rewards C_star C_h t z c hc i) hn.le
        _ = _ := by
          have hcard : S.1.card = p.m := (Finset.mem_powersetCard.mp S.2).2
          simp only [Finset.sum_const, nsmul_eq_mul, hcard]
          ring
  · simp only [ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor, Set.indicator_of_notMem (s := {z | active t z}) ha]
    positivity

/-- Literal numerical raw-learning budget for the same fixed-ID section. -/
public def rawLearningBudget : ℝ :=
  (2 * Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ) / 16) / rate.eta.val +
    (16 * (p.m : ℝ) ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p +
      32 * (p.m : ℝ)) * rate.eta.val * p.T

private theorem raw_pointwise_le (S : ProductSet p.K p.m) (z : X) :
    ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarRawGap rate rewards C_star C_h S z ≤
      (2 * Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ) / 16) / rate.eta.val +
      16 * (p.m : ℝ) ^ 2 * rate.eta.val * p.T +
      8 * rate.eta.val * (ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarBacklogCost rate rewards C_star C_h z +
        ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarWeightedRawArrival rate rewards C_star C_h z) := by
  have hcmp := ReferenceCompleteOriginalCalendarRawLearningComparison.complete_original_calendar_raw_learning_comparison rate rewards C_star C_h S z
  have he := rate.eta.property
  have hl := RecordedPotentialStep.potentialLambda_pos Q
  have hlog : 0 ≤ Real.log (Nat.choose p.K p.m : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt p.m_lt_K)
  have hdiv : Real.log (Nat.choose p.K p.m : ℝ) /
      RecordedPotentialStep.potentialLambda Q ≤ 2 * Real.log (Nat.choose p.K p.m : ℝ) / rate.eta.val := by
    apply (div_le_div_iff₀ hl he).mpr
    have hh := RecordedPotentialStep.eta_div_two_le_potentialLambda Q
    change rate.eta.val / 2 ≤ _ at hh
    nlinarith only [mul_le_mul_of_nonneg_left hh hlog]
  have hlen : ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length : ℝ) ≤ p.T := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    exact_mod_cast Nat.sub_le p.T (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
  have hquad : 16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q *
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length : ℝ) ≤
      16 * (p.m : ℝ) ^ 2 * rate.eta.val * p.T := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left (RecordedPotentialStep.potentialLambda_le_eta Q)
      (by positivity)) hlen (by positivity) (by positivity)
  cases hc : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
    simp only [hc] at hcmp
    rw [hcmp.1, hcmp.2.1, hcmp.2.2]
    positivity
  | some state =>
    simp only [hc] at hcmp
    obtain ⟨_, _, _, _, hb⟩ := hcmp
    calc
      _ ≤ _ := hb
      _ ≤ _ := by
        have hbase : 2 * Real.log (Nat.choose p.K p.m : ℝ) / rate.eta.val +
            (p.m : ℝ) / (16 * rate.eta.val) =
            (2 * Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ) / 16) / rate.eta.val := by ring
        linarith only [hdiv, hquad, hbase]

/-- All numerical learning observables are integrable on the actual section;
the complete-word COST/W/raw bounds are obtained before atom cancellation. -/
public theorem localized_learning_bounds (control0 : TimeControl p)
    (ids : CompletePublicTable.IDArray p) (S : ProductSet p.K p.m) :
    let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
    IntegrableOn (ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarBacklogCost rate rewards C_star C_h) D μ ∧
    IntegrableOn (ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarWeightedRawArrival rate rewards C_star C_h) D μ ∧
    IntegrableOn (ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarRawGap rate rewards C_star C_h S) D μ ∧
    IntegrableOn (retainedRoundedLearningSum rate rewards C_star C_h S) D μ ∧
    (∫ z in D, ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarBacklogCost rate rewards C_star C_h z ∂μ) ≤
      (2 / 11 : ℝ) * (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) * p.T * (μ).real D ∧
    (∫ z in D, ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarWeightedRawArrival rate rewards C_star C_h z ∂μ) ≤
      (p.m : ℝ) * p.T * (μ).real D ∧
    (∫ z in D, ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarRawGap rate rewards C_star C_h S z ∂μ) ≤
      rawLearningBudget rate * (μ).real D ∧
    (∫ z in D, retainedRoundedLearningSum rate rewards C_star C_h S z ∂μ) ≤
      (rawLearningBudget rate + (p.m : ℝ) * p.T / (rate.eta.val * ConstructorDimensions.D p)) * (μ).real D := by
  let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  have hs := calendar_fixedID_signed rate rewards C_star C_h control0 ids S
  have hb := calendar_fixedID_finite_bounds rate rewards C_star C_h control0 ids S
  have hcEq : ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarBacklogCost rate rewards C_star C_h =
      (fun z => ∑ t : Fin p.T, retainedCostAt rate rewards C_star C_h t z) :=
    funext (fun z => (original_calendar_sums rate rewards C_star C_h S z).1)
  have hwEq : ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarWeightedRawArrival rate rewards C_star C_h =
      (fun z => ∑ t : Fin p.T, arrival t z) :=
    funext (fun z => (original_calendar_sums rate rewards C_star C_h S z).2.1)
  have hrEq : ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarRawGap rate rewards C_star C_h S =
      (fun z => ∑ t : Fin p.T, ReferenceOriginalCalendarFixedIDNonfirstLearning.acceptedArrivalComparatorGap rate rewards C_star C_h S t z) :=
    funext (fun z => (original_calendar_sums rate rewards C_star C_h S z).2.2)
  rw [← hcEq, ← hwEq] at hb
  have hri : IntegrableOn (ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarRawGap rate rewards C_star C_h S) D μ := by
    rw [hrEq]
    exact integrable_finsetSum _ (fun t _ => (hs t).1)
  have hhi : IntegrableOn (retainedRoundedLearningSum rate rewards C_star C_h S) D μ :=
    integrable_finsetSum _ (fun t _ => (hs t).2.1)
  have hfi : IntegrableOn (fun z => ∑ t : Fin p.T,
      ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor rate rewards C_star C_h S t z) D μ :=
    integrable_finsetSum _ (fun t _ => (hs t).2.2.1)
  have hraw := integral_mono hri
    (((integrable_const _).add (integrable_const _)).add
      ((hb.1.add hb.2.1).const_mul (8 * rate.eta.val)))
    (raw_pointwise_le rate rewards C_star C_h S)
  rw [integral_add' ((integrable_const _).add (integrable_const _)) ((hb.1.add hb.2.1).const_mul _),
    integral_add' (integrable_const _) (integrable_const _),
    integral_const_mul (8 * rate.eta.val)
      (ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarBacklogCost rate rewards C_star C_h +
        ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarWeightedRawArrival rate rewards C_star C_h),
    integral_add' hb.1 hb.2.1] at hraw
  simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ] at hraw
  have hrawb : (∫ z in D, ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarRawGap rate rewards C_star C_h S z ∂μ) ≤
      rawLearningBudget rate * (μ).real D := by
    have hc := mul_le_mul_of_nonneg_left hb.2.2.1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) rate.eta.property.le)
    have hw := mul_le_mul_of_nonneg_left hb.2.2.2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) rate.eta.property.le)
    unfold rawLearningBudget
    nlinarith only [hraw, hc, hw]
  have hfloor : (∫ z in D, ∑ t : Fin p.T,
      ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRateFloor rate rewards C_star C_h S t z ∂μ) ≤
      ((p.m : ℝ) * p.T / (rate.eta.val * ConstructorDimensions.D p)) * (μ).real D := by
    have hh := integral_mono hfi (integrable_const ((p.m : ℝ) * p.T / rate.n))
      (fun z => calc
        _ ≤ ∑ _t : Fin p.T, (p.m : ℝ) / rate.n :=
          Finset.sum_le_sum (fun t _ => floor_le rate rewards C_star C_h S t z)
        _ = _ := by simp [nsmul_eq_mul]; ring)
    simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
      rate.n_scale, mul_comm ((μ).real D)] using hh
  refine ⟨hb.1, hb.2.1, hri, hhi, hb.2.2.1, hb.2.2.2, hrawb, ?_⟩
  have hsign := Finset.sum_le_sum (s := Finset.univ) (fun t _ => (hs t).2.2.2)
  rw [← integral_finsetSum _ (fun t _ => (hs t).2.1), Finset.sum_add_distrib,
    ← integral_finsetSum _ (fun t _ => (hs t).1),
    ← integral_finsetSum _ (fun t _ => (hs t).2.2.1), ← hrEq] at hsign
  change (∫ z in D, ∑ t : Fin p.T, ReferenceOriginalCalendarFixedIDNonfirstLearning.retainedRewardGap rate rewards C_star C_h S t z ∂μ) ≤ _
  nlinarith only [hsign, hrawb, hfloor]

private theorem section_integrable (ids : CompletePublicTable.IDArray p) (f : X → ℝ)
    (hf : IntegrableOn f (ReferenceFixedIDSourceSection.fixedIDSourceSection ids) μ) :
    Integrable f (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids) := by
  have hp := ReferenceFixedIDSourceSection.idArrayAtom_positive (p := p) ids
  have ha : CompletePublicTable.idArrayMeasure p {ids} ≠ 0 := by
    intro h
    simp [Measure.real, h] at hp
  rw [IntegrableOn, ReferenceFixedIDSourceSection.sourceInputLaw_restrict_fixedIDSourceSection] at hf
  exact (integrable_smul_measure ha (measure_ne_top _ _)).mp hf

private theorem section_bound (ids : CompletePublicTable.IDArray p) (f : X → ℝ) (c : ℝ)
    (hf : (∫ z in ReferenceFixedIDSourceSection.fixedIDSourceSection ids, f z ∂μ) ≤
      c * (μ).real (ReferenceFixedIDSourceSection.fixedIDSourceSection ids)) :
    (∫ z, f z ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw ids) ≤ c := by
  rw [ReferenceFixedIDSourceSection.sourceInputLaw_setIntegral_fixedIDSourceSection,
    ReferenceFixedIDSourceSection.sourceInputLaw_real_fixedIDSourceSection] at hf
  exact le_of_mul_le_mul_left (hf.trans_eq (mul_comm _ _))
    (ReferenceFixedIDSourceSection.idArrayAtom_positive (p := p) ids)

/-- EVERY original ID array, under the literal fixed-ID law retaining all
whole rows and all extended private coordinates. This is an internal learning
estimate, separate from logical auxiliary and physical regret. -/
public theorem fixedID_learning_mean (control0 : TimeControl p)
    (ids : CompletePublicTable.IDArray p) (S : ProductSet p.K p.m) :
    let ν := ReferenceFixedIDSourceSection.fixedIDSourceLaw ids
    Integrable (ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarBacklogCost rate rewards C_star C_h) ν ∧
    Integrable (ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarWeightedRawArrival rate rewards C_star C_h) ν ∧
    Integrable (ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarRawGap rate rewards C_star C_h S) ν ∧
    Integrable (retainedRoundedLearningSum rate rewards C_star C_h S) ν ∧
    (∫ z, ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarBacklogCost rate rewards C_star C_h z ∂ν) ≤
      (2 / 11 : ℝ) * (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) * p.T ∧
    (∫ z, ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarWeightedRawArrival rate rewards C_star C_h z ∂ν) ≤ (p.m : ℝ) * p.T ∧
    (∫ z, ReferenceCompleteOriginalCalendarRawLearningComparison.originalCalendarRawGap rate rewards C_star C_h S z ∂ν) ≤ rawLearningBudget rate ∧
    (∫ z, retainedRoundedLearningSum rate rewards C_star C_h S z ∂ν) ≤
      rawLearningBudget rate + (p.m : ℝ) * p.T / (rate.eta.val * ConstructorDimensions.D p) := by
  obtain ⟨hc, hw, hr, hh, hcb, hwb, hrb, hhb⟩ :=
    localized_learning_bounds rate rewards C_star C_h control0 ids S
  exact ⟨section_integrable ids _ hc, section_integrable ids _ hw,
    section_integrable ids _ hr, section_integrable ids _ hh,
    section_bound ids _ _ hcb, section_bound ids _ _ hwb,
    section_bound ids _ _ hrb, section_bound ids _ _ hhb⟩

/-- The literal finite rounded-learning expectation for every original fixed
ID array. No good-ID condition or supplied numerical estimate is required. -/
public theorem retainedRoundedLearningSum_fixedID_mean (control0 : TimeControl p)
    (ids : CompletePublicTable.IDArray p) (S : ProductSet p.K p.m) :
    Integrable (retainedRoundedLearningSum rate rewards C_star C_h S)
      (ReferenceFixedIDSourceSection.fixedIDSourceLaw ids) ∧
    (∫ z, retainedRoundedLearningSum rate rewards C_star C_h S z
      ∂ReferenceFixedIDSourceSection.fixedIDSourceLaw ids) ≤
      (2 * Real.log (Nat.choose p.K p.m : ℝ) + (p.m : ℝ) / 16) / rate.eta.val +
      (16 * (p.m : ℝ) ^ 2 + (16 / 11 : ℝ) * CanonicalRecordingRates.R p +
        32 * (p.m : ℝ)) * rate.eta.val * p.T +
      (p.m : ℝ) * p.T / (rate.eta.val * ConstructorDimensions.D p) := by
  obtain ⟨_, _, _, hi, _, _, _, hb⟩ :=
    fixedID_learning_mean rate rewards C_star C_h control0 ids S
  exact ⟨hi, hb⟩

end Assembly

end Bandits.Support.ReferenceOriginalCalendarFixedIDLearningMean

end
