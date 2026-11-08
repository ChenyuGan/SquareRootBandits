/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition
public import Bandits.Support.ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic

/-!
# Original-calendar LIVE and collection branch increment transport

The literal selected contributions are identified with the accepted same-date
LIVE and collection scalar terms under the original source-input law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (actualRecord sourcePrefixFiltration)
open ReferenceLaterLiveNumericalReadout (laterLiveReadout)
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceOriginalCalendarLiveCollectionIncrementTransport

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord
  (p := p) (rate := rate)
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val

private theorem dispatch_live_of_state_live (r : Record)
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
    (r : Record) (c : RecordedQueueRun.RoundInput p.K)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hselector : ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveRecordSelector
      rate r = some (c, payload)) :
    ∃ regs owned base, r.input.state.coordinator = .live regs owned base := by
  have hdispatchLive : ∃ regs owned base outcome,
      ReferenceActivePhysicalStep.dispatch r.input = .live regs owned base outcome := by
    unfold ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveRecordSelector
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
    (r : Record) (regs : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters regs)
    (base : Fin (p.m - 1) → ℕ) (hstate : r.input.state.coordinator = .live regs owned base)
    (c : RecordedQueueRun.RoundInput p.K)
    (hread : laterLiveReadout 0 r = some c) :
    (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveRecordSelector
      rate r).isSome = true := by
  have hcoverage :=
    ReferenceOriginalCalendarRetainedBranchPartition.liveRecordSelector_coverage
      rate r c hread
  obtain ⟨outcome, hcut⟩ := dispatch_live_of_state_live
    rate r regs owned base hstate
  rcases hcoverage with hfirst | hlive | hbirth
  · have hfalse : False := by
      unfold ReferenceOriginalCalendarRetainedBranchPartition.firstChosenRecordSelector at hfirst
      rw [hcut] at hfirst
      simp at hfirst
    exact False.elim hfalse
  · exact hlive
  · have hfalse : False := by
      unfold ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector at hbirth
      rw [hcut] at hbirth
      simp at hbirth
    exact False.elim hfalse

private theorem continuingLiveSelector_isSome_iff_liveDomain
    (q : Fin p.T) (z : X) :
    (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
      rate rewards C_star C_h q z).isSome = true ↔
      z ∈ ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveDomain
        rate rewards C_star C_h q := by
  constructor
  · intro hsome
    obtain ⟨data, hselector⟩ := Option.isSome_iff_exists.mp hsome
    rcases data with ⟨r, cp⟩
    rcases cp with ⟨c, payload⟩
    have hparts : actualRecord rate rewards C_star C_h q z = some r ∧
        ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveRecordSelector
          rate r = some (c, payload) := by
      unfold ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector at hselector
      rcases Option.bind_eq_some_iff.mp hselector with ⟨r', hr, hmap⟩
      rcases Option.map_eq_some_iff.mp hmap with ⟨cp', hcp, hdata⟩
      cases hdata
      exact ⟨hr, hcp⟩
    obtain ⟨hr, hrecord⟩ := hparts
    have hread :=
      ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveRecordSelector_cell
        rate r c payload hrecord
    have hstate :=
      continuingLiveRecordSelector_implies_liveInput rate r c payload hrecord
    change z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q
    change ∃ r : Record,
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
          rate rewards C_star C_h q z = some r ∧
        (∃ regs owned base, r.input.state.coordinator = .live regs owned base) ∧
        (laterLiveReadout 0 r).isSome = true
    refine ⟨r, ?_, hstate, ?_⟩
    · simpa only [ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt] using hr
    · rw [hread]
      rfl
  · intro hdomain
    change z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q at hdomain
    change ∃ r : Record,
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
          rate rewards C_star C_h q z = some r ∧
        (∃ regs owned base, r.input.state.coordinator = .live regs owned base) ∧
        (laterLiveReadout 0 r).isSome = true at hdomain
    obtain ⟨r, hr, hstate, hreadSome⟩ := hdomain
    obtain ⟨c, hread⟩ := Option.isSome_iff_exists.mp hreadSome
    obtain ⟨regs, owned, base, hstate⟩ := hstate
    have hrecordSome := continuingLiveRecordSelector_witness_of_actualLiveReadout
      rate r regs owned base hstate c hread
    obtain ⟨cp, hrecord⟩ := Option.isSome_iff_exists.mp hrecordSome
    have hr' : actualRecord rate rewards C_star C_h q z = some r := by
      simpa only [ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt] using hr
    have hselector :
        ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
          rate rewards C_star C_h q z = some ⟨r, cp⟩ := by
      unfold ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
      rw [hr']
      simp [hrecord]
    rw [hselector]
    rfl

private theorem continuingLiveBranchContribution_eq_signedInheritedTerm_at
    (q : Fin p.T) (a : Fin p.K) (z : X) :
    ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
        rate rewards C_star C_h q a z
        (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
          rate rewards C_star C_h q z) =
      ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.signedInheritedTerm
        rate rewards C_star C_h q a z := by
  by_cases hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z
  · by_cases hsome :
        (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
          rate rewards C_star C_h q z).isSome = true
    · have hdomain := (continuingLiveSelector_isSome_iff_liveDomain
        rate rewards C_star C_h q z).mp hsome
      have hgate :=
        (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveGate_iff_activeUpdate
          rate rewards C_star C_h q z).mpr ⟨hdomain, hactive⟩
      have hsupport := hgate.1
      obtain ⟨data, hselector⟩ := Option.isSome_iff_exists.mp hsome
      rcases data with ⟨r, cp⟩
      rcases cp with ⟨c, payload⟩
      have hcell :=
        ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector_actualCell
          rate rewards C_star C_h q z r c payload hselector
      have hnorm :=
        ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt_eq
          rate rewards C_star C_h q a z c hactive hcell
      have hbranch :
          ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
              rate rewards C_star C_h q a z
              (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
                rate rewards C_star C_h q z) =
            ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
                rate rewards C_star C_h q.val a z *
              (Real.exp (beta * ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt
                rate rewards C_star C_h q a z) - 1) := by
        rw [hselector]
        simp only [ReferenceOriginalCalendarRetainedBranchPartition.branchContribution,
          hactive, ↓reduceIte]
        rw [← hnorm]
      have hsigned :=
        ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.signedInheritedTerm_eq
          rate rewards C_star C_h q a z
      rw [ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.normalizedIncrement_eq_live
        rate rewards C_star C_h q a z hgate] at hsigned
      simp only [ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.inheritedEnergy,
        Set.indicator_of_mem hsupport] at hsigned
      exact hbranch.trans hsigned.symm
    · have hnotDomain : z ∉
        ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveDomain
          rate rewards C_star C_h q := by
        intro hdomain
        exact hsome ((continuingLiveSelector_isSome_iff_liveDomain
          rate rewards C_star C_h q z).mpr hdomain)
      have hnone :
          ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
            rate rewards C_star C_h q z = none := by
        cases hsel : ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
            rate rewards C_star C_h q z with
        | none => rfl
        | some data => exact False.elim (hsome (by simp [hsel]))
      simp [ReferenceOriginalCalendarRetainedBranchPartition.branchContribution,
        ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.signedInheritedTerm,
        hnotDomain, hnone]
  · by_cases hdomain : z ∈
        ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.liveDomain
          rate rewards C_star C_h q
    · have hnormzero :
          ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt
            rate rewards C_star C_h q a z = 0 := by
        simp [ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt,
          hactive]
      cases hselector : ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
          rate rewards C_star C_h q z <;>
        simp [ReferenceOriginalCalendarRetainedBranchPartition.branchContribution,
          ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.signedInheritedTerm,
          hactive, hdomain, hnormzero]
    · cases hselector : ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
          rate rewards C_star C_h q z <;>
        simp [ReferenceOriginalCalendarRetainedBranchPartition.branchContribution,
          ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.signedInheritedTerm,
          hactive, hdomain]

public theorem continuingLive_branchContribution_eq_signedInheritedTerm
    (q : Fin p.T) (a : Fin p.K) :
    (fun z : X =>
      ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
        rate rewards C_star C_h q a z
        (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
          rate rewards C_star C_h q z)) =
      ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.signedInheritedTerm
        rate rewards C_star C_h q a := by
  funext z
  exact continuingLiveBranchContribution_eq_signedInheritedTerm_at
    rate rewards C_star C_h q a z

public theorem continuingLive_branchContribution_integrable
    (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    Integrable (fun z : X =>
      ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
        rate rewards C_star C_h q a z
        (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
          rate rewards C_star C_h q z)) mu := by
  rw [continuingLive_branchContribution_eq_signedInheritedTerm
    rate rewards C_star C_h q a]
  exact (ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.signedInheritedTerm_condExp
    rate rewards C_star C_h control0 q a).1

public theorem continuingLive_branchContribution_integral_nonpos
    (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    (∫ z, ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
      rate rewards C_star C_h q a z
      (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
        rate rewards C_star C_h q z) ∂mu) ≤ 0 := by
  rw [continuingLive_branchContribution_eq_signedInheritedTerm
    rate rewards C_star C_h q a]
  exact ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep.signedInheritedTerm_integral_nonpos
    rate rewards C_star C_h control0 q a

private theorem collectionOrCutoffBranchContribution_eq_retainedTerm_at
    (q : Fin p.T) (a : Fin p.K) (z : X) :
    ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
        rate rewards C_star C_h q a z
        (ReferenceOriginalCalendarRetainedBranchPartition.collectionOrCutoffSelector
          rate rewards C_star C_h q z) =
      ReferenceOriginalCalendarCollectionRetainedEnergyStep.W
          rate rewards C_star C_h q a z *
        (ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX
          rate rewards C_star C_h q a z - 1) := by
  by_cases hG : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.G
      rate rewards C_star C_h q
  · have hactiveSome :=
      (ReferenceOriginalCalendarRetainedBranchPartition.activeCollectionSelector_iff_G
        rate rewards C_star C_h q a z).mpr hG
    obtain ⟨hactive, hsome⟩ := hactiveSome
    obtain ⟨data, hselector⟩ := Option.isSome_iff_exists.mp hsome
    rcases data with ⟨r, cp⟩
    rcases cp with ⟨c, payload⟩
    obtain ⟨_, henergy, _⟩ :=
      ReferenceOriginalCalendarRetainedBranchPartition.collectionBranch_matches_retainedStep
        rate rewards C_star C_h q a z r c payload hactive hselector
    obtain ⟨_, hcell⟩ :=
      ReferenceOriginalCalendarRetainedBranchPartition.collectionSelector_eq_collectionRecorder
        rate rewards C_star C_h q z r c payload hselector
    have hnorm :=
      ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt_eq
        rate rewards C_star C_h q a z c hactive hcell
    have hq : RecordedRoundMoments.normalizedQuantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a - 4 =
          ReferenceOriginalCalendarCollectionRetainedEnergyStep.x
            rate rewards C_star C_h q a z := hnorm.symm.trans
              (ReferenceOriginalCalendarRetainedBranchPartition.collectionBranch_matches_retainedStep
                rate rewards C_star C_h q a z r c payload hactive hselector).2.2
    rw [hselector]
    simp only [ReferenceOriginalCalendarRetainedBranchPartition.branchContribution,
      hactive, ↓reduceIte]
    rw [henergy, hq]
    rfl
  · have hnoActiveSome : ¬
        (ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
            rate rewards C_star C_h q z ∧
          (ReferenceOriginalCalendarRetainedBranchPartition.collectionOrCutoffSelector
            rate rewards C_star C_h q z).isSome = true) := by
      intro h
      exact hG ((ReferenceOriginalCalendarRetainedBranchPartition.activeCollectionSelector_iff_G
        rate rewards C_star C_h q a z).mp h)
    have hx := ReferenceOriginalCalendarCollectionRetainedEnergyStep.x_off_gate
      rate rewards C_star C_h q a z hG
    by_cases hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
        rate rewards C_star C_h q z
    · cases hselector : ReferenceOriginalCalendarRetainedBranchPartition.collectionOrCutoffSelector
          rate rewards C_star C_h q z with
      | none =>
          simp [ReferenceOriginalCalendarRetainedBranchPartition.branchContribution,
            ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX, hx]
      | some data =>
          have hfalse := hnoActiveSome ⟨hactive, by simp [hselector]⟩
          exact False.elim hfalse
    · cases hselector : ReferenceOriginalCalendarRetainedBranchPartition.collectionOrCutoffSelector
          rate rewards C_star C_h q z <;>
        simp [ReferenceOriginalCalendarRetainedBranchPartition.branchContribution, hactive,
          ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX, hx]

public theorem collectionOrCutoff_branchContribution_eq_retainedEnergyTerm
    (q : Fin p.T) (a : Fin p.K) :
    (fun z : X =>
      ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
        rate rewards C_star C_h q a z
        (ReferenceOriginalCalendarRetainedBranchPartition.collectionOrCutoffSelector
          rate rewards C_star C_h q z)) =
      (fun z : X =>
        ReferenceOriginalCalendarCollectionRetainedEnergyStep.W
            rate rewards C_star C_h q a z *
          (ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX
              rate rewards C_star C_h q a z - 1)) := by
  funext z
  exact collectionOrCutoffBranchContribution_eq_retainedTerm_at
    rate rewards C_star C_h q a z

private theorem retainedEnergyTerm_integrable
    (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    Integrable (fun z : X =>
      ReferenceOriginalCalendarCollectionRetainedEnergyStep.W rate rewards C_star C_h q a z *
        (ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX
          rate rewards C_star C_h q a z - 1)) mu := by
  let W := ReferenceOriginalCalendarCollectionRetainedEnergyStep.W rate rewards C_star C_h q a
  let E := ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX rate rewards C_star C_h q a
  let A := fun z : X => E z - 1
  obtain ⟨hWi, _hXi⟩ := ReferenceOriginalCalendarCollectionRetainedEnergyStep.energy_integrable
    rate rewards C_star C_h q a control0
  have hEi := ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX_integrable
    rate rewards C_star C_h q a control0
  have hAi : Integrable A mu := by
    exact hEi.sub (integrable_const (1 : ℝ))
  have hWbounds : ∀ z, 0 ≤ W z ∧ W z ≤
      Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))) := by
    intro z
    by_cases hB : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.B
        rate rewards C_star C_h q
    · have hbounds := ReferenceOriginalCalendarCollectionRetainedEnergyStep.queueExp_bounds
        rate rewards C_star C_h a q.val z
      simpa only [W, ReferenceOriginalCalendarCollectionRetainedEnergyStep.W,
        Set.indicator_of_mem hB] using hbounds
    · have hupper : 0 ≤ Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))) := Real.exp_nonneg _
      simp only [W, ReferenceOriginalCalendarCollectionRetainedEnergyStep.W,
        Set.indicator_of_notMem hB]
      exact ⟨le_rfl, hupper⟩
  have hAW : Integrable (fun z => A z * W z) mu := by
    apply hAi.mul_bdd hWi.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (hWbounds z).1]
    exact (hWbounds z).2
  have hWA : Integrable (fun z => W z * A z) mu := by
    convert hAW using 1
    funext z
    exact mul_comm _ _
  have hWA' : Integrable (fun z : X =>
      ReferenceOriginalCalendarCollectionRetainedEnergyStep.W rate rewards C_star C_h q a z *
        (ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX
          rate rewards C_star C_h q a z - 1)) mu := by
    exact hWA
  exact hWA'

private theorem retainedEnergyTerm_integral_nonpos
    (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    (∫ z, ReferenceOriginalCalendarCollectionRetainedEnergyStep.W
        rate rewards C_star C_h q a z *
      (ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX
        rate rewards C_star C_h q a z - 1) ∂mu) ≤ 0 := by
  let W := ReferenceOriginalCalendarCollectionRetainedEnergyStep.W rate rewards C_star C_h q a
  let E := ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX rate rewards C_star C_h q a
  let A := fun z : X => E z - 1
  have hle := (sourcePrefixFiltration control0).le' (q.val + 1)
  obtain ⟨hWi, _hXi⟩ := ReferenceOriginalCalendarCollectionRetainedEnergyStep.energy_integrable
    rate rewards C_star C_h q a control0
  have hEi := ReferenceOriginalCalendarCollectionRetainedEnergyStep.expX_integrable
    rate rewards C_star C_h q a control0
  have hAi : Integrable A mu := hEi.sub (integrable_const (1 : ℝ))
  have hWbounds : ∀ z, 0 ≤ W z ∧ W z ≤
      Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))) := by
    intro z
    by_cases hB : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.B
        rate rewards C_star C_h q
    · have hbounds := ReferenceOriginalCalendarCollectionRetainedEnergyStep.queueExp_bounds
        rate rewards C_star C_h a q.val z
      simpa only [W, ReferenceOriginalCalendarCollectionRetainedEnergyStep.W,
        Set.indicator_of_mem hB] using hbounds
    · have hupper : 0 ≤ Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))) := Real.exp_nonneg _
      simp only [W, ReferenceOriginalCalendarCollectionRetainedEnergyStep.W,
        Set.indicator_of_notMem hB]
      exact ⟨le_rfl, hupper⟩
  have hWA : Integrable (fun z => W z * A z) mu := by
    have hAW : Integrable (fun z => A z * W z) mu := by
      apply hAi.mul_bdd hWi.aestronglyMeasurable
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (hWbounds z).1]
      exact (hWbounds z).2
    convert hAW using 1
    funext z
    exact mul_comm _ _
  have hWmeas := ReferenceOriginalCalendarCollectionRetainedEnergyStep.W_measurable
    rate rewards C_star C_h control0 q a
  have hpull := condExp_mul_of_aestronglyMeasurable_left
    hWmeas.aestronglyMeasurable hWA hAi
  have hsub := condExp_sub hEi (integrable_const (1 : ℝ))
    (sourcePrefixFiltration control0 (q.val + 1))
  have hone := condExp_const (μ := mu) hle (1 : ℝ)
  rw [hone] at hsub
  have hCE : mu[(fun z => W z * A z) |
      sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu] (fun _ => (0 : ℝ)) := by
    filter_upwards [hpull, hsub,
      ReferenceOriginalCalendarCollectionRetainedEnergyStep.condExp_expX_le_one
        rate rewards C_star C_h control0 q a] with z hp hs he
    change mu[W * A | sourcePrefixFiltration control0 (q.val + 1)] z ≤ 0
    rw [hp]
    change W z * mu[A | sourcePrefixFiltration control0 (q.val + 1)] z ≤ 0
    have hsubA : mu[A | sourcePrefixFiltration control0 (q.val + 1)] z =
        mu[E | sourcePrefixFiltration control0 (q.val + 1)] z - 1 := by
      change mu[(fun z => E z - 1) |
        sourcePrefixFiltration control0 (q.val + 1)] z = _
      exact hs
    rw [hsubA]
    exact mul_nonpos_of_nonneg_of_nonpos (hWbounds z).1 (sub_nonpos.mpr he)
  have hi := integral_mono_ae integrable_condExp (integrable_const (0 : ℝ)) hCE
  rw [integral_condExp hle] at hi
  simpa using hi

public theorem collectionOrCutoff_branchContribution_integrable
    (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    Integrable (fun z : X =>
      ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
        rate rewards C_star C_h q a z
        (ReferenceOriginalCalendarRetainedBranchPartition.collectionOrCutoffSelector
          rate rewards C_star C_h q z)) mu := by
  rw [collectionOrCutoff_branchContribution_eq_retainedEnergyTerm
    rate rewards C_star C_h q a]
  exact retainedEnergyTerm_integrable rate rewards C_star C_h control0 q a

public theorem collectionOrCutoff_branchContribution_integral_nonpos
    (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    (∫ z, ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
      rate rewards C_star C_h q a z
      (ReferenceOriginalCalendarRetainedBranchPartition.collectionOrCutoffSelector
        rate rewards C_star C_h q z) ∂mu) ≤ 0 := by
  rw [collectionOrCutoff_branchContribution_eq_retainedEnergyTerm
    rate rewards C_star C_h q a]
  exact retainedEnergyTerm_integral_nonpos rate rewards C_star C_h control0 q a

public theorem continuingLive_collectionOrCutoff_branchContribution_sum_integrable
    (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    Integrable (fun z : X =>
      ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
        rate rewards C_star C_h q a z
        (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
          rate rewards C_star C_h q z) +
      ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
        rate rewards C_star C_h q a z
        (ReferenceOriginalCalendarRetainedBranchPartition.collectionOrCutoffSelector
          rate rewards C_star C_h q z)) mu := by
  exact (continuingLive_branchContribution_integrable
    rate rewards C_star C_h control0 q a).add
      (collectionOrCutoff_branchContribution_integrable
        rate rewards C_star C_h control0 q a)

public theorem continuingLive_collectionOrCutoff_branchContribution_sum_integral_nonpos
    (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    (∫ z, (ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
        rate rewards C_star C_h q a z
        (ReferenceOriginalCalendarRetainedBranchPartition.continuingLiveSelector
          rate rewards C_star C_h q z) +
      ReferenceOriginalCalendarRetainedBranchPartition.branchContribution
        rate rewards C_star C_h q a z
        (ReferenceOriginalCalendarRetainedBranchPartition.collectionOrCutoffSelector
          rate rewards C_star C_h q z)) ∂mu) ≤ 0 := by
  have hLiveInt := continuingLive_branchContribution_integrable
    rate rewards C_star C_h control0 q a
  have hCollectionInt := collectionOrCutoff_branchContribution_integrable
    rate rewards C_star C_h control0 q a
  rw [integral_add hLiveInt hCollectionInt]
  exact add_nonpos
    (continuingLive_branchContribution_integral_nonpos
      rate rewards C_star C_h control0 q a)
    (collectionOrCutoff_branchContribution_integral_nonpos
      rate rewards C_star C_h control0 q a)

end Bandits.Support.ReferenceOriginalCalendarLiveCollectionIncrementTransport

end
