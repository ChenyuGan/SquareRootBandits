/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarFirstBranchIncrementTransport
public import Bandits.Support.ReferenceOriginalCalendarLiveCollectionWeightedDrift

import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

/-!
# First chosen weighted observations on the original calendar

The observations below retain the actual first chosen selector, its original
source law, and its actual first queue cell. The first update is inclusive,
including when it is the update that crosses the analytical overflow level.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceOriginalCalendarFirstWeightedTransport

open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
  (q : Fin p.T)

local notation "X" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "A" => ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
  rate rewards C_star C_h q
local notation "phase" => ReferenceFirstLiveSourcePhasePartition.sourcePhase
  rate rewards C_star C_h q
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "V" => ReferenceOriginalCalendarLiveCollectionWeightedDrift.V
  rate rewards C_star C_h
local notation "C" => ReferenceOriginalCalendarLiveCollectionWeightedDrift.C
  rate rewards C_star C_h
local notation "theta" => ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ))
local notation "Inputs" => ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
  rate rewards C_star C_h
local notation "firstCell" => ReferenceFirstLaunchCommonUpdateSource.firstCell
  rate rewards C_star C_h
local notation "firstUpdate" => ReferenceFirstLaunchCommonUpdateSource.firstUpdate
  rate rewards C_star C_h
local notation "birthPotential" => ReferenceFirstLaunchEnergyInitialization.birthPotential
  rate rewards C_star C_h
local notation "firstReadout" => ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
  rate rewards C_star C_h

/-- The actual first-selector weighted square-potential increment, zero off
that selector event. -/
public def firstWeightedDelta (q : Fin p.T) : X → ℝ :=
  (ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
    rate rewards C_star C_h q).indicator
    (ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV
      rate rewards C_star C_h q)

/-- The actual first-selector raw arrival, weighted by the original zero-score
marginal and zero outside the exact first-selector event. -/
public def firstWeightedArrival (q : Fin p.T) : X → ℝ :=
  (ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
    rate rewards C_star C_h q).indicator (fun z =>
      ∑ i : Fin p.K, ProductSetLaw.theta p.m (fun _ : Fin p.K => (1 : ℝ)) i *
        match ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
            rate rewards C_star C_h q z with
        | none => 0
        | some c => RecordedRoundMoments.rawEstimate Q
            (RecordedQueueRun.initialState p.K) c i)

private theorem sourceStratum_birth_subset (j : Fin (M p))
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)) :
    z.val ∈ phase 2 := by
  rw [ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_birth_iUnion
    rate rewards C_star C_h q]
  apply Set.mem_iUnion.mpr
  refine ⟨j, ?_⟩
  exact z.property

private theorem stateReadout_injective {K : ℕ}
    (s t : RecordedQueueRun.RunState K)
    (h : ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout s =
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout t) :
    s = t := by
  cases s
  cases t
  simp only [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
    Prod.mk.injEq] at h
  cases h.1
  cases h.2.1
  cases h.2.2
  rfl

/-- The accepted first-update transport identifies the actual incoming prefix,
actual enabled cell, and inclusive successor with the source-stratum update. -/
public theorem source_first_transport (j : Fin (M p))
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)) :
    Inputs q.val z.val = some [] ∧
    ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
      rate rewards C_star C_h q z.val = some (firstCell j q control0 z) ∧
    Inputs (q.val + 1) z.val = some [firstCell j q control0 z] ∧
    RecordedQueueRun.run Q [firstCell j q control0 z] = firstUpdate j q control0 z ∧
    (firstCell j q control0 z).enabled = true := by
  have h := ReferenceOriginalCalendarFirstDispatchEnergyTransport.carried_initial_first_update_transport
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (t := q) (a := ⟨0, ConstructorDimensions.K_pos p⟩)
    (q := j) z
  rcases h with ⟨hbefore, hcell, hafter, hreadout, _, _, _, henabled⟩
  have hrunReadout :
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q [firstCell j q control0 z]) =
        ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (firstUpdate j q control0 z) := by
    have h' := hreadout
    simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hafter, Option.map_some, Option.some.injEq] at h'
    exact h'
  refine ⟨hbefore, hcell, hafter, stateReadout_injective _ _ hrunReadout, henabled⟩

/-- On the actual FIRST selector, the previous full-prefix potential and
backlog are zero, and the successor potential is the actual first-update
weighted square potential. The current marginals are exactly the all-one
weight marginal. -/
public theorem source_first_weighted_facts (j : Fin (M p))
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)) :
    V q.val z.val = 0 ∧ C q.val z.val = 0 ∧
    V (q.val + 1) z.val = birthPotential j q control0 z ∧
    (∀ i : Fin p.K,
      ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt
        rate rewards C_star C_h q.val i z.val = theta i) ∧
    (∀ i : Fin p.K,
      (RecordedQueueRun.run Q [firstCell j q control0 z]).registers i =
        (firstUpdate j q control0 z).registers i) := by
  have ht := source_first_transport rate rewards C_star C_h control0 q j z
  rcases ht with ⟨hbefore, _, hafter, hrun, _⟩
  have hweight0 :
      RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q ([] :
        List (RecordedQueueRun.RoundInput p.K))) = fun _ => 1 := by
    funext i
    rfl
  have hpotential :
      RecordedWeightedDrift.weightedSquarePotential p.m Q (firstUpdate j q control0 z) =
        birthPotential j q control0 z := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [ReferenceOriginalCalendarLiveCollectionWeightedDrift.V, hbefore,
      RecordedWeightedDrift.weightedSquarePotential, RecordedQueueRun.run,
      RecordedQueueRun.execute, RecordedQueueRun.initialState,
      StoppedQueueBound.normalizedBacklog]
  · simp [ReferenceOriginalCalendarLiveCollectionWeightedDrift.C, hbefore,
      RecordedWeightedDrift.weightedBacklog, RecordedQueueRun.run,
      RecordedQueueRun.execute, RecordedQueueRun.initialState,
      StoppedQueueBound.normalizedBacklog]
  · simp [ReferenceOriginalCalendarLiveCollectionWeightedDrift.V, hafter, hrun,
      hpotential]
  · intro i
    simp [ReferenceOriginalCalendarLiveCollectionWeightedDrift.thetaAt, hbefore,
      hweight0]
  · intro i
    rw [hrun]

include control0 in
private theorem selector_data_on_sourceStratum (j : Fin (M p))
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)) :
    ∃ r c payload,
      ReferenceOriginalCalendarRetainedBranchPartition.firstChosenSelector
        rate rewards C_star C_h q z.val = some ⟨r, (c, payload)⟩ := by
  have hphase := sourceStratum_birth_subset rate rewards C_star C_h q j z
  have hevent := (ReferenceOriginalCalendarFirstBranchIncrementTransport.firstChosenSelector_isSome_iff_sourcePhase
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (q := q) (a := ⟨0, ConstructorDimensions.K_pos p⟩) z.val).2 hphase
  cases hsel : ReferenceOriginalCalendarRetainedBranchPartition.firstChosenSelector
      rate rewards C_star C_h q z.val with
  | none => simp [hsel] at hevent
  | some data =>
      rcases data with ⟨r, cellPayload⟩
      rcases cellPayload with ⟨c, payload⟩
      exact ⟨r, c, payload, rfl⟩

private theorem source_first_raw_eq_readout (j : Fin (M p))
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q))
    (i : Fin p.K) :
    RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.initialState p.K)
      (firstCell j q control0 z) i = firstReadout j q control0 z i := by
  have hstep := ReferenceFirstLaunchCommonUpdateSource.source_first_update
    rate rewards C_star C_h j q control0 z
  have htotal := (hstep.1 i).2.2
  have hcast :
      (((firstUpdate j q control0 z).registers i).1 +
        ((firstUpdate j q control0 z).registers i).2 : ℕ) =
      ReferenceFirstLaunchCommonUpdateSource.firstArrival
        rate rewards C_star C_h j q control0 z i := htotal
  have hreadout : firstReadout j q control0 z i =
      (ReferenceFirstLaunchCommonUpdateSource.firstArrival
        rate rewards C_star C_h j q control0 z i : ℝ) / (rate.n : ℝ) := by
    change ((((firstUpdate j q control0 z).registers i).1 +
      ((firstUpdate j q control0 z).registers i).2 : ℕ) : ℝ) /
        (rate.eta.val * (D p : ℝ)) = _
    rw [hcast, rate.n_scale]
  rw [RecordedRoundMoments.rawEstimate_eq_normalizedQuantizedArrival_of_enabled
      Q (RecordedQueueRun.initialState p.K) (firstCell j q control0 z) i
      (source_first_transport rate rewards C_star C_h control0 q j z).2.2.2.2
      rfl]
  rw [RecordedRoundMoments.normalizedQuantizedArrival]
  change (RecordedQueueRun.quantizedArrival Q (firstCell j q control0 z) i : ℝ) /
      ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) = _
  have hQn :
      ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) =
        (rate.n : ℝ) := by
    simp [ReferenceFirstLaunchNumericalCell.queueParameters]
  rw [show RecordedQueueRun.quantizedArrival Q (firstCell j q control0 z) i =
    ReferenceFirstLaunchCommonUpdateSource.firstArrival
      rate rewards C_star C_h j q control0 z i by rfl, hQn, ← hreadout]

public theorem first_arrival_on_sourceStratum (j : Fin (M p))
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)) :
    (fun x : X => firstWeightedArrival rate rewards C_star C_h q x) z.val =
      ∑ i : Fin p.K, theta i * firstReadout j q control0 z i := by
  have hphase := sourceStratum_birth_subset rate rewards C_star C_h q j z
  have hevent := (ReferenceOriginalCalendarFirstBranchIncrementTransport.firstChosenSelector_isSome_iff_sourcePhase
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (q := q) (a := ⟨0, ConstructorDimensions.K_pos p⟩) z.val).2 hphase
  obtain ⟨r, c, payload, hselector⟩ := selector_data_on_sourceStratum
    rate rewards C_star C_h control0 q j z
  have hactual := ReferenceOriginalCalendarRetainedBranchPartition.firstSelector_actualCell
    rate rewards C_star C_h q z.val r c payload hselector
  have htransport := source_first_transport rate rewards C_star C_h control0 q j z
  have hcellEq : c = firstCell j q control0 z :=
    Option.some.inj (hactual.symm.trans htransport.2.1)
  have hmem : z.val ∈ A := by
    change (ReferenceOriginalCalendarRetainedBranchPartition.firstChosenSelector
      rate rewards C_star C_h q z.val).isSome = true
    exact hevent
  change Set.indicator A (fun x : X =>
    ∑ i : Fin p.K, theta i *
      match ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
          rate rewards C_star C_h q x with
      | none => 0
      | some c => RecordedRoundMoments.rawEstimate Q
          (RecordedQueueRun.initialState p.K) c i) z.val = _
  rw [Set.indicator_of_mem hmem, hactual]
  dsimp only
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcellEq, source_first_raw_eq_readout rate rewards C_star C_h control0 q j z i]

public theorem source_first_delta_eq_birthPotential (j : Fin (M p))
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)) :
    ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV rate rewards C_star C_h q z.val =
      birthPotential j q control0 z := by
  have hf := source_first_weighted_facts rate rewards C_star C_h control0 q j z
  change V (q.val + 1) z.val - V q.val z.val = _
  rw [hf.2.2.1, hf.1]
  exact sub_zero _

include control0 in
private theorem measurableSet_firstSelectorEvent : MeasurableSet A := by
  exact ReferenceOriginalCalendarFirstBranchIncrementTransport.measurableSet_firstSelectorEvent
    rate rewards C_star C_h control0 q ⟨0, ConstructorDimensions.K_pos p⟩

include control0 in
public theorem firstWeightedDelta_integrable :
    Integrable (firstWeightedDelta rate rewards C_star C_h q) mu := by
  unfold firstWeightedDelta
  have hdelta : Integrable
      (ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV
        rate rewards C_star C_h q) mu := by
    exact (ReferenceOriginalCalendarLiveCollectionWeightedDrift.V_integrable
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (q.val + 1)).sub (ReferenceOriginalCalendarLiveCollectionWeightedDrift.V_integrable
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) q.val)
  exact hdelta.indicator
    (measurableSet_firstSelectorEvent rate rewards C_star C_h control0 q)

include control0 in
public theorem firstWeightedDelta_integral_le_event_mass :
    (∫ z : X, firstWeightedDelta rate rewards C_star C_h q z ∂mu) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (sourceInputLaw p).real A := by
  classical
  let f : X → ℝ := ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV
    rate rewards C_star C_h q
  let S : Fin (M p) → Set X := fun j =>
    ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h q
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)
  have hf : Integrable f mu := by
    dsimp [f]
    exact (ReferenceOriginalCalendarLiveCollectionWeightedDrift.V_integrable
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (q.val + 1)).sub (ReferenceOriginalCalendarLiveCollectionWeightedDrift.V_integrable
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) q.val)
  have hmeas (j : Fin (M p)) : MeasurableSet (S j) :=
    ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h q control0
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)
  have hdis : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    apply ReferenceTotalSourcePairCoupling.sourceStratumEvent_disjoint
    intro heq
    apply hij
    exact congrArg Prod.fst heq
  have hstratum (j : Fin (M p)) :
      (∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q),
        f z.val ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)) ≤
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)).real Set.univ := by
    rw [show (fun z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q) => f z.val) =
      fun z => birthPotential j q control0 z by
        funext z
        exact source_first_delta_eq_birthPotential rate rewards C_star C_h control0 q j z]
    exact ReferenceFirstLaunchEnergyInitialization.integral_birthPotential
      rate rewards C_star C_h j q control0
  have hmass (j : Fin (M p)) :
      (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)).real Set.univ =
        (sourceInputLaw p).real (S j) := by
    let f0 : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q) → X := Subtype.val
    let hmap := ReferenceTotalSourceDisintegration.sourceStratumMeasure_map
      rate rewards C_star C_h q control0
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)
    calc
      _ = Measure.real
          ((ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)).map f0) Set.univ := by
          symm
          simpa [f0] using map_measureReal_apply
            (measurable_subtype_coe : Measurable f0) MeasurableSet.univ
      _ = ((sourceInputLaw p).restrict (S j)).real Set.univ := by
          exact congrArg (fun η : Measure X => η.real Set.univ)
            (by simpa [f0, S] using hmap)
      _ = (sourceInputLaw p).real (S j) := by simp
  have hmassUnion :
      (∑ j : Fin (M p),
        (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)).real Set.univ) =
        (sourceInputLaw p).real (⋃ j : Fin (M p), S j) := by
    calc
      _ = ∑ j : Fin (M p), (sourceInputLaw p).real (S j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hmass j
      _ = (sourceInputLaw p).real (⋃ j : Fin (M p), S j) :=
        (measureReal_iUnion_fintype (μ := mu) hdis hmeas
          (fun _ => by finiteness)).symm
  have hunion := ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_birth_iUnion
    rate rewards C_star C_h q
  rw [firstWeightedDelta]
  have hA := ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent_eq_sourcePhase
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (q := q)
    (a := ⟨0, ConstructorDimensions.K_pos p⟩)
  calc
    (∫ z : X,
      (ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
        rate rewards C_star C_h q).indicator f z ∂mu) =
        ∫ z in phase 2, f z ∂mu :=
      by
        rw [hA]
        exact integral_indicator
          (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
            rate rewards C_star C_h q control0 ⟨2, by omega⟩)
    _ ≤ (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (sourceInputLaw p).real (phase 2) := by
      rw [hunion]
      calc
        (∫ z in ⋃ j : Fin (M p), S j, f z ∂mu) =
            ∑ j : Fin (M p), ∫ z in S j, f z ∂mu :=
          integral_iUnion_fintype hmeas hdis (fun _ => hf.integrableOn)
        _ = ∑ j : Fin (M p), ∫ z : ReferenceTotalSourceDisintegration.SourceStratum
            rate rewards C_star C_h q
              (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q),
            f z.val ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
              (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (integral_subtype_comap (hmeas j) f).symm
        _ ≤ ∑ j : Fin (M p),
            (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
              (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
                (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)).real Set.univ :=
          Finset.sum_le_sum (fun j _ => hstratum j)
        _ = (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
            (sourceInputLaw p).real (⋃ j : Fin (M p), S j) := by
          rw [← Finset.mul_sum, hmassUnion]
    _ = (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (sourceInputLaw p).real
          (ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent
            rate rewards C_star C_h q) := by
      rw [← hA]


private theorem measurable_optionElim {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (none : β) (f : α → β) (hf : Measurable f) :
    Measurable (fun o : Option α => o.elim none f) := by
  have hsum : Measurable (fun x : α ⊕ PUnit => x.elim f (fun _ => none)) :=
    Measurable.sumElim hf measurable_const
  have hcomp := hsum.comp (comap_measurable (Equiv.optionEquivSumPUnit α))
  convert hcomp using 1
  funext o
  cases o <;> rfl

private abbrev FirstNumericCoordinates :=
  Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ)))

private def initialRawCoordinate (rate : ReferenceActivePhysicalStep.RateInput p)
    (i : Fin p.K) (v : FirstNumericCoordinates (p := p)) : ℝ :=
  if v.1 then
    if v.2.1 = some i then
      (Nat.floor ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n * v.2.2.1 i / v.2.2.2 i) : ℝ) / (ReferenceFirstLaunchNumericalCell.queueParameters rate).n
    else 0
  else 0

private theorem measurable_initialRawCoordinate (rate : ReferenceActivePhysicalStep.RateInput p)
    (i : Fin p.K) :
    Measurable (initialRawCoordinate (p := p) rate i) := by
  let reward := fun v : FirstNumericCoordinates (p := p) => v.2.2.1 i
  let currentRate := fun v : FirstNumericCoordinates (p := p) => v.2.2.2 i
  have hre : Measurable reward := (measurable_pi_apply i).comp
    (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hrate : Measurable currentRate := (measurable_pi_apply i).comp
    (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hval : Measurable (fun v : FirstNumericCoordinates (p := p) =>
      (Nat.floor ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n * reward v / currentRate v) : ℝ) / (ReferenceFirstLaunchNumericalCell.queueParameters rate).n) := by
    have hquot : Measurable (fun v => (ReferenceFirstLaunchNumericalCell.queueParameters rate).n * reward v / currentRate v) :=
      (measurable_const.mul hre).div hrate
    have hfloor : Measurable (fun v => Nat.floor ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n * reward v / currentRate v)) :=
      Nat.measurable_floor.comp hquot
    have hcast : Measurable (fun v =>
        (Nat.floor ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n * reward v / currentRate v) : ℝ)) :=
      MeasurableEmbedding.natCast.measurable.comp hfloor
    exact hcast.div_const _
  have hrecord : MeasurableSet {v : FirstNumericCoordinates (p := p) | v.2.1 = some i} :=
    (measurableSet_singleton (some i)).preimage
      (measurable_fst.comp measurable_snd)
  have hinner : Measurable (fun v => if v.2.1 = some i then
      (Nat.floor ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n * reward v / currentRate v) : ℝ) / (ReferenceFirstLaunchNumericalCell.queueParameters rate).n else 0) :=
    Measurable.ite hrecord hval measurable_const
  have henabled : MeasurableSet {v : FirstNumericCoordinates (p := p) | v.1 = true} :=
    (measurableSet_singleton true).preimage measurable_fst
  exact Measurable.ite henabled hinner measurable_const

private theorem rawEstimate_initial_eq_coordinate (c : RecordedQueueRun.RoundInput p.K)
    (i : Fin p.K) :
    RecordedRoundMoments.rawEstimate (ReferenceFirstLaunchNumericalCell.queueParameters rate) (RecordedQueueRun.initialState p.K) c i =
      initialRawCoordinate (p := p) rate i
        (ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates c) := by
  cases c with
  | mk enabled recordedArm reward currentRate reward_nonneg reward_le rate_pos =>
      by_cases hrecord : recordedArm = some i
      · cases enabled <;>
          simp [initialRawCoordinate, hrecord, RecordedRoundMoments.rawEstimate,
            RecordedQueueRun.initialState, RecordedQueueRun.acceptedRecord,
            RecordedQueueRun.acceptedArrival, RecordedQueueRun.quantizedArrival,
            ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates]
      · cases enabled <;>
          simp [initialRawCoordinate, hrecord, RecordedRoundMoments.rawEstimate,
          RecordedQueueRun.initialState, RecordedQueueRun.acceptedRecord,
          RecordedQueueRun.acceptedArrival, RecordedQueueRun.quantizedArrival,
          ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates]

private def actualFirstRawArrival (i : Fin p.K) : X → ℝ := fun z =>
  (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell rate rewards C_star C_h q z).elim
    0 (fun c => initialRawCoordinate (p := p) rate i
      (ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates c))

private theorem actualFirstRawArrival_measurable (i : Fin p.K) :
    Measurable (actualFirstRawArrival rate rewards C_star C_h q i) := by
  have h := measurable_optionElim (0 : ℝ)
    (initialRawCoordinate (p := p) rate i)
    (measurable_initialRawCoordinate (p := p) rate i)
  have h' := h.comp
    (ReferenceOriginalCalendarContinuingLiveRecorderLaw.measurable_actualNumerical
      rate rewards C_star C_h q)
  have heq : (fun z : X =>
      ((ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell
        rate rewards C_star C_h q z).map
          ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates).elim
        0 (initialRawCoordinate (p := p) rate i)) =
      actualFirstRawArrival rate rewards C_star C_h q i := by
    funext z
    cases hcell : ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell
        rate rewards C_star C_h q z <;>
      simp [actualFirstRawArrival, hcell]
  rw [← heq]
  exact h'

include control0 in
private theorem selector_actualCell_eq_continuing (z : X) (hz : z ∈ A) :
    ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
      rate rewards C_star C_h q z =
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell
      rate rewards C_star C_h q z := by
  have hA := ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent_eq_sourcePhase
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (q := q)
    (a := ⟨0, ConstructorDimensions.K_pos p⟩)
  have hphase : z ∈ phase 2 := by
    rw [← hA]
    exact hz
  have hs := ReferenceOriginalCalendarFirstBranchIncrementTransport.firstChosenSelector_isSome_iff_sourcePhase
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (q := q) (a := ⟨0, ConstructorDimensions.K_pos p⟩)
  have hsome : (ReferenceOriginalCalendarRetainedBranchPartition.firstChosenSelector
      rate rewards C_star C_h q z).isSome = true := (hs z).2 hphase
  have hselector_exists : ∃ r c payload,
      ReferenceOriginalCalendarRetainedBranchPartition.firstChosenSelector
        rate rewards C_star C_h q z = some ⟨r, (c, payload)⟩ := by
    cases hselector : ReferenceOriginalCalendarRetainedBranchPartition.firstChosenSelector
        rate rewards C_star C_h q z with
    | none => simp [hselector] at hsome
    | some data =>
        rcases data with ⟨r, cp⟩
        rcases cp with ⟨c, payload⟩
        exact ⟨r, c, payload, rfl⟩
  rcases hselector_exists with ⟨r, c, payload, hselector⟩
  have hparts :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r ∧
      ReferenceOriginalCalendarRetainedBranchPartition.firstChosenRecordSelector rate r =
        some (c, payload) := by
    unfold ReferenceOriginalCalendarRetainedBranchPartition.firstChosenSelector at hselector
    rcases Option.bind_eq_some_iff.mp hselector with ⟨r', hr', hmap⟩
    rcases Option.map_eq_some_iff.mp hmap with ⟨cp, hcp, hdata⟩
    cases hdata
    exact ⟨hr', hcp⟩
  have hlive := ReferenceOriginalCalendarRetainedBranchPartition.firstRecordSelector_cell
    rate r c payload hparts.2
  rw [ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt,
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell,
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt,
    hparts.1]
  simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hlive]

private def actualFirstWeightedArrival : X → ℝ := fun z =>
  ∑ i : Fin p.K, theta i * actualFirstRawArrival rate rewards C_star C_h q i z

private theorem actualFirstWeightedArrival_measurable :
    Measurable (actualFirstWeightedArrival rate rewards C_star C_h q) := by
  apply Finset.measurable_fun_sum Finset.univ
  intro i hi
  exact measurable_const.mul (actualFirstRawArrival_measurable rate rewards C_star C_h q i)

include control0 in
private theorem firstWeightedArrival_eq_actualSelector_indicator :
    firstWeightedArrival rate rewards C_star C_h q = Set.indicator A
      (actualFirstWeightedArrival rate rewards C_star C_h q) := by
  funext z
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem hz]
    simp only [firstWeightedArrival]
    rw [Set.indicator_of_mem hz]
    change (∑ i : Fin p.K, theta i *
        match ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
            rate rewards C_star C_h q z with
        | none => 0
        | some c => RecordedRoundMoments.rawEstimate (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.initialState p.K) c i) = _
    rw [selector_actualCell_eq_continuing rate rewards C_star C_h control0 q z hz]
    simp only [actualFirstWeightedArrival, actualFirstRawArrival]
    apply Finset.sum_congr rfl
    intro i hi
    cases hcell : ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell
        rate rewards C_star C_h q z with
    | none => rfl
    | some c =>
        change theta i * RecordedRoundMoments.rawEstimate
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.initialState p.K) c i =
          theta i * initialRawCoordinate (p := p) rate i
            (ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates c)
        rw [rawEstimate_initial_eq_coordinate (rate := rate) c i]
  · simp [firstWeightedArrival, Set.indicator_of_notMem hz]

include control0 in
public theorem firstWeightedArrival_measurable :
    Measurable (firstWeightedArrival rate rewards C_star C_h q) := by
  rw [firstWeightedArrival_eq_actualSelector_indicator rate rewards C_star C_h control0 q]
  exact (actualFirstWeightedArrival_measurable rate rewards C_star C_h q).indicator
    (measurableSet_firstSelectorEvent rate rewards C_star C_h control0 q)


include control0 in
private theorem firstReadout_bounds (j : Fin (M p))
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q))
    (i : Fin p.K) :
    0 ≤ firstReadout j q control0 z i ∧ firstReadout j q control0 z i ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
  let rho : ℝ := ((rewards q i).val : ℝ) / (ConstructorDimensions.D p : ℝ)
  let xi : ℝ := CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) i
  let value : ℝ := QuantizedRecordingMoments.quantizedValue
    (ConstructorDimensions.D p) rate.eta.val xi rho
  have hD : 0 < (ConstructorDimensions.D p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.D_pos p)
  have hrho : rho ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [rho]
    refine ⟨div_nonneg (Nat.cast_nonneg _) hD.le, (div_le_one hD).2 ?_⟩
    exact_mod_cast Nat.le_of_lt_succ (rewards q i).isLt
  have hbeta : 0 < CanonicalRecordingRates.beta p rate.eta.val :=
    CanonicalRecordingRates.beta_pos p rate.eta.property
  have hxi : 0 < xi := by
    exact CanonicalRecordingRates.xi_pos p rate.eta.property (fun _ => 1) i
  have hbetaxi : CanonicalRecordingRates.beta p rate.eta.val ≤ xi :=
    CanonicalRecordingRates.beta_le_xi p rate.eta.property (fun _ => 1) i
  have hvalue_nonneg := QuantizedRecordingMoments.quantizedValue_nonneg
    (ConstructorDimensions.D p) rate.eta.val xi rho rate.eta.property
  have hvalue_bound := QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
    (ConstructorDimensions.D p) rate.eta.val xi rho
    (CanonicalRecordingRates.beta p rate.eta.val)
    (ConstructorDimensions.D_pos p) rate.eta.property hxi hrho hbeta hbetaxi
  have hreadout := ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout_eq_sourceMarker
    rate rewards C_star C_h j q control0 z i
  change firstReadout j q control0 z i =
    (if ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
      rate rewards C_star C_h j q control0 z = some i then value else 0) at hreadout
  by_cases hmarker : ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
      rate rewards C_star C_h j q control0 z = some i
  · rw [hreadout, ite_eq_left hmarker]
    exact ⟨hvalue_nonneg, hvalue_bound⟩
  · rw [hreadout, ite_eq_right hmarker]
    exact ⟨by norm_num, (one_div_pos.mpr hbeta).le⟩

include control0 in
private theorem firstWeightedArrival_bound_on_event (z : X) (hz : z ∈ A) :
    0 ≤ firstWeightedArrival rate rewards C_star C_h q z ∧
      firstWeightedArrival rate rewards C_star C_h q z ≤
        (p.m : ℝ) / CanonicalRecordingRates.beta p rate.eta.val := by
  have hA := ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent_eq_sourcePhase
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (q := q)
    (a := ⟨0, ConstructorDimensions.K_pos p⟩)
  have hphase : z ∈ phase 2 := by rw [← hA]; exact hz
  have hcover := ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_birth_iUnion
    rate rewards C_star C_h q
  rw [hcover] at hphase
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hphase
  let zz : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q) := ⟨z, hj⟩
  have heq := first_arrival_on_sourceStratum rate rewards C_star C_h control0 q j zz
  have hsumtheta : (∑ i : Fin p.K, theta i) = (p.m : ℝ) :=
    ProductSetLaw.sum_theta_eq_card (fun _ : Fin p.K => (1 : ℝ))
      (ConstructorDimensions.m_pos p) p.m_lt_K (by intro i; norm_num)
  have htheta (i : Fin p.K) : 0 ≤ theta i :=
    (ProductSetLaw.theta_pos (fun _ : Fin p.K => (1 : ℝ)) i
      (ConstructorDimensions.m_pos p) p.m_lt_K (by intro a; norm_num)).le
  have hY (i : Fin p.K) := firstReadout_bounds rate rewards C_star C_h control0 q j zz i
  change firstWeightedArrival rate rewards C_star C_h q z = _ at heq
  rw [heq]
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (htheta i) (hY i).1
  · calc
      _ ≤ ∑ i : Fin p.K, theta i *
          (1 / CanonicalRecordingRates.beta p rate.eta.val) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hY i).2 (htheta i))
      _ = (p.m : ℝ) / CanonicalRecordingRates.beta p rate.eta.val := by
        rw [← Finset.sum_mul, hsumtheta]
        ring

include control0 in
public theorem firstWeightedArrival_integrable :
    Integrable (firstWeightedArrival rate rewards C_star C_h q) mu := by
  have hmeas := firstWeightedArrival_measurable rate rewards C_star C_h control0 q
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    ((p.m : ℝ) / CanonicalRecordingRates.beta p rate.eta.val)
  filter_upwards [] with z
  by_cases hz : z ∈ A
  · rw [Real.norm_eq_abs, abs_of_nonneg
      (firstWeightedArrival_bound_on_event rate rewards C_star C_h control0 q z hz).1]
    exact (firstWeightedArrival_bound_on_event rate rewards C_star C_h control0 q z hz).2
  · have hconst : 0 ≤ (p.m : ℝ) / CanonicalRecordingRates.beta p rate.eta.val :=
      div_nonneg (Nat.cast_nonneg _) (CanonicalRecordingRates.beta_pos p rate.eta.property).le
    simpa [firstWeightedArrival, Set.indicator_of_notMem hz] using hconst

include control0 in
private theorem integral_firstWeightedArrival_on_stratum_le
    (j : Fin (M p)) :
    (∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q),
      firstWeightedArrival rate rewards C_star C_h q z.val ∂
        ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)) ≤
      (p.m : ℝ) *
        (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)).real Set.univ := by
  let Z := ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
    (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)
  let μZ := ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
    (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)
  let μC := ReferenceRetainedSourceCoupling.retainedRemainderMeasure rate rewards C_star C_h
    j q q.val le_rfl control0
  have hmass : μZ Set.univ = μC Set.univ := by
    have hmap := ReferenceFirstLaunchRecordingSourceLaw.map_sourceCoordinates
      rate rewards C_star C_h j q control0
    have h := congrArg (fun η => η Set.univ) hmap
    rw [Measure.map_apply
      (ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
        rate rewards C_star C_h j q control0) MeasurableSet.univ,
      Set.preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod] at h
    simpa only [MeasureTheory.measure_univ, mul_one] using h
  have hmassReal : (μZ Set.univ).toReal = (μC Set.univ).toReal :=
    congrArg ENNReal.toReal hmass
  have hcoordset : {z : Z |
      (ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
        rate rewards C_star C_h j q control0 z).1 ∈ Set.univ ∧
      (ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
        rate rewards C_star C_h j q control0 z).2.1 ∈ Set.univ} = Set.univ := by
    ext z
    simp
  have hassign : (ContinuousControlSlice.assignmentLaw p.K Set.univ).toReal = 1 := by simp
  have hbound (i : Fin p.K) :
      (∫ z : Z, ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h j q control0 z i ∂μZ) ≤ (μZ Set.univ).toReal := by
    let rho : ℝ := ((rewards q i).val : ℝ) / (ConstructorDimensions.D p : ℝ)
    let xi : ℝ := CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) i
    let value := QuantizedRecordingMoments.quantizedValue
      (ConstructorDimensions.D p) rate.eta.val xi rho
    have hmoment' := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
      rate rewards C_star C_h j q control0 i Set.univ Set.univ
      MeasurableSet.univ MeasurableSet.univ
    have hset : {z : Z |
        (ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
          rate rewards C_star C_h j q control0 z).1 ∈ Set.univ ∧
        (ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
          rate rewards C_star C_h j q control0 z).2.1 ∈ Set.univ} = Set.univ := hcoordset
    have hmean' := hmoment'.2.2.2.2.1
    rw [hset, setIntegral_univ, hassign] at hmean'
    simp only [mul_one] at hmean'
    have hcoeff : xi * value ≤ 1 := by
      have hc := ReferenceFirstLaunchCommonUpdateSource.first_update_moment_coefficients_bounds
        rate rewards q i
      have hrho : rho ≤ 1 := by
        dsimp [rho]
        apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
        exact_mod_cast Nat.le_of_lt_succ (rewards q i).isLt
      dsimp [xi, value, rho]
      exact hc.2.1.trans hrho
    have hnonneg : 0 ≤ (μC Set.univ).toReal := MeasureTheory.measureReal_nonneg
    have hbound' : (μC Set.univ).toReal * (xi * value) ≤ (μC Set.univ).toReal :=
      mul_le_of_le_one_right hnonneg hcoeff
    calc
      _ = (μC Set.univ).toReal * (xi * value) := by
        calc
          _ = (μC Set.univ).toReal * xi * value := by
            simpa only [rho, xi, value] using hmean'
          _ = _ := by ring
      _ ≤ (μZ Set.univ).toReal := by
        calc
          _ ≤ (μC Set.univ).toReal := hbound'
          _ = (μZ Set.univ).toReal := hmassReal.symm
  have htheta (i : Fin p.K) : 0 ≤ theta i :=
    (ProductSetLaw.theta_pos (fun _ : Fin p.K => (1 : ℝ)) i
      (ConstructorDimensions.m_pos p) p.m_lt_K (by intro a; norm_num)).le
  have hsum := ProductSetLaw.sum_theta_eq_card (fun _ : Fin p.K => (1 : ℝ))
    (ConstructorDimensions.m_pos p) p.m_lt_K (by intro i; norm_num)
  have hInt (i : Fin p.K) : Integrable
      (fun z : Z => theta i * ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
        rate rewards C_star C_h j q control0 z i) μZ := by
    have hm := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
      rate rewards C_star C_h j q control0 i Set.univ Set.univ
      MeasurableSet.univ MeasurableSet.univ
    exact hm.2.2.1.const_mul (theta i)
  rw [show (fun z : Z => firstWeightedArrival rate rewards C_star C_h q z.val) =
      fun z : Z => ∑ i : Fin p.K, theta i *
        ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
          rate rewards C_star C_h j q control0 z i by
        funext z
        exact first_arrival_on_sourceStratum rate rewards C_star C_h control0 q j z]
  rw [integral_finsetSum Finset.univ (fun i _ => hInt i)]
  calc
    _ ≤ ∑ i : Fin p.K, theta i * (μZ Set.univ).toReal := by
      apply Finset.sum_le_sum
      intro i hi
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hbound i) (htheta i)
    _ = (p.m : ℝ) * (μZ Set.univ).toReal := by
      rw [← Finset.sum_mul, hsum]


private abbrev FirstReadout :=
  ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K

private def firstStateFromReadout (r : FirstReadout (p := p)) :
    RecordedQueueRun.RunState p.K :=
  { registers := r.1, overflow := r.2.1, records := r.2.2 }

private theorem firstStateFromReadout_stateReadout (state : RecordedQueueRun.RunState p.K) :
    firstStateFromReadout (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout state) =
      state := by
  cases state
  rfl

private theorem V_measurable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (n : ℕ) :
    Measurable (ReferenceOriginalCalendarLiveCollectionWeightedDrift.V rate rewards C_star C_h n) := by
  let P := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
    rate rewards C_star C_h
  let f : FirstReadout (p := p) → ℝ := fun r =>
    RecordedWeightedDrift.weightedSquarePotential p.m
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) (firstStateFromReadout r)
  have hf : Measurable f := by
    dsimp [f, firstStateFromReadout]
    unfold RecordedWeightedDrift.weightedSquarePotential
      RecordedQueueRun.scoreWeight StoppedQueueBound.normalizedBacklog
      ProductSetLaw.theta FiniteNormalization.mass FiniteNormalization.normalizedWeight
      FiniteNormalization.totalMass ProductSetLaw.setWeight ProductSetLaw.support
      ScoreWeights.scoreWeight
    fun_prop
  have hopt : @Measurable (Option (FirstReadout (p := p))) ℝ
      (ReferenceInitializationMeasurability.optionCountableMeasurableSpace _)
      Real.measurableSpace (fun o => o.elim 0 f) := by
    intro s hs
    exact MeasurableSpace.measurableSet_top
  have hP := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
    rate rewards C_star C_h n
  have hEq : (fun z : X => (P n z).elim 0 f) =
      ReferenceOriginalCalendarLiveCollectionWeightedDrift.V rate rewards C_star C_h n := by
    funext z
    cases hinputs : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h n z with
    | none =>
        simp [P, f, ReferenceOriginalCalendarLiveCollectionWeightedDrift.V,
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hinputs]
    | some past =>
        simp [P, f, ReferenceOriginalCalendarLiveCollectionWeightedDrift.V,
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout, hinputs,
          firstStateFromReadout_stateReadout]
  rw [← hEq]
  exact hopt.comp hP

/-- Ambient measurability of the actual first-selector weighted square
increment on the unchanged original source. -/
public theorem firstWeightedDelta_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) : Measurable (firstWeightedDelta rate rewards C_star C_h q) := by
  unfold firstWeightedDelta
  have hdelta : Measurable (ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV
      rate rewards C_star C_h q) := by
    unfold ReferenceOriginalCalendarLiveCollectionWeightedDrift.deltaV
    exact (V_measurable rate rewards C_star C_h (q.val + 1)).sub
      (V_measurable rate rewards C_star C_h q.val)
  exact hdelta.indicator
    (ReferenceOriginalCalendarFirstBranchIncrementTransport.measurableSet_firstSelectorEvent
      rate rewards C_star C_h control0 q ⟨0, ConstructorDimensions.K_pos p⟩)

include control0 in
/-- The actual first-selector weighted raw-arrival budget on the whole
original source law, with exactly the first-selector event mass. -/
public theorem firstWeightedArrival_integral_le_event_mass :
    (∫ z : X, firstWeightedArrival rate rewards C_star C_h q z ∂mu) ≤
      (p.m : ℝ) * (sourceInputLaw p).real A := by
  classical
  let f : X → ℝ := firstWeightedArrival rate rewards C_star C_h q
  let S : Fin (M p) → Set X := fun j =>
    ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h q
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)
  have hf : Integrable f mu := by
    dsimp [f]
    exact firstWeightedArrival_integrable rate rewards C_star C_h control0 q
  have hmeas (j : Fin (M p)) : MeasurableSet (S j) :=
    ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h q control0
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)
  have hdis : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    apply ReferenceTotalSourcePairCoupling.sourceStratumEvent_disjoint
    intro heq
    apply hij
    exact congrArg Prod.fst heq
  have hunion := ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_birth_iUnion
    rate rewards C_star C_h q
  have hA := ReferenceOriginalCalendarFirstBranchIncrementTransport.firstSelectorEvent_eq_sourcePhase
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (q := q)
    (a := ⟨0, ConstructorDimensions.K_pos p⟩)
  have hUnion : (⋃ j : Fin (M p), S j) = A := hunion.symm.trans hA.symm
  have hmeasUnion : MeasurableSet (⋃ j : Fin (M p), S j) :=
    MeasurableSet.iUnion fun j => hmeas j
  have hzero (z : X) (hz : z ∉ ⋃ j : Fin (M p), S j) : f z = 0 := by
    have hzA : z ∉ A := by rw [← hUnion]; exact hz
    simp [f, firstWeightedArrival, Set.indicator_of_notMem hzA]
  have hdecomp : f = (⋃ j : Fin (M p), S j).indicator f := by
    funext z
    by_cases hz : z ∈ ⋃ j : Fin (M p), S j
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz, hzero z hz]
  have hmass (j : Fin (M p)) :
      (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)).real Set.univ =
        (sourceInputLaw p).real (S j) := by
    let f0 : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q) → X := Subtype.val
    let hm := ReferenceTotalSourceDisintegration.sourceStratumMeasure_map
      rate rewards C_star C_h q control0
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)
    calc
      _ = Measure.real
          ((ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)).map f0) Set.univ := by
          symm
          simpa [f0] using map_measureReal_apply
            (measurable_subtype_coe : Measurable f0) MeasurableSet.univ
      _ = ((sourceInputLaw p).restrict (S j)).real Set.univ := by
          exact congrArg (fun η : Measure X => η.real Set.univ)
            (by simpa [f0, S] using hm)
      _ = (sourceInputLaw p).real (S j) := by simp
  calc
    _ = ∫ z, f z ∂mu := by rfl
    _ = ∫ z, (⋃ j : Fin (M p), S j).indicator f z ∂mu :=
      congrArg (fun g : X → ℝ => ∫ z, g z ∂mu) hdecomp
    _ = ∫ z in ⋃ j : Fin (M p), S j, f z ∂mu :=
      integral_indicator (μ := mu) (f := f) hmeasUnion
    _ = ∑ j : Fin (M p), ∫ z in S j, f z ∂mu := by
      exact integral_iUnion_fintype (μ := mu) (s := S) hmeas hdis
        (fun _ => hf.integrableOn)
    _ = ∑ j : Fin (M p),
        ∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q),
          f z.val ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (integral_subtype_comap (hmeas j) f).symm
    _ ≤ ∑ j : Fin (M p), (p.m : ℝ) *
        (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)).real Set.univ :=
      Finset.sum_le_sum (fun j _ =>
        integral_firstWeightedArrival_on_stratum_le rate rewards C_star C_h control0 q j)
    _ = (p.m : ℝ) * ∑ j : Fin (M p),
          (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h q
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j q)).real Set.univ := by
      rw [← Finset.mul_sum]
    _ = (p.m : ℝ) * (sourceInputLaw p).real (⋃ j : Fin (M p), S j) := by
      congr 1
      calc
        _ = ∑ j : Fin (M p), (sourceInputLaw p).real (S j) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hmass j
        _ = (sourceInputLaw p).real (⋃ j : Fin (M p), S j) :=
          (measureReal_iUnion_fintype (μ := mu) hdis hmeas
            (fun _ => by finiteness)).symm
    _ = (p.m : ℝ) * (sourceInputLaw p).real A := by rw [hUnion]

end Bandits.Support.ReferenceOriginalCalendarFirstWeightedTransport

end
