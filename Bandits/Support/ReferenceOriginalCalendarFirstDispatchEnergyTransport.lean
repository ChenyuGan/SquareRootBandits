/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project contributors
-/
module

public import Bandits.Support.ReferenceOriginalCalendarCarriedStoppedEnergy
public import Bandits.Support.ReferenceFirstLaunchEnergyInitialization

import Mathlib.Tactic

/-!
# Original-calendar energy transport at the initial first dispatch

These internal estimates compare the carried energy of the original numerical
prefix with the inclusive first update on each actual initial-launch stratum,
then integrate over the whole initial-launch phase of the original source law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceOriginalCalendarFirstDispatchEnergyTransport

open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix (prefixInputs prefixReadout)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open ReferenceSourcePrefixHistoryFiltration (actualLaunchBy actualRecord)

private theorem getElem?_takeWhile_eq {α : Type*} (test : α → Bool) :
    ∀ (xs : List α) (k : ℕ), k < (xs.takeWhile test).length →
      xs[k]? = (xs.takeWhile test)[k]? := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro k hk
      by_cases htest : test x
      · cases k with
        | zero => simp [List.takeWhile, htest]
        | succ k =>
            have hk' : k < (xs.takeWhile test).length := by
              simpa [List.takeWhile, htest] using hk
            simpa [List.takeWhile, htest] using ih k hk'
      · simp [List.takeWhile, htest] at hk

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
  (t : Fin p.T) (a : Fin p.K) (q : Fin (ConstructorDimensions.M p))

local notation "X" => SourceInput p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "muZ" => ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
  (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "PI" => prefixInputs rate rewards C_star C_h
local notation "P" => prefixReadout rate rewards C_star C_h
local notation "firstCell" => ReferenceFirstLaunchCommonUpdateSource.firstCell
  rate rewards C_star C_h q t control0
local notation "firstUpdate" => ReferenceFirstLaunchCommonUpdateSource.firstUpdate
  rate rewards C_star C_h q t control0
local notation "energy" => ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
  rate rewards C_star C_h
local notation "sourceRecords" => ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
  rate rewards C_star C_h
local notation "sourceStart" => ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
  rate rewards C_star C_h

/-- The initial physical update is the same singleton update in the original
carried prefix. The incoming empty state and enabled cell are derived from the
actual source stratum. -/
theorem carried_initial_first_update_transport (z : Z) :
    PI t.val z.val = some [] ∧
    ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt rate rewards C_star C_h t z.val =
      some (firstCell z) ∧
    PI (t.val + 1) z.val = some [firstCell z] ∧
    P (t.val + 1) z.val = some (stateReadout (firstUpdate z)) ∧
    energy t.val a z.val = 1 ∧
    energy (t.val + 1) a z.val =
      ReferenceFirstLaunchEnergyInitialization.birthBacklogExponential
        rate rewards C_star C_h q t control0 a z ∧
    (stateReadout (RecordedQueueRun.run Q
      ([] : List (RecordedQueueRun.RoundInput p.K)))).2.1 = false ∧
    (firstCell z).enabled = true := by
  classical
  let source : X := z.val
  let hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true :=
    z.property.2.1
  have hcrossGenerated : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate source rewards C_star C_h).crossing.isSome = true := by
    simpa [ReferenceCompletePhysicalHistory.generatedInput,
      ReferenceCompletePhysicalHistory.generatedBoundary] using hcross
  let count : ℕ := p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  let hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T :=
    ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseSpan rate rewards C_star C_h source
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hcross count hspan
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hcross count hspan
  have helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = t.val :=
    ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq rate rewards C_star C_h q t z
  have hstart : sourceStart source = t.val := by
    change ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = t.val
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using helapsed
  have hwindowRecords := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
    rate rewards C_star C_h source hcross
  have hwindow : W = ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h) := by
    dsimp [W, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow]
    rw [← hwindowRecords]
  have htake := ReferenceFirstLiveCalendarPrefixReadout.firstWindowBirthCells_take_one
    rate rewards C_star C_h q t control0 z
  have hcellsEq : ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source = cells := by
    change (if hc : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing.isSome = true then
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate source rewards C_star C_h
        hc count (by
          change ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
            (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) ≤ p.T
          exact (Nat.add_sub_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate source rewards C_star C_h)).le) else []) = cells
    rw [dif_pos hcrossGenerated]
  have hcellsPos : 0 < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source).length := by
    apply List.length_pos_of_ne_nil
    intro hempty
    rw [hempty] at htake
    simp at htake
  have hwindowPos : 0 < W.length := by
    have hlen := ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
      rate rewards C_star C_h source
    unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow at hlen
    rw [← hwindow] at hlen
    omega
  have hphysicalStart :
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = t.val := by
    change ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = t.val at hstart
    exact hstart
  have hfirstCell? : cells[0]? = some (firstCell z) := by
    have htakeCells : cells.take 1 = [firstCell z] := by
      simpa only [source, hcellsEq] using htake
    have h := congrArg (fun xs : List (RecordedQueueRun.RoundInput p.K) => xs[0]?) htakeCells
    simpa only [List.getElem?_take_of_lt (by omega : 0 < 1), List.getElem?_cons_zero] using h
  have hfirstCell : cells[0]'(by
      rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
      exact hwindowPos) = firstCell z := by
    have h := hfirstCell?
    rw [List.getElem?_eq_getElem (by
      rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
      exact hwindowPos)] at h
    exact Option.some.inj h
  obtain ⟨_, hstartPos, hraw⟩ :=
    ReferenceCompleteFirstPhaseObservationRecovery.actualFirstLiveRawObservationIdentity
      rate rewards C_star C_h source hcross
  let k : Fin W.length := ⟨0, hwindowPos⟩
  have hraw0 := hraw k
  dsimp only at hraw0
  rcases hraw0 with ⟨_, _, _, _, _, _, hlive, hcollection, _, _, _, hcellEnabled, _, _, _, _⟩
  have hrecord : actualRecord rate rewards C_star C_h t source = some (W[0]'hwindowPos) := by
    let test := fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      !ReferenceCollectionPhaseHistory.cutoffChosen r.input
    have hwindowLength :
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).takeWhile test).length = W.length := by
      change (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)).length = W.length
      rw [← hwindow]
    have hlookup := getElem?_takeWhile_eq test
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
      0 (by rw [hwindowLength]; exact hwindowPos)
    have hlookup' :
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)[0]? =
          some (W[0]'hwindowPos) := by
      calc
        _ = (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h))[0]? := hlookup
        _ = some (W[0]'hwindowPos) := by
          rw [← hwindow]
          exact List.getElem?_eq_getElem hwindowPos
    unfold actualRecord
    rw [hphysicalStart]
    simpa only [Nat.sub_self, if_pos le_rfl] using hlookup'
  have hcell0 : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate (W[0]'hwindowPos) =
      some (firstCell z) := by
    have hlive' : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
        (W[0]'hwindowPos) = some (cells[0]'(by
          rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
          exact hwindowPos)) := by
      simpa only [k, Fin.val_mk] using hlive
    have hcollection' : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
        (W[0]'hwindowPos) = none := by
      simpa only [k, Fin.val_mk] using hcollection
    change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 (W[0]'hwindowPos)).or
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 (W[0]'hwindowPos)) = _
    rw [hlive', hcollection', hfirstCell]
    rfl
  have hactualCell :
      ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt rate rewards C_star C_h t source =
        some (firstCell z) := by
    unfold ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
    rw [hrecord]
    simp only [Option.bind_some, hcell0]
  have hlaunch : actualLaunchBy rate rewards C_star C_h t.val source := by
    change (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).crossing.isSome = true ∧
      sourceStart source ≤ t.val
    rw [hstart]
    exact ⟨hcrossGenerated, le_rfl⟩
  have hprefix : PI t.val source = some [] := by
    change (if actualLaunchBy rate rewards C_star C_h t.val source then
      (((sourceRecords source).take (t.val - sourceStart source)).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id else none) = some []
    rw [if_pos hlaunch, hstart]
    simp only [Nat.sub_self, List.take_zero, List.map_nil, List.mapM_nil]
    rfl
  have hsourceLookup :
      (sourceRecords source)[t.val - sourceStart source]? = some (W[0]'hwindowPos) := by
    let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    change records[t.val - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h]? =
      some (W[0]'hwindowPos)
    rw [hphysicalStart]
    have hrecord' := hrecord
    unfold actualRecord at hrecord'
    rw [hphysicalStart] at hrecord'
    simpa only [if_pos le_rfl] using hrecord'
  have hprefixNext := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
    rate rewards C_star C_h t.val source [] hprefix (W[0]'hwindowPos) (firstCell z)
    hsourceLookup hcell0
  have hprefixOne : PI (t.val + 1) source = some [firstCell z] := by
    simpa using hprefixNext
  have hreadout : P (t.val + 1) source = some (stateReadout (firstUpdate z)) := by
    have hrun := ReferenceFirstLaunchCommonUpdateSource.source_first_chronological_execute
      rate rewards C_star C_h q t control0 z
    rw [(ReferenceFirstLaunchCommonUpdateSource.source_first_cell_chronological
      rate rewards C_star C_h q t control0 z).2.1] at hrun
    have hrunOne : RecordedQueueRun.run Q [firstCell z] = firstUpdate z := by
      change RecordedQueueRun.execute Q [firstCell z]
        (RecordedQueueRun.initialState p.K) = firstUpdate z
      exact hrun
    change (PI (t.val + 1) source).map
      (fun inputs => stateReadout (RecordedQueueRun.run Q inputs)) = _
    simpa only [hprefixOne, Option.map_some, hrunOne]
  have henergyIn : energy t.val a source = 1 := by
    rw [← hstart]
    exact ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy_sourceStart
      rate rewards C_star C_h source a hcross
  have hcarry := ReferenceOriginalCalendarCarriedStoppedEnergy.carriedPrefixReadout_of_present
    rate rewards C_star C_h (t.val + 1) source (stateReadout (firstUpdate z)) hreadout
  have henergyOut : energy (t.val + 1) a source =
      ReferenceFirstLaunchEnergyInitialization.birthBacklogExponential
        rate rewards C_star C_h q t control0 a z := by
    rw [ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy, hcarry]
    change Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
      (((stateReadout (firstUpdate z)).1 a).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) = _
    rw [ReferenceFirstLaunchEnergyInitialization.birthBacklogExponential]
    congr 1
    simp only [StoppedQueueBound.normalizedBacklog, stateReadout]
    ring
  have hflag : (stateReadout (RecordedQueueRun.run Q
      ([] : List (RecordedQueueRun.RoundInput p.K)))).2.1 = false := by
    simp [stateReadout, RecordedQueueRun.run, RecordedQueueRun.execute,
      RecordedQueueRun.initialState]
  have hcellEn : (firstCell z).enabled = true := by
    have hcellEnabled' : (cells[0]'(by
        rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
        exact hwindowPos)).enabled = true := by
      simpa only [k, Fin.val_mk] using hcellEnabled
    rw [hfirstCell] at hcellEnabled'
    exact hcellEnabled'
  exact ⟨hprefix, hactualCell, hprefixOne, hreadout, henergyIn, henergyOut,
    hflag, hcellEn⟩

include control0 in
/-- The carried-energy increment integrates to at most the unchanged mass of
the entire original initial-launch stratum. -/
theorem integral_carried_initial_increment_le_stratum_mass :
    (∫ z : Z,
      (energy (t.val + 1) a z.val - energy t.val a z.val) ∂muZ) ≤
      (muZ).real Set.univ := by
  have hpoint :
      (fun z : Z => energy (t.val + 1) a z.val - energy t.val a z.val) =
        fun z => Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          StoppedQueueBound.normalizedBacklog Q (firstUpdate z) a) - 1 := by
    funext z
    obtain ⟨_, _, _, _, hbefore, hafter, _, _⟩ :=
      carried_initial_first_update_transport rate rewards C_star C_h control0 t a q z
    simp only [hbefore, hafter,
      ReferenceFirstLaunchEnergyInitialization.birthBacklogExponential]
  rw [hpoint]
  exact ReferenceFirstLiveCalendarExponentialBound.integral_exp_birth_difference_le_mass
    rate rewards C_star C_h q t control0 a

include control0 in
/-- The exact first-launch phase increment is bounded by its original-law
mass after finite, unnormalized disintegration over every selected-index
stratum. -/
theorem integral_carried_initial_increment_le_launch_mass :
    (∫ z in ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t 2,
      energy (t.val + 1) a z - energy t.val a z ∂sourceInputLaw p) ≤
      (sourceInputLaw p).real
        (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2) := by
  classical
  let mu := sourceInputLaw p
  let : IsProbabilityMeasure mu := by
    dsimp [mu]
    exact BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  let f : X → ℝ := fun z => energy (t.val + 1) a z - energy t.val a z
  let S : Fin (ConstructorDimensions.M p) → Set X := fun j =>
    ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)
  have hf : Integrable f mu := by
    dsimp [f, mu]
    have hnext := ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
      rate rewards C_star C_h (t.val + 1) (by omega) a
    have hcurrent := ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
      rate rewards C_star C_h t.val t.isLt.le a
    exact hnext.sub hcurrent
  have hmeas (j : Fin (ConstructorDimensions.M p)) : MeasurableSet (S j) := by
    exact ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
      rate rewards C_star C_h t control0
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)
  have hdis : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    apply ReferenceTotalSourcePairCoupling.sourceStratumEvent_disjoint
    intro heq
    apply hij
    exact congrArg Prod.fst heq
  have hstratum (j : Fin (ConstructorDimensions.M p)) :
      (∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t),
        f z.val ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)) ≤
        (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)).real Set.univ := by
    simpa only [f] using
      integral_carried_initial_increment_le_stratum_mass
        rate rewards C_star C_h control0 t a j
  have hmass (j : Fin (ConstructorDimensions.M p)) :
      (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)).real Set.univ =
          mu.real (S j) := by
    let f0 : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t) → X := Subtype.val
    have hmap := ReferenceTotalSourceDisintegration.sourceStratumMeasure_map
      rate rewards C_star C_h t control0
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)
    calc
      _ = Measure.real
          ((ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)).map f0) Set.univ := by
          symm
          simpa [f0] using map_measureReal_apply
            (measurable_subtype_coe : Measurable f0) MeasurableSet.univ
      _ = (mu.restrict (S j)).real Set.univ := by
          exact congrArg (fun η : Measure X => η.real Set.univ)
            (by simpa [f0, S, mu] using hmap)
      _ = mu.real (S j) := by simp
  have hunion := ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_birth_iUnion
    rate rewards C_star C_h t
  change (∫ z in ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t 2, f z ∂mu) ≤
    mu.real (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2)
  rw [hunion]
  calc
    (∫ z in ⋃ j : Fin (ConstructorDimensions.M p), S j, f z ∂mu) =
        ∑ j : Fin (ConstructorDimensions.M p), ∫ z in S j, f z ∂mu :=
      integral_iUnion_fintype hmeas hdis (fun _ => hf.integrableOn)
    _ = ∑ j : Fin (ConstructorDimensions.M p),
        ∫ z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t),
          f z.val ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (integral_subtype_comap (hmeas j) f).symm
    _ ≤ ∑ j : Fin (ConstructorDimensions.M p),
        (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex j t)).real Set.univ :=
      Finset.sum_le_sum (fun j _ => hstratum j)
    _ = mu.real (⋃ j : Fin (ConstructorDimensions.M p), S j) := by
      calc
        _ = ∑ j : Fin (ConstructorDimensions.M p), mu.real (S j) :=
          Finset.sum_congr rfl (fun j _ => hmass j)
        _ = mu.real (⋃ j : Fin (ConstructorDimensions.M p), S j) :=
          (measureReal_iUnion_fintype (μ := mu) hdis hmeas (fun _ => by finiteness)).symm
end Bandits.Support.ReferenceOriginalCalendarFirstDispatchEnergyTransport

end
