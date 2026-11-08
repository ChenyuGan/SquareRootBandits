/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw
public import Bandits.Support.ReferenceOriginalCalendarCarriedStoppedEnergy
public import Bandits.Support.ReferenceOriginalCalendarCollectionRetainedEnergyStep

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Tactic

/-!
# Original-calendar continuing LIVE retained energy step

The literal continuing-LIVE cell at the current original source date appends
to the inherited stopped queue prefix. The proof restricts its accepted source
MGF to the predictable retained gate and preserves the original source law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceSourcePrefixHistoryFiltration (actualRecord sourcePrefixFiltration)
open ReferenceLaterLiveNumericalReadout (laterLiveReadout)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) :=
  ReferenceOriginalCalendarCollectionRetainedEnergyStep.optionMeasurableSpace

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
local notation "Cell" => RecordedQueueRun.RoundInput p.K
local notation "Readout" => ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K
local notation "P" => ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
  rate rewards C_star C_h
local notation "Inputs" => ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
  rate rewards C_star C_h
local notation "CE" => ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
  rate rewards C_star C_h
local notation "D" => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
  rate rewards C_star C_h

/-! The observable supports and scalar restrictions use the actual LIVE domain,
the sole original prefix readout, and the inherited stopped scalar. -/

public def liveDomain (q : Fin p.T) : Set X :=
  ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
    rate rewards C_star C_h q

public def prefixPresent (q : Fin p.T) : Set X :=
  {z | (P q.val z).isSome = true}

public def retainedSupport (q : Fin p.T) : Set X :=
  liveDomain rate rewards C_star C_h q ∩ prefixPresent rate rewards C_star C_h q

public def priorEnergyGate (q : Fin p.T) : Set X :=
  ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q

public def liveRetainedGate (q : Fin p.T) : Set X :=
  retainedSupport rate rewards C_star C_h q ∩ priorEnergyGate rate rewards C_star C_h q

public def predictableExtension (q : Fin p.T) : Set X :=
  prefixPresent rate rewards C_star C_h q ∩ priorEnergyGate rate rewards C_star C_h q

public def inheritedEnergy (q : Fin p.T) (a : Fin p.K) : X → ℝ :=
  (retainedSupport rate rewards C_star C_h q).indicator (CE q.val a)

public def successorEnergy (q : Fin p.T) (a : Fin p.K) : X → ℝ :=
  (retainedSupport rate rewards C_star C_h q).indicator (CE (q.val + 1) a)

public def liveNormalizedIncrement (q : Fin p.T) (a : Fin p.K) : X → ℝ :=
  (liveRetainedGate rate rewards C_star C_h q).indicator
    (fun z => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
      rate rewards C_star C_h q a z - 4)

public def signedInheritedTerm (q : Fin p.T) (a : Fin p.K) : X → ℝ :=
  (liveDomain rate rewards C_star C_h q).indicator (fun z =>
    CE q.val a z *
      (Real.exp (beta * ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt
        rate rewards C_star C_h q a z) - 1))

/-! The actual LIVE domain and prefix support produce exactly the current
original record and its same `cell0` slot. -/

theorem liveDomain_cell0 (q : Fin p.T) (z : X)
    (hz : z ∈ liveDomain rate rewards C_star C_h q) :
    ∃ r : Record, ∃ c : Cell,
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
        rate rewards C_star C_h q z = some r ∧
      laterLiveReadout 0 r = some c ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell
        rate rewards C_star C_h q z = some c ∧ c.enabled = true ∧
      ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
        rate rewards C_star C_h q z = some c := by
  have hD := hz
  obtain ⟨r, hr, _hin, hsome⟩ := hD
  obtain ⟨c, hread⟩ := Option.isSome_iff_exists.mp hsome
  have hcell0 : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
    simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hread]
  refine ⟨r, c, hr, hread, hcell0, ?_, ?_, ?_⟩
  · change (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
      rate rewards C_star C_h q z).bind (laterLiveReadout 0) = some c
    rw [hr]
    simp [hread]
  · obtain ⟨rData, _, _, _, cData, _, hrecordData, _, hreadData, _, hen, _, _, _, _⟩ :=
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell_data
        rate rewards C_star C_h q z hz
    have hrEq : rData = r := Option.some.inj (hrecordData.symm.trans hr)
    rw [hrEq] at hreadData
    have hcEq : cData = c := Option.some.inj (hreadData.symm.trans hread)
    subst cData
    exact hen
  · change (actualRecord rate rewards C_star C_h q z).bind
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some c
    change (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
      rate rewards C_star C_h q z).bind
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some c
    rw [hr]
    exact hcell0

/-- The accepted LIVE cell and its per-arm raw values are matched to the same
physical source record. -/
theorem liveDomain_physicalRaw (q : Fin p.T) (z : X)
    (hz : z ∈ liveDomain rate rewards C_star C_h q) :
    ∃ (r : Record) (c : Cell)
      (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r),
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
        rate rewards C_star C_h q z = some r ∧
      laterLiveReadout 0 r = some c ∧ cell.input = c ∧
      c.recordedArm = ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
        r cell.selected.view.payload true ∧
      ∀ a, (∃! owner : Fin p.m,
          SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
            (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a) ∧
        ((a ∉ cell.selected.view.payload.slowSet.1 ∧
          ∃ out, r.output.coordinator.recording = some out ∧
            ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
              (ReferenceActiveHorizonMeasurability.roundRecordCode r) a =
              some (RecordedQueueRun.quantizedArrival Q c a)) ∨
          ∃ i : Fin (p.m - 1), cell.selected.view.payload.assignment.assigned i = a ∧
            (∀ j, cell.selected.view.payload.assignment.assigned j = a → j = i) ∧
            (if (cell.states i).status = .unoccupied then
              ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
                r cell.selected.view.payload i
            else ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time
              (cell.selected.view.payload.downRecord i)
              (r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2) =
              RecordedQueueRun.quantizedArrival Q c a) := by
  obtain ⟨r, c, cell, hrecord, hread, hinput, hmarker, _howners, _hstates,
    _hfollowers, hraw⟩ :=
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell_physical
        rate rewards C_star C_h q z hz
  exact ⟨r, c, cell, hrecord, hread, hinput, hmarker, hraw⟩

theorem presentPrefix_append (q : Fin p.T) (z : X)
    (hz : z ∈ retainedSupport rate rewards C_star C_h q) :
    ∃ L : List Cell, ∃ c : Cell,
      Inputs q.val z = some L ∧
      ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
        rate rewards C_star C_h q z = some c ∧
      Inputs (q.val + 1) z = some (L ++ [c]) ∧
      P q.val z = some (stateReadout (RecordedQueueRun.run Q L)) ∧
      P (q.val + 1) z = some
        (stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)) := by
  have hD : z ∈ liveDomain rate rewards C_star C_h q := hz.1
  have hV : z ∈ prefixPresent rate rewards C_star C_h q := hz.2
  have hPsome : (P q.val z).isSome = true := hV
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hPsome
  obtain ⟨L, hL, _⟩ := Option.map_eq_some_iff.mp ho
  obtain ⟨r, c, hr, hread, hcell0, hactualCell, _hen, hc⟩ :=
    liveDomain_cell0 rate rewards C_star C_h q z hD
  have hlaunch := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch
    rate rewards C_star C_h q.val z L hL
  have hphysical : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ q.val := by
    simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hlaunch.2
  have hslot :
      (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
        rate rewards C_star C_h z)[q.val -
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
            rate rewards C_star C_h z]? = some r := by
    change ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r at hr
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
    rw [ite_eq_left hphysical] at hr
    simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hr
  have hnext := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
    rate rewards C_star C_h q.val z L hL r c hslot hcell0
  refine ⟨L, c, hL, hc, hnext, ?_, ?_⟩
  · simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hL, Option.map_some]
  · simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hnext, Option.map_some,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]

theorem P_measurable (control0 : TimeControl p) (q : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (q.val + 1)] (P q.val) :=
  ReferenceOriginalCalendarCollectionRetainedEnergyStep.P_measurable
    rate rewards C_star C_h control0 q

theorem measurableSet_liveDomain (control0 : TimeControl p) (q : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      (liveDomain rate rewards C_star C_h q) :=
  ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain_measurable
    rate rewards C_star C_h control0 q

theorem measurableSet_prefixPresent (control0 : TimeControl p) (q : Fin p.T) :
    MeasurableSet[sourcePrefixFiltration control0 (q.val + 1)]
      (prefixPresent rate rewards C_star C_h q) := by
  exact ReferenceOriginalCalendarCollectionRetainedEnergyStep.measurableSet_V
    rate rewards C_star C_h control0 q

theorem measurableSet_retainedSupport (control0 : TimeControl p) (q : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] (retainedSupport rate rewards C_star C_h q) :=
  (measurableSet_liveDomain rate rewards C_star C_h control0 q).inter
    (measurableSet_prefixPresent rate rewards C_star C_h control0 q)

theorem measurableSet_priorEnergyGate (control0 : TimeControl p) (q : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] (priorEnergyGate rate rewards C_star C_h q) :=
  ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
    rate rewards C_star C_h control0 q

theorem measurableSet_liveRetainedGate (control0 : TimeControl p) (q : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] (liveRetainedGate rate rewards C_star C_h q) :=
  (measurableSet_retainedSupport rate rewards C_star C_h control0 q).inter
    (measurableSet_priorEnergyGate rate rewards C_star C_h control0 q)

theorem measurableSet_predictableExtension (control0 : TimeControl p) (q : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] (predictableExtension rate rewards C_star C_h q) :=
  (measurableSet_prefixPresent rate rewards C_star C_h control0 q).inter
    (measurableSet_priorEnergyGate rate rewards C_star C_h control0 q)

theorem inheritedEnergy_measurable (control0 : TimeControl p) (q : Fin p.T)
    (a : Fin p.K) : Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] (inheritedEnergy rate rewards C_star C_h q a) := by
  have hB := measurableSet_retainedSupport rate rewards C_star C_h control0 q
  have hE := ReferenceOriginalCalendarCarriedStoppedEnergy.measurable_carriedStoppedEnergy_predictable
    rate rewards C_star C_h control0 q a
  exact hE.indicator hB

theorem energy_integrable (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    Integrable (inheritedEnergy rate rewards C_star C_h q a) mu ∧
      Integrable (successorEnergy rate rewards C_star C_h q a) mu := by
  have hB := ((sourcePrefixFiltration control0).le' (q.val + 1)) _
    (measurableSet_retainedSupport rate rewards C_star C_h control0 q)
  have h0 := ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
    rate rewards C_star C_h q.val (by omega) a
  have h1 := ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
    rate rewards C_star C_h (q.val + 1) (by omega) a
  exact ⟨h0.indicator hB, h1.indicator hB⟩

/-! On retained support the same optional prefix reads the same actual LIVE
cell, including enabled zero-arrival rounds and the terminal successor. -/

theorem liveGate_iff_activeUpdate (q : Fin p.T) (z : X) :
    z ∈ liveRetainedGate rate rewards C_star C_h q ↔
      z ∈ liveDomain rate rewards C_star C_h q ∧
        ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
          rate rewards C_star C_h q z := by
  constructor
  · intro hz
    refine ⟨hz.1.1, ?_⟩
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hz.1.2
    obtain ⟨r, c, _hr, _hread, _hcell0, _hactual, _hen, hc⟩ :=
      liveDomain_cell0 rate rewards C_star C_h q z hz.1.1
    have hP : P q.val z = some o := ho
    have hPC : ReferenceOriginalCalendarCollectionRetainedEnergyStep.P
        rate rewards C_star C_h q.val z = some o := hP
    have hcurrent : ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
        rate rewards C_star C_h q z = some o := by
      calc
        _ = ReferenceOriginalCalendarCollectionRetainedEnergyStep.P
            rate rewards C_star C_h q.val z :=
              (ReferenceOriginalCalendarCollectionRetainedEnergyStep.P_eq_current
                rate rewards C_star C_h q z).symm
        _ = some o := hPC
    rcases hz.2 with ⟨v, hv, hclear⟩
    have hvo : o = v := Option.some.inj (hcurrent.symm.trans hv)
    subst v
    exact ⟨o, c, hP, hc, hclear, _hen⟩
  · rintro ⟨hD, hA⟩
    obtain ⟨o, c, hP, _hc, hclear, _hen⟩ := hA
    have hV : z ∈ prefixPresent rate rewards C_star C_h q := by
      simp [prefixPresent, hP]
    have hPC : ReferenceOriginalCalendarCollectionRetainedEnergyStep.P
        rate rewards C_star C_h q.val z = some o := hP
    have hcurrent : ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
        rate rewards C_star C_h q z = some o := by
      calc
        _ = ReferenceOriginalCalendarCollectionRetainedEnergyStep.P
            rate rewards C_star C_h q.val z :=
              (ReferenceOriginalCalendarCollectionRetainedEnergyStep.P_eq_current
                rate rewards C_star C_h q z).symm
        _ = some o := hPC
    exact ⟨⟨hD, hV⟩, ⟨o, hcurrent, hclear⟩⟩

theorem actualArrival_eq_cell (q : Fin p.T) (a : Fin p.K) (z : X)
    (hz : z ∈ liveDomain rate rewards C_star C_h q) (c : Cell)
    (hc : ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
      rate rewards C_star C_h q z = some c) :
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
      rate rewards C_star C_h q a z =
        RecordedRoundMoments.normalizedQuantizedArrival Q c a := by
  obtain ⟨r, cLive, hrecord, hreadLive, _hcell0, _hactualLive, _henabled, hactualAt⟩ :=
    liveDomain_cell0 rate rewards C_star C_h q z hz
  obtain ⟨rData, _, _, _, cData, _, hrecordData, _, hreadData, hcellData,
    _, _, _, _, _⟩ :=
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell_data
        rate rewards C_star C_h q z hz
  have hr : rData = r := Option.some.inj (hrecordData.symm.trans hrecord)
  rw [hr] at hreadData
  have hcData : cData = cLive := Option.some.inj (hreadData.symm.trans hreadLive)
  have hcLive : cLive = c := Option.some.inj (hactualAt.symm.trans hc)
  have hcData' : cData = c := hcData.trans hcLive
  have hzD : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q := by
    simpa only [liveDomain] using hz
  calc
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
        rate rewards C_star C_h q a z =
        (RecordedQueueRun.quantizedArrival Q cData a : ℝ) / (rate.n : ℝ) := by
          change (D q).indicator (fun z =>
            match ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell
              rate rewards C_star C_h q z with
            | none => 0
            | some c => (RecordedQueueRun.quantizedArrival Q c a : ℝ) / (rate.n : ℝ)) z = _
          rw [Set.indicator_of_mem hzD, hcellData]
    _ = RecordedRoundMoments.normalizedQuantizedArrival Q c a := by
      rw [hcData']
      rfl

theorem normalizedIncrement_eq_live (q : Fin p.T) (a : Fin p.K) (z : X)
    (hz : z ∈ liveRetainedGate rate rewards C_star C_h q) :
    liveNormalizedIncrement rate rewards C_star C_h q a z =
      ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt
        rate rewards C_star C_h q a z := by
  have hA := (liveGate_iff_activeUpdate rate rewards C_star C_h q z).mp hz
  obtain ⟨_, c, _hP, hc, _hf, _hen⟩ := hA.2
  have hraw := actualArrival_eq_cell rate rewards C_star C_h q a z hA.1 c hc
  calc
    liveNormalizedIncrement rate rewards C_star C_h q a z =
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
          rate rewards C_star C_h q a z - 4 := by
            change (liveRetainedGate rate rewards C_star C_h q).indicator
              (fun z => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
                rate rewards C_star C_h q a z - 4) z = _
            exact Set.indicator_of_mem hz _
    _ = RecordedRoundMoments.normalizedQuantizedArrival Q c a - 4 := by rw [hraw]
    _ = ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt
        rate rewards C_star C_h q a z :=
          (ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt_eq
            rate rewards C_star C_h q a z c hA.2 hc).symm

theorem normalizedIncrement_zero_off_liveDomain (q : Fin p.T) (a : Fin p.K) (z : X)
    (hz : z ∉ liveDomain rate rewards C_star C_h q) :
    liveNormalizedIncrement rate rewards C_star C_h q a z = 0 := by
  have hnotG : z ∉ liveRetainedGate rate rewards C_star C_h q := by
    rintro ⟨⟨hD, _⟩, _⟩
    exact hz hD
  change (liveRetainedGate rate rewards C_star C_h q).indicator
    (fun z => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
      rate rewards C_star C_h q a z - 4) z = 0
  exact Set.indicator_of_notMem hnotG _

/-- The LIVE increment is the actual enabled increment restricted by the
predictable prefix-present and pre-overflow gate. -/
theorem liveIncrement_eq_extension (q : Fin p.T) (a : Fin p.K) :
    liveNormalizedIncrement rate rewards C_star C_h q a =
      (predictableExtension rate rewards C_star C_h q).indicator
        (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualIncrement
          rate rewards C_star C_h q a) := by
  funext z
  change (liveRetainedGate rate rewards C_star C_h q).indicator
      (fun z => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
        rate rewards C_star C_h q a z - 4) z =
    (predictableExtension rate rewards C_star C_h q).indicator
      ((liveDomain rate rewards C_star C_h q).indicator
        (fun z => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
          rate rewards C_star C_h q a z - 4)) z
  have hgate : z ∈ liveRetainedGate rate rewards C_star C_h q ↔
      z ∈ liveDomain rate rewards C_star C_h q ∧
        z ∈ predictableExtension rate rewards C_star C_h q := by
    change ((z ∈ liveDomain rate rewards C_star C_h q ∧
        z ∈ prefixPresent rate rewards C_star C_h q) ∧
        z ∈ priorEnergyGate rate rewards C_star C_h q) ↔
      (z ∈ liveDomain rate rewards C_star C_h q ∧
        (z ∈ prefixPresent rate rewards C_star C_h q ∧
          z ∈ priorEnergyGate rate rewards C_star C_h q))
    exact ⟨fun ⟨⟨hD, hV⟩, hH⟩ => ⟨hD, ⟨hV, hH⟩⟩,
      fun ⟨hD, ⟨hV, hH⟩⟩ => ⟨⟨hD, hV⟩, hH⟩⟩
  by_cases hD : z ∈ liveDomain rate rewards C_star C_h q
  · by_cases hJ : z ∈ predictableExtension rate rewards C_star C_h q
    · rw [Set.indicator_of_mem (hgate.mpr ⟨hD, hJ⟩),
        Set.indicator_of_mem hJ, Set.indicator_of_mem hD]
    · rw [Set.indicator_of_notMem (fun hg => hJ (hgate.mp hg).2),
        Set.indicator_of_notMem hJ]
  · have hnotG : z ∉ liveRetainedGate rate rewards C_star C_h q :=
      fun hg => hD (hgate.mp hg).1
    rw [Set.indicator_of_notMem hnotG]
    by_cases hJ : z ∈ predictableExtension rate rewards C_star C_h q
    · rw [Set.indicator_of_mem hJ]
      change 0 = (liveDomain rate rewards C_star C_h q).indicator
        (fun z => ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
          rate rewards C_star C_h q a z - 4) z
      exact (Set.indicator_of_notMem hD _).symm
    · rw [Set.indicator_of_notMem hJ]

/-- Restrict the accepted original-source LIVE exponential law by the
predictable additional gate `V ∩ H`. -/
theorem liveIncrement_exponential_condExp (control0 : TimeControl p)
    (q : Fin p.T) (a : Fin p.K) :
    Integrable (fun z => Real.exp
      (beta * liveNormalizedIncrement rate rewards C_star C_h q a z)) mu ∧
      mu[(fun z => Real.exp
        (beta * liveNormalizedIncrement rate rewards C_star C_h q a z)) | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu]
        fun _ => (1 : ℝ) := by
  let J := predictableExtension rate rewards C_star C_h q
  let f := fun z => Real.exp (beta *
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualIncrement
      rate rewards C_star C_h q a z)
  let fJ := J.indicator f
  let fJc := Jᶜ.indicator (fun _ : X => (1 : ℝ))
  have hJ := measurableSet_predictableExtension rate rewards C_star C_h control0 q
  have hle := (sourcePrefixFiltration control0).le' (q.val + 1)
  have hJa := hle _ hJ
  obtain ⟨hfInt, hfCE⟩ :=
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualIncrement_exponential_condExp
      rate rewards C_star C_h control0 q a
  have hdecomp : (fun z => Real.exp
      (beta * liveNormalizedIncrement rate rewards C_star C_h q a z)) = fJ + fJc := by
    funext z
    by_cases hz : z ∈ J
    · have hx := congrFun (liveIncrement_eq_extension rate rewards C_star C_h q a) z
      rw [hx]
      simp [fJ, fJc, f, J, hz]
    · have hx := congrFun (liveIncrement_eq_extension rate rewards C_star C_h q a) z
      have hcompl : z ∈ Jᶜ := hz
      rw [hx]
      simp [fJ, fJc, f, J, hz, hcompl]
  have hJfInt : Integrable fJ mu := hfInt.indicator hJa
  have hJcInt : Integrable fJc mu := (integrable_const (1 : ℝ)).indicator hJa.compl
  have hExpInt : Integrable (fun z => Real.exp
      (beta * liveNormalizedIncrement rate rewards C_star C_h q a z)) mu := by
    rw [hdecomp]
    exact hJfInt.add hJcInt
  refine ⟨hExpInt, ?_⟩
  have hs := condExp_add hJfInt hJcInt
    (sourcePrefixFiltration control0 (q.val + 1))
  have hJfCE := condExp_indicator (μ := mu)
    (m := sourcePrefixFiltration control0 (q.val + 1)) hfInt hJ
  have hJcCE := condExp_indicator (μ := mu)
    (m := sourcePrefixFiltration control0 (q.val + 1))
    (integrable_const (1 : ℝ)) hJ.compl
  have hone := condExp_const (μ := mu) hle (1 : ℝ)
  rw [hdecomp]
  filter_upwards [hs, hJfCE, hJcCE, hfCE] with z hs hJfCE hJcCE hfCE
  rw [hs, Pi.add_apply, hJfCE, hJcCE, hone]
  change J.indicator (mu[f | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)]) z + Jᶜ.indicator (fun _ : X => (1 : ℝ)) z ≤ 1
  by_cases hz : z ∈ J
  · simp only [Set.indicator_of_mem hz,
      Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hz), add_zero]
    exact hfCE
  · simp only [Set.indicator_of_notMem hz,
      Set.indicator_of_mem (show z ∈ Jᶜ from hz), zero_add]
    exact le_rfl

theorem signedInheritedTerm_eq (q : Fin p.T) (a : Fin p.K) (z : X) :
    signedInheritedTerm rate rewards C_star C_h q a z =
      inheritedEnergy rate rewards C_star C_h q a z *
        (Real.exp (beta * liveNormalizedIncrement rate rewards C_star C_h q a z) - 1) := by
  by_cases hd : z ∈ liveDomain rate rewards C_star C_h q
  · by_cases hg : z ∈ liveRetainedGate rate rewards C_star C_h q
    · have hx := normalizedIncrement_eq_live rate rewards C_star C_h q a z hg
      simp only [signedInheritedTerm, Set.indicator_of_mem hd,
        inheritedEnergy, Set.indicator_of_mem hg.1]
      rw [← hx]
    · have hnotA : ¬ ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
          rate rewards C_star C_h q z := by
        intro hA
        exact hg ((liveGate_iff_activeUpdate rate rewards C_star C_h q z).mpr ⟨hd, hA⟩)
      have hnotG : z ∉ liveRetainedGate rate rewards C_star C_h q := hg
      simp [signedInheritedTerm, hd, inheritedEnergy, liveNormalizedIncrement,
        hnotG, ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt,
        hnotA]
  · have hnotG : z ∉ liveRetainedGate rate rewards C_star C_h q := by
      rintro ⟨⟨hD, _⟩, _⟩
      exact hd hD
    simp [signedInheritedTerm, hd, inheritedEnergy, liveNormalizedIncrement, hnotG]

theorem signedInheritedTerm_condExp (control0 : TimeControl p)
    (q : Fin p.T) (a : Fin p.K) :
    Integrable (signedInheritedTerm rate rewards C_star C_h q a) mu ∧
      mu[signedInheritedTerm rate rewards C_star C_h q a | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu]
        fun _ => (0 : ℝ) := by
  let W := inheritedEnergy rate rewards C_star C_h q a
  let A := fun z => Real.exp
    (beta * liveNormalizedIncrement rate rewards C_star C_h q a z) - 1
  let S := signedInheritedTerm rate rewards C_star C_h q a
  obtain ⟨hWi, _hXi⟩ := energy_integrable rate rewards C_star C_h control0 q a
  obtain ⟨hAi, hACE⟩ := liveIncrement_exponential_condExp
    rate rewards C_star C_h control0 q a
  have hAInt : Integrable A mu := by
    exact hAi.sub (integrable_const (1 : ℝ))
  have hWmeas := inheritedEnergy_measurable rate rewards C_star C_h control0 q a
  have hceil : 0 ≤ ReferenceOriginalCalendarCarriedStoppedEnergy.energyCeiling rate := by
    unfold ReferenceOriginalCalendarCarriedStoppedEnergy.energyCeiling
    exact Real.exp_nonneg _
  have hWnonneg : ∀ z, 0 ≤ W z := by
    intro z
    by_cases hz : z ∈ retainedSupport rate rewards C_star C_h q
    · simp only [W, inheritedEnergy, Set.indicator_of_mem hz]
      exact le_trans (by norm_num)
        (ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy_bounds
          rate rewards C_star C_h q.val (by omega) a z).1
    · simp only [W, inheritedEnergy, Set.indicator_of_notMem hz]
      exact le_rfl
  have hWupper : ∀ z, W z ≤ ReferenceOriginalCalendarCarriedStoppedEnergy.energyCeiling rate := by
    intro z
    by_cases hz : z ∈ retainedSupport rate rewards C_star C_h q
    · simp only [W, inheritedEnergy, Set.indicator_of_mem hz]
      exact (ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy_bounds
        rate rewards C_star C_h q.val (by omega) a z).2
    · simp only [W, inheritedEnergy, Set.indicator_of_notMem hz]
      exact hceil
  have hWA : Integrable (fun z => W z * A z) mu := by
    have hAW : Integrable (fun z => A z * W z) mu := by
      apply hAInt.mul_bdd hWi.aestronglyMeasurable
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg z)]
      exact hWupper z
    convert hAW using 1
    funext z
    exact mul_comm _ _
  have hSignedInt : Integrable S mu := by
    have hEq : S = fun z => W z * A z := by
      funext z
      exact signedInheritedTerm_eq rate rewards C_star C_h q a z
    rw [hEq]
    exact hWA
  have hpull := condExp_mul_of_aestronglyMeasurable_left
    hWmeas.aestronglyMeasurable hWA hAInt
  have hsub := condExp_sub hAi (integrable_const (1 : ℝ))
    (sourcePrefixFiltration control0 (q.val + 1))
  have hone := condExp_const (μ := mu)
    ((sourcePrefixFiltration control0).le' (q.val + 1)) (1 : ℝ)
  rw [hone] at hsub
  have htermCE : mu[S | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] =ᵐ[mu] W * mu[A | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] := by
    have hEq : S = fun z => W z * A z := by
      funext z
      exact signedInheritedTerm_eq rate rewards C_star C_h q a z
    rw [hEq]
    exact hpull
  refine ⟨hSignedInt, ?_⟩
  filter_upwards [htermCE, hsub, hACE] with z hterm hsub hExp
  rw [hterm]
  have hsubA : mu[A | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (q.val + 1)] z =
      mu[(fun z => Real.exp (beta * liveNormalizedIncrement rate rewards C_star C_h q a z)) |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] z - 1 := by
    change mu[(fun z => Real.exp (beta * liveNormalizedIncrement rate rewards C_star C_h q a z) - 1) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] z = _
    exact hsub
  change W z * mu[A | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
    control0 (q.val + 1)] z ≤ 0
  rw [hsubA]
  exact mul_nonpos_of_nonneg_of_nonpos (hWnonneg z) (sub_nonpos.mpr hExp)

theorem signedInheritedTerm_integral_nonpos (control0 : TimeControl p)
    (q : Fin p.T) (a : Fin p.K) :
    (∫ z, signedInheritedTerm rate rewards C_star C_h q a z ∂mu) ≤ 0 := by
  obtain ⟨hInt, hCE⟩ := signedInheritedTerm_condExp rate rewards C_star C_h control0 q a
  have hle := (sourcePrefixFiltration control0).le' (q.val + 1)
  have hi := integral_mono_ae integrable_condExp (integrable_const (0 : ℝ)) hCE
  rw [integral_condExp hle] at hi
  simpa using hi


/-! On the same actual-prefix support, the accepted LIVE cell advances the
queue and retains the first detecting successor. -/

theorem presentPrefix_queue_step (q : Fin p.T) (a : Fin p.K) (z : X)
    (hz : z ∈ retainedSupport rate rewards C_star C_h q) :
    ∃ before after : Readout,
      P q.val z = some before ∧
      P (q.val + 1) z = some after ∧
      ((after.1 a).2 : ℝ) / ((Q).n : ℝ) =
        if z ∈ liveRetainedGate rate rewards C_star C_h q then
          max (((before.1 a).2 : ℝ) / ((Q).n : ℝ) +
            liveNormalizedIncrement rate rewards C_star C_h q a z) 0
        else ((before.1 a).2 : ℝ) / ((Q).n : ℝ) := by
  obtain ⟨L, c, _hL, hc, _happend, hbefore, hafter⟩ :=
    presentPrefix_append rate rewards C_star C_h q z hz
  refine ⟨_, _, hbefore, hafter, ?_⟩
  have hclear : z ∈ priorEnergyGate rate rewards C_star C_h q ↔
      (RecordedQueueRun.run Q L).overflow = false := by
    have hcurrent :=
      (ReferenceOriginalCalendarCollectionRetainedEnergyStep.P_eq_current
        rate rewards C_star C_h q z).symm.trans hbefore
    constructor
    · rintro ⟨v, hv, hflag⟩
      rw [hcurrent] at hv
      have hv' := Option.some.inj hv
      rw [← hv'] at hflag
      simpa only [stateReadout] using hflag
    · intro hflag
      exact ⟨_, hcurrent, by simpa only [stateReadout] using hflag⟩
  by_cases hg : z ∈ liveRetainedGate rate rewards C_star C_h q
  · have hf := hclear.mp hg.2
    have hactive := (liveGate_iff_activeUpdate rate rewards C_star C_h q z).mp hg
    obtain ⟨o, cActive, hP, hcActive, hflag, henabled⟩ := hactive.2
    have hcEq : cActive = c := Option.some.inj (hcActive.symm.trans hc)
    subst cActive
    have hArrival := actualArrival_eq_cell rate rewards C_star C_h q a z hg.1.1 c hc
    have hraw : RecordedRoundMoments.rawEstimate Q (RecordedQueueRun.run Q L) c a =
        ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualArrival
          rate rewards C_star C_h q a z := by
      rw [RecordedRoundMoments.rawEstimate_eq_normalizedQuantizedArrival_of_enabled
        Q (RecordedQueueRun.run Q L) c a henabled hf]
      exact hArrival.symm
    have hstep := CanonicalQueueProcess.normalizedBacklog_step_of_retained
      Q (RecordedQueueRun.run Q L) c a hf henabled
    simpa only [ite_eq_left hg, liveNormalizedIncrement, Set.indicator_of_mem hg, hraw,
      stateReadout, StoppedQueueBound.normalizedBacklog, add_sub_assoc] using hstep
  · have hOverflow : (RecordedQueueRun.run Q L).overflow = true := by
      by_cases hfalse : (RecordedQueueRun.run Q L).overflow = false
      · exact False.elim (hg (⟨hz, hclear.mpr hfalse⟩))
      · cases h : (RecordedQueueRun.run Q L).overflow <;> simp_all
    have hstep := CanonicalQueueProcess.normalizedBacklog_step_of_inactive
      Q (RecordedQueueRun.run Q L) c a (Or.inr hOverflow)
    simpa only [ite_eq_right hg,
      stateReadout, StoppedQueueBound.normalizedBacklog] using hstep

theorem successorEnergy_le_inherited_add_gate_add_signed (q : Fin p.T)
    (a : Fin p.K) (z : X) :
    successorEnergy rate rewards C_star C_h q a z ≤
      inheritedEnergy rate rewards C_star C_h q a z +
        (liveRetainedGate rate rewards C_star C_h q).indicator
          (fun _ : X => (1 : ℝ)) z +
        signedInheritedTerm rate rewards C_star C_h q a z := by
  by_cases hB : z ∈ retainedSupport rate rewards C_star C_h q
  · have hEnergyUpdate :=
      ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy_update_bound
        rate rewards C_star C_h q a z
    have hW : inheritedEnergy rate rewards C_star C_h q a z = CE q.val a z :=
      by
        change (retainedSupport rate rewards C_star C_h q).indicator
          (CE q.val a) z = _
        exact Set.indicator_of_mem hB _
    have hX : successorEnergy rate rewards C_star C_h q a z = CE (q.val + 1) a z :=
      by
        change (retainedSupport rate rewards C_star C_h q).indicator
          (CE (q.val + 1) a) z = _
        exact Set.indicator_of_mem hB _
    by_cases hG : z ∈ liveRetainedGate rate rewards C_star C_h q
    · have hactive := (liveGate_iff_activeUpdate rate rewards C_star C_h q z).mp hG
      have hx := normalizedIncrement_eq_live rate rewards C_star C_h q a z hG
      have hS := signedInheritedTerm_eq rate rewards C_star C_h q a z
      have hS' : signedInheritedTerm rate rewards C_star C_h q a z =
          CE q.val a z * (Real.exp (beta *
            ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt
              rate rewards C_star C_h q a z) - 1) := by
        rw [hS, hW, hx]
      have hGate : (liveRetainedGate rate rewards C_star C_h q).indicator
          (fun _ : X => (1 : ℝ)) z = 1 := Set.indicator_of_mem hG _
      rw [hX, hW, hGate]
      simp only [hactive.2, ite_true] at hEnergyUpdate
      rw [hS']
      linarith
    · have hnotActive : ¬ ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
          rate rewards C_star C_h q z := by
        intro hA
        exact hG ((liveGate_iff_activeUpdate rate rewards C_star C_h q z).mpr
          ⟨hB.1, hA⟩)
      have hxzero : liveNormalizedIncrement rate rewards C_star C_h q a z = 0 :=
        Set.indicator_of_notMem hG _
      have hS := signedInheritedTerm_eq rate rewards C_star C_h q a z
      have hSzero : signedInheritedTerm rate rewards C_star C_h q a z = 0 := by
        rw [hS, hW, hxzero]
        simp
      have hGate : (liveRetainedGate rate rewards C_star C_h q).indicator
          (fun _ : X => (1 : ℝ)) z = 0 := Set.indicator_of_notMem hG _
      rw [hX, hW, hGate, hSzero]
      have hupdate' := hEnergyUpdate
      simp [hnotActive,
        ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt] at hupdate'
      linarith
  · have hnotG : z ∉ liveRetainedGate rate rewards C_star C_h q := by
      rintro ⟨hB', _⟩
      exact hB hB'
    have hS := signedInheritedTerm_eq rate rewards C_star C_h q a z
    simp [successorEnergy, inheritedEnergy, hB, hnotG, hS]

/-- Conditional retained-energy step on the actual continuing-LIVE stratum;
the inherited signed term is discharged by its same-stratum MGF. -/
theorem retained_energy_step (control0 : TimeControl p) (q : Fin p.T)
    (a : Fin p.K) :
    mu[successorEnergy rate rewards C_star C_h q a | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu]
      (fun z => inheritedEnergy rate rewards C_star C_h q a z +
        (liveRetainedGate rate rewards C_star C_h q).indicator
          (fun _ : X => (1 : ℝ)) z) ∧
    (∫ z, successorEnergy rate rewards C_star C_h q a z ∂mu) ≤
      (∫ z, inheritedEnergy rate rewards C_star C_h q a z ∂mu) +
        ∫ z, (liveRetainedGate rate rewards C_star C_h q).indicator
          (fun _ : X => (1 : ℝ)) z ∂mu := by
  let W := inheritedEnergy rate rewards C_star C_h q a
  let gate := (liveRetainedGate rate rewards C_star C_h q).indicator
    (fun _ : X => (1 : ℝ))
  let S := signedInheritedTerm rate rewards C_star C_h q a
  have hle := (sourcePrefixFiltration control0).le' (q.val + 1)
  have hG := measurableSet_liveRetainedGate rate rewards C_star C_h control0 q
  have hGa := hle _ hG
  obtain ⟨hWi, hXi⟩ := energy_integrable rate rewards C_star C_h control0 q a
  obtain ⟨hSi, hSCE⟩ := signedInheritedTerm_condExp
    rate rewards C_star C_h control0 q a
  have hgi : Integrable gate mu := (integrable_const (1 : ℝ)).indicator hGa
  have hWmeas := inheritedEnergy_measurable rate rewards C_star C_h control0 q a
  have hWCE := condExp_of_stronglyMeasurable hle hWmeas.stronglyMeasurable hWi
  have hgateMeas : Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] gate := measurable_const.indicator hG
  have hgateCE := condExp_of_stronglyMeasurable hle hgateMeas.stronglyMeasurable hgi
  have hRInt : Integrable (fun z => W z + gate z + S z) mu :=
    (hWi.add hgi).add hSi
  have hmono := condExp_mono (m := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)) hXi hRInt
    (Filter.Eventually.of_forall
      (successorEnergy_le_inherited_add_gate_add_signed rate rewards C_star C_h q a))
  have hsumWG := condExp_add hWi hgi
    (sourcePrefixFiltration control0 (q.val + 1))
  have hsumS := condExp_add (hWi.add hgi) hSi
    (sourcePrefixFiltration control0 (q.val + 1))
  have hCE : mu[successorEnergy rate rewards C_star C_h q a | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] ≤ᵐ[mu]
      (fun z => W z + gate z) := by
    filter_upwards [hmono, hsumWG, hsumS, hSCE]
      with z hmono hsumWG hsumS hSCE
    have hmono' : mu[successorEnergy rate rewards C_star C_h q a |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] z ≤
      mu[inheritedEnergy rate rewards C_star C_h q a + gate +
        signedInheritedTerm rate rewards C_star C_h q a |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] z := by
      change mu[successorEnergy rate rewards C_star C_h q a |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] z ≤
          mu[W + gate + S |
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] z at hmono
      exact hmono
    calc
      _ ≤ _ := hmono'
      _ = (mu[inheritedEnergy rate rewards C_star C_h q a + gate |
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] +
          mu[signedInheritedTerm rate rewards C_star C_h q a |
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)]) z := hsumS
      _ = (mu[inheritedEnergy rate rewards C_star C_h q a |
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] +
          mu[gate | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] +
          mu[signedInheritedTerm rate rewards C_star C_h q a |
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)]) z := by
              change mu[inheritedEnergy rate rewards C_star C_h q a + gate |
                  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] z +
                mu[signedInheritedTerm rate rewards C_star C_h q a |
                  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] z = _
              rw [hsumWG]
              simp only [Pi.add_apply]
      _ = inheritedEnergy rate rewards C_star C_h q a z + gate z +
          mu[signedInheritedTerm rate rewards C_star C_h q a |
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] z := by
              change mu[inheritedEnergy rate rewards C_star C_h q a |
                  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] z +
                mu[gate | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] z +
                mu[signedInheritedTerm rate rewards C_star C_h q a |
                  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)] z = _
              rw [hWCE, hgateCE]
      _ ≤ inheritedEnergy rate rewards C_star C_h q a z + gate z := by
              simpa only [add_zero] using
                (add_le_add_right hSCE
                  (inheritedEnergy rate rewards C_star C_h q a z + gate z))
  refine ⟨hCE, ?_⟩
  have hi := integral_mono_ae integrable_condExp (hWi.add hgi) hCE
  rw [integral_condExp hle] at hi
  calc
    _ ≤ ∫ z, W z + gate z ∂mu := hi
    _ = (∫ z, W z ∂mu) + ∫ z, gate z ∂mu := integral_add hWi hgi

end Bandits.Support.ReferenceOriginalCalendarContinuingLiveRetainedEnergyStep

end
