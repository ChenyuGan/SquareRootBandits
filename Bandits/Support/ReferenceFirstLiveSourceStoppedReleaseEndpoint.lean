/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePrelaunchInspectedDecoderPast
public import Bandits.Support.ReferenceFirstLiveInspectedNumericalCells
public import Bandits.Support.ReferenceFirstLiveDecoderPastMeasurability
public import Bandits.Support.ReferenceFirstLiveOverflowMeasurability
public import Bandits.Support.ReferenceFirstLiveReleaseDecoderSilence

/-!
# Actual first-live source stopped release endpoint

Sources: `sources/zip4/manuscript/05_binary_transport.tex:293-345,354-431`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-100`.

This file observes the existing complete physical run on the original source.
The release support is clipped at the first excluded calendar round; its
endpoint is proved from the current gate, strict-past decoder flags, and the
strict-past replay of the existing numerical queue.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseEndpoint

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

private theorem measurableSet_option_singleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace] {a} := by
  let e := Equiv.optionEquivSumPUnit α
  have he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e :=
    comap_measurable _
  have hset : ({a} : Set (Option α)) = e ⁻¹' {e a} := by
    ext x
    exact ⟨congrArg e, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e a with
  | inl value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inr_image (α := α)

local instance {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] :
    @MeasurableSingletonClass (Option α) LaterAssignmentStartMeasurability.optionMeasurableSpace :=
  ⟨measurableSet_option_singleton⟩

abbrev Source (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p

/-- The actual initialization endpoint, including the no-launch sentinel. -/
def physicalStart (z : Source p) : ℕ :=
  ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h

/-- The complete actual physical suffix, with no replacement run. -/
def completeRecords (z : Source p) :=
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h

/-- All true gates in the original complete suffix, including empty pending
sets and rounds after every follower has released. -/
def actualGateSupport (z : Source p) : Finset ℕ :=
  ReferenceLocalReleaseGateChronology.gateSupport (physicalStart rate rewards C_star C_h z)
    (completeRecords rate rewards C_star C_h z)

/-- The first and one-past-last actual raw local gates. -/
def actualGateAlpha (z : Source p) : ℕ :=
  ReferenceLocalReleaseGateChronology.gateAlpha (physicalStart rate rewards C_star C_h z)
    (completeRecords rate rewards C_star C_h z)

def actualGateBeta (z : Source p) : ℕ :=
  ReferenceLocalReleaseGateChronology.gateBeta (physicalStart rate rewards C_star C_h z)
    (completeRecords rate rewards C_star C_h z)

/-- The literal current strict-past decoder Boolean, with the original argument
order and the actual launch date. -/
def actualDecoderFlag (z : Source p) (n : ℕ) (hn : n ≤ p.T) : Bool :=
  ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
      rate rewards C_star C_h z n hn ||
    ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag
      rate rewards C_star C_h (physicalStart rate rewards C_star C_h z) n hn z

/-- The first one-based excluded date forced by either literal decoder flag;
the horizon sentinel is included in the minimum. -/
def decoderFirstExcluded (z : Source p) : ℕ := by
  classical
  let bad : Finset ℕ :=
    (((Finset.univ : Finset (Fin p.T)).filter fun n =>
      actualDecoderFlag rate rewards C_star C_h z n.val (Nat.le_of_lt n.isLt) = true).image
        fun n => n.val + 1) ∪ {p.T + 1}
  exact bad.min' ⟨p.T + 1, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩

/-- The overflow exclusion date is one past the first inclusive crossing
round, capped at the horizon sentinel. -/
def overflowFirstExcluded (z : Source p) : ℕ :=
  (ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound rate rewards C_star C_h z).elim
    (p.T + 1) (fun v => min (p.T + 1) (v + 1))

/-- First excluded calendar round. An overflow detector round itself remains
in the support. -/
def firstExcluded (z : Source p) : ℕ :=
  min (decoderFirstExcluded rate rewards C_star C_h z)
    (overflowFirstExcluded rate rewards C_star C_h z)

/-- The original local gate list, restricted to its actual stopped prefix. -/
def actualFirstReleaseSupport (z : Source p) : Finset ℕ :=
  (actualGateSupport rate rewards C_star C_h z).filter
    (fun v => v < firstExcluded rate rewards C_star C_h z)

/-- The stopped pending-set process on the original calendar. The readout is
queried at its original physical date, and is erased only outside the actual
stopped gate support. -/
def firstReleasePending (z : Source p) (t : Fin p.T) : Finset (Fin (p.m - 1)) :=
  if t.val + 1 ∈ actualFirstReleaseSupport rate rewards C_star C_h z then
    ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h
      (physicalStart rate rewards C_star C_h z) t z
  else ∅

/-- The analytical release start and end. The actual gate list remains the
support even when every follower has already released. -/
def firstReleaseSigma (z : Source p) : ℕ :=
  let beta' := min (actualGateBeta rate rewards C_star C_h z)
    (firstExcluded rate rewards C_star C_h z)
  if actualGateAlpha rate rewards C_star C_h z < beta' then
    actualGateAlpha rate rewards C_star C_h z else p.T + 1

def firstReleaseTheta (z : Source p) : ℕ :=
  let beta' := min (actualGateBeta rate rewards C_star C_h z)
    (firstExcluded rate rewards C_star C_h z)
  if actualGateAlpha rate rewards C_star C_h z < beta' then beta' else p.T + 1

/-- Current raw gate membership is exactly the existing source-prefix entry
readout. The empty-pending gate remains true in this equivalence. -/
theorem actual_gate_support_mem_iff_entry (z : Source p) (t : Fin p.T) :
    t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z ↔
      (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
        (physicalStart rate rewards C_star C_h z) t z).map Prod.fst = some true := by
  classical
  by_cases hcross : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate z rewards C_star C_h).crossing.isSome = true
  · let s := physicalStart rate rewards C_star C_h z
    have hcross' : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
      simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput] using hcross
    let active := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross'
    have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h = some active := by
      simpa only [active] using
        ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hcross'
    have hsElapsed : ReferenceInitializationRun.elapsed p
        (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).completed = s := by
      dsimp [s, physicalStart, ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary]
    have hspan : s + (p.T - s) ≤ p.T := by
      have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
      have hs' : s ≤ p.T := by simpa [s, physicalStart] using hs
      omega
    have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart active s := by
      have h := (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
        rate z rewards C_star C_h hcross').2.1
      exact hsElapsed ▸ h
    have hrunRecords :
        (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross'
          s (p.T - s) hsElapsed hspan).records =
            ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h := by
      simpa [s, physicalStart, ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceLocalReleaseGateChronology.sourceRun] using
        (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate z rewards C_star C_h active hlaunch).symm
    have hsupportEq : actualGateSupport rate rewards C_star C_h z =
        ReferenceLocalReleaseGateChronology.gateSupport s
          (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross'
            s (p.T - s) hsElapsed hspan).records := by
      change ReferenceLocalReleaseGateChronology.gateSupport
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) = _
      have hsStart : s = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
        simp [s, physicalStart]
      rw [← hsStart, ← hrunRecords]
    by_cases hbefore : s ≤ t.val
    · have hsourceRecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
        rate rewards C_star C_h t z active hlaunch (by simpa [s, physicalStart] using hbefore)
      have hsourceRecord' : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z = some
            (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
              (t.val - s) (by have ht := t.isLt; omega) hactive) := by
        simpa [s, physicalStart] using hsourceRecord
      have hrecordTime :
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
            (t.val - s) (by have ht := t.isLt; omega) hactive).input.time = t := by
        apply Fin.ext
        simp [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
          ReferenceActivePhysicalHorizon.roundInputAt]
        omega
      have hentry :
          (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s t z).map
              Prod.fst = some true ↔
            ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s t
              (ReferenceActivePhysicalStepMeasurability.encodeState
                (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
                  (t.val - s) (by have ht := t.isLt; omega) hactive).input.state) = true := by
        simp [ReferenceSourcePrefixHistoryFiltration.entry,
          ReferenceSourcePrefixHistoryFiltration.incoming, hsourceRecord',
          ReferenceRetainedReleasePhaseObservation.localReleaseEntry]
      let gateAt : Fin (p.T - s) → Bool := fun j =>
        ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s j.val
            (by have hj := j.isLt; omega) hactive).input.time
          (ReferenceActivePhysicalStepMeasurability.encodeState
            (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s j.val
              (by have hj := j.isLt; omega) hactive).input.state)
      have hmem : t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z ↔
          ∃ j : Fin (p.T - s),
            gateAt j = true ∧
              s + j.val + 1 = t.val + 1 := by
        rw [hsupportEq]
        simpa [gateAt, ReferenceLocalReleaseGateChronology.sourceRun] using
          ReferenceLocalReleaseGateChronology.mem_run_gateSupport active z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s hactive
            (p.T - s) hspan s (t.val + 1)
      constructor
      · intro hgate
        obtain ⟨j, hjgate, hjtime⟩ := hmem.mp hgate
        have hjval : j.val = t.val - s := by omega
        let j₀ : Fin (p.T - s) := ⟨t.val - s, by have ht := t.isLt; omega⟩
        have hjEq : j = j₀ := Fin.ext hjval
        have hgateEq : gateAt j = gateAt j₀ := congrArg gateAt hjEq
        have hcurrent :
            ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s t
              (ReferenceActivePhysicalStepMeasurability.encodeState
                (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
                  (t.val - s) (by have ht := t.isLt; omega) hactive).input.state) = true := by
          have hgateAtJ₀ := hgateEq.symm.trans hjgate
          change ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s
              (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s j₀.val
                (by have hj := j₀.isLt; omega) hactive).input.time
              (ReferenceActivePhysicalStepMeasurability.encodeState
                (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s j₀.val
                  (by have hj := j₀.isLt; omega) hactive).input.state) = true at hgateAtJ₀
          have hgateTime := congrArg
            (fun time => ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s time
              (ReferenceActivePhysicalStepMeasurability.encodeState
                (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
                  (t.val - s) (by have ht := t.isLt; omega) hactive).input.state)) hrecordTime
          exact hgateTime.symm.trans hgateAtJ₀
        exact hentry.mpr hcurrent
      · intro hentryTrue
        apply hmem.mpr
        refine ⟨⟨t.val - s, by have ht := t.isLt; omega⟩, ?_, ?_⟩
        · have hcurrent := hentry.mp hentryTrue
          have hgateTime := congrArg
            (fun time => ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s time
              (ReferenceActivePhysicalStepMeasurability.encodeState
                (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
                  (t.val - s) (by have ht := t.isLt; omega) hactive).input.state)) hrecordTime
          have hgateAt : gateAt ⟨t.val - s, by have ht := t.isLt; omega⟩ = true := by
            change ReferenceRetainedReleasePhaseObservation.localReleaseGate rate s
                (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
                  (t.val - s) (by have ht := t.isLt; omega) hactive).input.time
                (ReferenceActivePhysicalStepMeasurability.encodeState
                  (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
                    (t.val - s) (by have ht := t.isLt; omega) hactive).input.state) = true
            exact hgateTime.trans hcurrent
          exact hgateAt
        · change s + (t.val - s) + 1 = t.val + 1
          omega
    · have hnoneRecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
        rate rewards C_star C_h t z (by simpa [s, physicalStart] using (Nat.lt_of_not_ge hbefore))
      constructor
      · intro hgate
        have hrunGate : t.val + 1 ∈
            ReferenceLocalReleaseGateChronology.gateSupport s
            (ReferenceActivePhysicalHorizon.run active z.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
              (p.T - s) hspan hactive).records := by
          simpa [ReferenceLocalReleaseGateChronology.sourceRun] using hsupportEq ▸ hgate
        have hindices := (ReferenceLocalReleaseGateChronology.mem_run_gateSupport
          active z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
          hactive (p.T - s) hspan s (t.val + 1)).mp hrunGate
        obtain ⟨j, _, hjtime⟩ := hindices
        have : s ≤ t.val := by omega
        exact (hbefore this).elim
      · intro hentry
        simp [ReferenceSourcePrefixHistoryFiltration.entry,
          ReferenceSourcePrefixHistoryFiltration.incoming, hnoneRecord] at hentry
  · have hnone : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate z rewards C_star C_h).crossing = none := by
      cases h : (ReferenceCompletePhysicalHistory.generatedBoundary
          rate z rewards C_star C_h).crossing with
      | none => rfl
      | some x => simp [h] at hcross
    have hlaunch := (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
      rate z rewards C_star C_h).2 hnone
    have hhistory := ReferenceCompletePhysicalHistory.no_launch_complete_history
      rate z rewards C_star C_h hlaunch
    have hsupport : actualGateSupport rate rewards C_star C_h z = ∅ := by
      unfold actualGateSupport
      rw [show completeRecords rate rewards C_star C_h z = [] from hhistory.2.1]
      simp [ReferenceLocalReleaseGateChronology.gateSupport]
    have hrecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_no_crossing
      rate rewards C_star C_h t z hnone
    rw [hsupport]
    simp [ReferenceSourcePrefixHistoryFiltration.entry,
      ReferenceSourcePrefixHistoryFiltration.incoming, hrecord]

/-- The actual raw gate at the current calendar date is adapted to the
original source filtration after that round. Variable launch dates are
partitioned by the genuine launch strata. -/
theorem actual_gate_support_adapted
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      {z : Source p | t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z} := by
  classical
  let stratumEvent (s : Fin (t.val + 1)) : Set (Source p) :=
    {z | z ∈ ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s.val ∧
      (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s.val t z).map
        Prod.fst = some true}
  have hdescription :
      {z : Source p | t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z} =
        ⋃ s : Fin (t.val + 1), stratumEvent s := by
    ext z
    constructor
    · intro hgate
      have hentry := (actual_gate_support_mem_iff_entry rate rewards C_star C_h z t).mp hgate
      have hrecord : ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z = some r := by
        cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
        | none => simp [ReferenceSourcePrefixHistoryFiltration.entry,
            ReferenceSourcePrefixHistoryFiltration.incoming, hr] at hentry
        | some r => exact ⟨r, rfl⟩
      have hs : physicalStart rate rewards C_star C_h z ≤ t.val := by
        by_contra hnot
        obtain ⟨r, hr⟩ := hrecord
        have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
          rate rewards C_star C_h t z (Nat.lt_of_not_ge hnot)
        rw [hnone] at hr
        cases hr
      have hcross : (ReferenceCompletePhysicalHistory.generatedBoundary
          rate z rewards C_star C_h).crossing.isSome = true := by
        by_contra hnot
        have hno : (ReferenceCompletePhysicalHistory.generatedBoundary
            rate z rewards C_star C_h).crossing = none := by
          cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary
              rate z rewards C_star C_h).crossing with
          | none => rfl
          | some c => simp [hc] at hnot
        obtain ⟨r, hr⟩ := hrecord
        rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_no_crossing
          rate rewards C_star C_h t z hno] at hr
        cases hr
      let s : Fin (t.val + 1) := ⟨physicalStart rate rewards C_star C_h z,
        Nat.lt_succ_of_le hs⟩
      have hsource : z ∈ ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h s.val := by
        exact ⟨hcross, rfl⟩
      have hentry' :
          (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s.val t z).map
            Prod.fst = some true := by
        simpa [s] using hentry
      exact Set.mem_iUnion.mpr ⟨s, hsource, hentry'⟩
    · intro hunion
      obtain ⟨s, hsource, hentry⟩ := Set.mem_iUnion.mp hunion
      have hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s.val :=
        hsource.2
      have hentry' :
          (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
            (physicalStart rate rewards C_star C_h z) t z).map Prod.fst = some true := by
        simpa [physicalStart, hs] using hentry
      exact (actual_gate_support_mem_iff_entry rate rewards C_star C_h z t).mpr hentry'
  rw [hdescription]
  apply MeasurableSet.iUnion
  intro s
  have hstratum := ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_measurable
    rate rewards C_star C_h control0 t s.val (Nat.le_of_lt_succ s.isLt)
  have hentry := ReferenceSourcePrefixHistoryFiltration.entry_measurable
    rate rewards C_star C_h control0 s.val t
  have hreadout : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)]
      {z : Source p |
        (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s.val t z).map
          Prod.fst = some true} := by
    let : MeasurableSpace (Option (Finset (Fin (p.m - 1)))) :=
      LaterAssignmentStartMeasurability.optionMeasurableSpace
    have hset : MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace]
        {e : Option (Bool × Option (Finset (Fin (p.m - 1)))) |
          e.map Prod.fst = some true} := by
      have hsetEq :
          {e : Option (Bool × Option (Finset (Fin (p.m - 1)))) |
            e.map Prod.fst = some true} =
          ⋃ pending : Option (Finset (Fin (p.m - 1))),
            ({some (true, pending)} : Set
              (Option (Bool × Option (Finset (Fin (p.m - 1)))))) := by
        ext e
        cases e with
        | none => simp
        | some pair =>
            rcases pair with ⟨flag, pending⟩
            cases flag <;> simp
      rw [hsetEq]
      exact MeasurableSet.iUnion fun pending =>
        measurableSet_option_singleton (some (true, pending))
    exact hset.preimage hentry
  have hresult : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)]
      (ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s.val ∩
        {z : Source p |
          (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s.val t z).map
            Prod.fst = some true}) := hstratum.inter hreadout
  have hset : (stratumEvent s : Set (Source p)) =
      ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s.val ∩
        {z : Source p |
          (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s.val t z).map
            Prod.fst = some true} := by
    ext z
    rfl
  rw [hset]
  exact hresult

/-- The literal decoder-stop disjunction is adapted after the current
physical date. A launch-dependent strict-past flag is assembled only on its
actual elapsed-time stratum; the prelaunch flag is retained on every stratum. -/
theorem actual_decoder_flag_true_adapted
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      {z : Source p | actualDecoderFlag rate rewards C_star C_h z t.val
        (Nat.le_of_lt t.isLt) = true} := by
  classical
  let H := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
    control0 (t.val + 1)
  let K := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h
    t.val (Nat.le_of_lt t.isLt)
  have hle : K ≤ H :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_sourcePrefixFiltration
      rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt)
  have hprelaunch : Measurable[K]
      (fun z : Source p => ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z t.val (Nat.le_of_lt t.isLt)) :=
    ReferencePrelaunchInspectedDecoderPast.prelaunchPastDecoderFlag_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt)
  have hprelaunchH : Measurable[H]
      (fun z : Source p => ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z t.val (Nat.le_of_lt t.isLt)) :=
    hprelaunch.mono hle le_rfl
  have hprelaunchSet : MeasurableSet[H]
      {z : Source p | ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
        rate rewards C_star C_h z t.val (Nat.le_of_lt t.isLt) = true} :=
    measurableSet_preimage hprelaunchH (measurableSet_singleton true)
  have hdecomposition :
      {z : Source p | actualDecoderFlag rate rewards C_star C_h z t.val
          (Nat.le_of_lt t.isLt) = true} =
        {z : Source p | ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
          rate rewards C_star C_h z t.val (Nat.le_of_lt t.isLt) = true} ∪
        ⋃ s : Fin (t.val + 1),
          ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
            (rate := rate) rewards C_star C_h s.val ∩
          {z : Source p | ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag
            rate rewards C_star C_h s.val t.val (Nat.le_of_lt t.isLt) z = true} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hflag
      have hor :
          ReferencePrelaunchDownDecisionReadout.prelaunchPastDecoderFlag
              rate rewards C_star C_h z t.val (Nat.le_of_lt t.isLt) = true ∨
            ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag
              rate rewards C_star C_h (physicalStart rate rewards C_star C_h z)
              t.val (Nat.le_of_lt t.isLt) z = true := by
        simpa only [actualDecoderFlag, Bool.or_eq_true] using hflag
      rcases hor with hpre | hstrict
      · exact Or.inl hpre
      · have hstrict' :=
          (ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag_eq_true_iff
            rate rewards C_star C_h (physicalStart rate rewards C_star C_h z) t.val
            (Nat.le_of_lt t.isLt) z).mp hstrict
        obtain ⟨j, r, hrecord, _hrecordFlag⟩ := hstrict'
        have hstartj : physicalStart rate rewards C_star C_h z ≤
            (Fin.castLE (Nat.le_of_lt t.isLt) j).val := by
          by_contra hnot
          have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
            rate rewards C_star C_h (Fin.castLE (Nat.le_of_lt t.isLt) j) z
            (Nat.lt_of_not_ge hnot)
          rw [hnone] at hrecord
          cases hrecord
        have hstart : physicalStart rate rewards C_star C_h z ≤ t.val := by
          exact hstartj.trans (Nat.le_of_lt j.isLt)
        have hcross :
            (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true := by
          by_contra hnot
          have hno : (ReferenceCompletePhysicalHistory.generatedBoundary
              rate z rewards C_star C_h).crossing = none := by
            cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary
                rate z rewards C_star C_h).crossing with
            | none => rfl
            | some c => simp [hc] at hnot
          have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_no_crossing
            rate rewards C_star C_h (Fin.castLE (Nat.le_of_lt t.isLt) j) z hno
          rw [hnone] at hrecord
          cases hrecord
        let s : Fin (t.val + 1) := ⟨physicalStart rate rewards C_star C_h z,
          Nat.lt_succ_of_le hstart⟩
        have hsource : z ∈
            ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
              (rate := rate) rewards C_star C_h s.val := ⟨hcross, rfl⟩
        have hstrictAtS :
            ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag
              rate rewards C_star C_h s.val t.val (Nat.le_of_lt t.isLt) z = true := by
          simpa [s] using hstrict
        exact Or.inr ⟨s, hsource, hstrictAtS⟩
    · intro h
      rcases h with hpre | ⟨s, hsource, hstrict⟩
      · simp [actualDecoderFlag, hpre]
      · have hs : physicalStart rate rewards C_star C_h z = s.val := hsource.2
        have hstrict' :
            ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag
              rate rewards C_star C_h (physicalStart rate rewards C_star C_h z)
              t.val (Nat.le_of_lt t.isLt) z = true := by
          simpa [hs] using hstrict
        simp [actualDecoderFlag, hstrict']
  rw [hdecomposition]
  apply MeasurableSet.union
  · exact hprelaunchSet
  · apply MeasurableSet.iUnion
    intro s
    have hstratum := ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_measurable
      rate rewards C_star C_h control0 t s.val (Nat.le_of_lt_succ s.isLt)
    have hstrictK : Measurable[K]
        (ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag
          rate rewards C_star C_h s.val t.val (Nat.le_of_lt t.isLt)) :=
      ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag_measurable_in_inspectedHistorySpace
        rate rewards C_star C_h s.val t.val (Nat.le_of_lt t.isLt)
    have hstrictH : Measurable[H]
        (ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag
          rate rewards C_star C_h s.val t.val (Nat.le_of_lt t.isLt)) :=
      hstrictK.mono hle le_rfl
    have hstrictSet : MeasurableSet[H]
        {z : Source p | ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag
          rate rewards C_star C_h s.val t.val (Nat.le_of_lt t.isLt) z = true} :=
      measurableSet_preimage hstrictH (measurableSet_singleton true)
    exact hstratum.inter hstrictSet

/-- Before calendar date `t+1`, the finite decoder cutoff is exactly the
absence of both actual detector flags through physical date `t`. -/
theorem decoder_cutoff_after_current_iff
    (t : Fin p.T) (z : Source p) :
    t.val + 1 < decoderFirstExcluded rate rewards C_star C_h z ↔
      ∀ n : Fin (t.val + 1),
        actualDecoderFlag rate rewards C_star C_h z n.val
          (by have hn := n.isLt; omega) = false := by
  classical
  let bad : Finset ℕ :=
    (((Finset.univ : Finset (Fin p.T)).filter fun n =>
      actualDecoderFlag rate rewards C_star C_h z n.val (Nat.le_of_lt n.isLt) = true).image
        fun n => n.val + 1) ∪ {p.T + 1}
  have hsentinel : p.T + 1 ∈ bad :=
    Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hnonempty : bad.Nonempty := ⟨p.T + 1, hsentinel⟩
  change t.val + 1 < bad.min' hnonempty ↔ _
  constructor
  · intro hmin n
    by_contra hfalse
    have htrue : actualDecoderFlag rate rewards C_star C_h z n.val
        (by have hn := n.isLt; omega) = true := by
      cases hflag : actualDecoderFlag rate rewards C_star C_h z n.val
          (by have hn := n.isLt; omega) with
      | false => exact (hfalse hflag).elim
      | true => rfl
    let j : Fin p.T := ⟨n.val, by have hn := n.isLt; omega⟩
    have hmem : n.val + 1 ∈ bad := by
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simpa [j] using htrue
      · rfl
    have hle := Finset.min'_le bad (n.val + 1) hmem
    omega
  · intro hfalse
    by_contra hnot
    have hle : bad.min' hnonempty ≤ t.val + 1 := Nat.le_of_not_gt hnot
    have hmemMin := Finset.min'_mem bad hnonempty
    rcases Finset.mem_union.mp hmemMin with himage | hsentinel'
    · obtain ⟨j, hj, hround⟩ := Finset.mem_image.mp himage
      have hjle : j.val + 1 ≤ t.val + 1 := by rw [hround]; exact hle
      have hjflag : actualDecoderFlag rate rewards C_star C_h z j.val
          (Nat.le_of_lt j.isLt) = true := (Finset.mem_filter.mp hj).2
      have hjle' : j.val ≤ t.val := by omega
      have hnotFlag : actualDecoderFlag rate rewards C_star C_h z j.val
          (Nat.le_of_lt j.isLt) = false := by
        simpa only [Fin.val_mk] using
          (hfalse ⟨j.val, Nat.lt_succ_of_le hjle'⟩)
      rw [hjflag] at hnotFlag
      cases hnotFlag
    · simp only [Finset.mem_singleton] at hsentinel'
      omega

private abbrev FirstLiveSourceZ (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) :=
  ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
    (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)

private def strictPastOverflowFalseOnStratum
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (z : FirstLiveSourceZ rate rewards C_star C_h q t s hs) : Prop :=
  (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h
      (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
        rate rewards C_star C_h q t s hs z).2.1
      (t.val - s + 1)
      (by
        have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
          rate rewards C_star C_h q t s hs z
        rw [hz.2.2]
        omega)).take (t.val - s))).overflow = false

private theorem source_stratum_prefix_factor
    (control0 : ContinuousLearningRows.TimeControl p) (q : Fin (M p))
    (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val) (z : Source p) :
    z ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
        (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) ↔
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z ∈
        ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
          (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) := by
  have hlaunch := ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_factor
    rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) s hs z
  have hindex : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z =
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected control0 t.val z).symm
  change (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = q ∧
      z ∈ ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s) ↔
    (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) = q ∧
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z ∈
        ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h s)
  rw [hindex]
  exact and_congr_right' hlaunch

/-- The actual selected-row, launch, and elapsed source stratum is known by
the original date-`t` source prefix. -/
theorem first_live_source_stratum_adapted
    (control0 : ContinuousLearningRows.TimeControl p) (q : Fin (M p))
    (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      (ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
        (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)) := by
  have hBorel := ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
    rate rewards C_star C_h t control0
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
  have hset :
      {z : Source p | z ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent
        rate rewards C_star C_h t
          (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)} =
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val) ⁻¹'
        ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
          (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) := by
    ext z
    exact source_stratum_prefix_factor rate rewards C_star C_h control0 q t s hs z
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  exact (MeasurableSpace.measurableSet_comap).2 ⟨
    ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs),
    hBorel, hset.symm⟩

private def actualGateCode (z : Source p) : Fin p.T → Bool :=
  fun t => if t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z then true else false

private def gateSupportFromCode (code : Fin p.T → Bool) : Finset ℕ :=
  (Finset.univ.filter fun t => code t = true).image fun t => t.val + 1

private def gateAlphaFromCode (code : Fin p.T → Bool) : ℕ :=
  let support := gateSupportFromCode code
  if h : support.Nonempty then support.min' h else p.T + 1

private def gateBetaFromCode (code : Fin p.T → Bool) : ℕ :=
  let support := gateSupportFromCode code
  if h : support.Nonempty then support.max' h + 1 else p.T + 1

private theorem actual_gate_support_eq_code (z : Source p) :
    actualGateSupport rate rewards C_star C_h z =
      gateSupportFromCode (p := p) (actualGateCode rate rewards C_star C_h z) := by
  classical
  ext v
  constructor
  · intro hv
    have hv' : v ∈ ReferenceLocalReleaseGateChronology.gateSupport
        (physicalStart rate rewards C_star C_h z)
        (completeRecords rate rewards C_star C_h z) := by
      simpa [actualGateSupport] using hv
    obtain ⟨hlo, hhi⟩ := ReferenceLocalReleaseGateChronology.gateSupport_bounds
      (physicalStart rate rewards C_star C_h z) v
      (completeRecords rate rewards C_star C_h z) hv'
    let t : Fin p.T := ⟨v - 1, by omega⟩
    have hdate : t.val + 1 = v := by dsimp [t]; omega
    apply Finset.mem_image.mpr
    refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hdate⟩
    simp [actualGateCode, hdate, hv]
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨t, ht, rfl⟩
    have hgate : t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z := by
      have hflag : actualGateCode rate rewards C_star C_h z t = true :=
        (Finset.mem_filter.mp ht).2
      simpa [actualGateCode] using hflag
    exact hgate

private theorem actual_gate_alpha_eq_code (z : Source p) :
    actualGateAlpha rate rewards C_star C_h z =
      gateAlphaFromCode (p := p) (actualGateCode rate rewards C_star C_h z) := by
  have hs := actual_gate_support_eq_code rate rewards C_star C_h z
  unfold actualGateAlpha
  change (if h : (actualGateSupport rate rewards C_star C_h z).Nonempty then
      (actualGateSupport rate rewards C_star C_h z).min' h else p.T + 1) = _
  rw [hs]
  unfold gateAlphaFromCode
  dsimp only

private theorem actual_gate_beta_eq_code (z : Source p) :
    actualGateBeta rate rewards C_star C_h z =
      gateBetaFromCode (p := p) (actualGateCode rate rewards C_star C_h z) := by
  have hs := actual_gate_support_eq_code rate rewards C_star C_h z
  unfold actualGateBeta
  change (if h : (actualGateSupport rate rewards C_star C_h z).Nonempty then
      (actualGateSupport rate rewards C_star C_h z).max' h + 1 else p.T + 1) = _
  rw [hs]
  unfold gateBetaFromCode
  dsimp only

private theorem measurable_actual_gate_code
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (actualGateCode rate rewards C_star C_h) := by
  apply measurable_pi_iff.mpr
  intro t
  have hset : MeasurableSet
      {z : Source p | t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z} :=
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1))
      {z : Source p | t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z}
      (actual_gate_support_adapted rate rewards C_star C_h control0 t)
  change Measurable (fun z : Source p =>
    if t.val + 1 ∈ actualGateSupport rate rewards C_star C_h z then true else false)
  exact Measurable.ite hset measurable_const measurable_const

private theorem measurable_actual_gate_alpha
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (actualGateAlpha rate rewards C_star C_h) := by
  have hcode := measurable_actual_gate_code rate rewards C_star C_h control0
  have hfun : Measurable (gateAlphaFromCode (p := p)) := measurable_of_countable _
  have heq : actualGateAlpha rate rewards C_star C_h =
      gateAlphaFromCode (p := p) ∘ actualGateCode rate rewards C_star C_h := by
    funext z
    exact actual_gate_alpha_eq_code rate rewards C_star C_h z
  rw [heq]
  exact hfun.comp hcode

private theorem measurable_actual_gate_beta
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (actualGateBeta rate rewards C_star C_h) := by
  have hcode := measurable_actual_gate_code rate rewards C_star C_h control0
  have hfun : Measurable (gateBetaFromCode (p := p)) := measurable_of_countable _
  have heq : actualGateBeta rate rewards C_star C_h =
      gateBetaFromCode (p := p) ∘ actualGateCode rate rewards C_star C_h := by
    funext z
    exact actual_gate_beta_eq_code rate rewards C_star C_h z
  rw [heq]
  exact hfun.comp hcode

private def decoderCode (z : Source p) : Fin p.T → Bool :=
  fun n => actualDecoderFlag rate rewards C_star C_h z n.val (Nat.le_of_lt n.isLt)

private def decoderExcludedFromCode (code : Fin p.T → Bool) : ℕ :=
  let bad := ((Finset.univ.filter fun n => code n = true).image fun n => n.val + 1) ∪
    {p.T + 1}
  bad.min' ⟨p.T + 1, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩

private theorem measurable_decoder_code
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (decoderCode rate rewards C_star C_h) := by
  apply measurable_pi_iff.mpr
  intro t
  have htrue : MeasurableSet
      {z : Source p | actualDecoderFlag rate rewards C_star C_h z t.val
        (Nat.le_of_lt t.isLt) = true} :=
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1))
      {z : Source p | actualDecoderFlag rate rewards C_star C_h z t.val
        (Nat.le_of_lt t.isLt) = true}
      (actual_decoder_flag_true_adapted rate rewards C_star C_h control0 t)
  have hite : Measurable (fun z : Source p =>
      if actualDecoderFlag rate rewards C_star C_h z t.val
          (Nat.le_of_lt t.isLt) = true then true else false) :=
    Measurable.ite htrue measurable_const measurable_const
  have heq : (fun z : Source p => actualDecoderFlag rate rewards C_star C_h z t.val
      (Nat.le_of_lt t.isLt)) = fun z =>
        if actualDecoderFlag rate rewards C_star C_h z t.val
            (Nat.le_of_lt t.isLt) = true then true else false := by
    funext z
    cases actualDecoderFlag rate rewards C_star C_h z t.val (Nat.le_of_lt t.isLt) <;> rfl
  change Measurable (fun z : Source p => actualDecoderFlag rate rewards C_star C_h z t.val
    (Nat.le_of_lt t.isLt))
  rw [heq]
  exact hite

private theorem decoder_first_excluded_eq_code (z : Source p) :
    decoderFirstExcluded rate rewards C_star C_h z =
      decoderExcludedFromCode (p := p) (decoderCode rate rewards C_star C_h z) := by
  rfl

private theorem measurable_decoder_first_excluded
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (decoderFirstExcluded rate rewards C_star C_h) := by
  have hcode := measurable_decoder_code rate rewards C_star C_h control0
  have hfun : Measurable (decoderExcludedFromCode (p := p)) := measurable_of_countable _
  have heq : decoderFirstExcluded rate rewards C_star C_h =
      decoderExcludedFromCode (p := p) ∘ decoderCode rate rewards C_star C_h := by
    funext z
    exact decoder_first_excluded_eq_code rate rewards C_star C_h z
  rw [heq]
  exact hfun.comp hcode

/-- The two actual calendar endpoints are Borel on the original full source.
This is an ambient measurability statement only; it adds no filtration or
stopping-time claim. -/
theorem first_release_endpoints_measurable
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (firstReleaseSigma rate rewards C_star C_h) ∧
      Measurable (firstReleaseTheta rate rewards C_star C_h) := by
  have hAlpha := measurable_actual_gate_alpha rate rewards C_star C_h control0
  have hBeta := measurable_actual_gate_beta rate rewards C_star C_h control0
  have hDecoder := measurable_decoder_first_excluded rate rewards C_star C_h control0
  have hOverflow : Measurable (overflowFirstExcluded rate rewards C_star C_h) := by
    have hround := ReferenceFirstLiveOverflowMeasurability.measurable_wholeFirstLiveOverflowRound
      rate rewards C_star C_h
    have hfun : Measurable (fun r : Option ℕ => r.elim (p.T + 1)
        (fun v => min (p.T + 1) (v + 1))) := measurable_of_countable _
    exact hfun.comp hround
  have hcut : Measurable (firstExcluded rate rewards C_star C_h) := by
    have hmin : Measurable (fun z : Source p =>
        min (decoderFirstExcluded rate rewards C_star C_h z)
          (overflowFirstExcluded rate rewards C_star C_h z)) :=
      (measurable_of_countable (fun x : ℕ × ℕ => min x.1 x.2)).comp
        (hDecoder.prodMk hOverflow)
    change Measurable (fun z : Source p =>
      min (decoderFirstExcluded rate rewards C_star C_h z)
        (overflowFirstExcluded rate rewards C_star C_h z))
    exact hmin
  have hBeta' : Measurable (fun z : Source p =>
      min (actualGateBeta rate rewards C_star C_h z)
        (firstExcluded rate rewards C_star C_h z)) :=
    (measurable_of_countable (fun x : ℕ × ℕ => min x.1 x.2)).comp
      (hBeta.prodMk hcut)
  have hBefore : MeasurableSet {z : Source p |
      actualGateAlpha rate rewards C_star C_h z <
        min (actualGateBeta rate rewards C_star C_h z)
          (firstExcluded rate rewards C_star C_h z)} :=
    measurableSet_lt hAlpha hBeta'
  have hSigma : Measurable (firstReleaseSigma rate rewards C_star C_h) := by
    change Measurable (fun z : Source p =>
      if actualGateAlpha rate rewards C_star C_h z <
          min (actualGateBeta rate rewards C_star C_h z)
            (firstExcluded rate rewards C_star C_h z)
        then actualGateAlpha rate rewards C_star C_h z else p.T + 1)
    exact Measurable.ite hBefore hAlpha measurable_const
  have hTheta : Measurable (firstReleaseTheta rate rewards C_star C_h) := by
    change Measurable (fun z : Source p =>
      if actualGateAlpha rate rewards C_star C_h z <
          min (actualGateBeta rate rewards C_star C_h z)
            (firstExcluded rate rewards C_star C_h z)
        then min (actualGateBeta rate rewards C_star C_h z)
          (firstExcluded rate rewards C_star C_h z) else p.T + 1)
    exact Measurable.ite hBefore hBeta' measurable_const
  exact ⟨hSigma, hTheta⟩

/-- Decoder exclusion always lies in the one-based physical horizon. -/
theorem decoderFirstExcluded_bounds (z : Source p) :
    1 ≤ decoderFirstExcluded rate rewards C_star C_h z ∧
      decoderFirstExcluded rate rewards C_star C_h z ≤ p.T + 1 := by
  classical
  let bad : Finset ℕ :=
    (((Finset.univ : Finset (Fin p.T)).filter fun n =>
      actualDecoderFlag rate rewards C_star C_h z n.val (Nat.le_of_lt n.isLt) = true).image
        fun n => n.val + 1) ∪ {p.T + 1}
  have hmem : decoderFirstExcluded rate rewards C_star C_h z ∈ bad := by
    exact Finset.min'_mem bad ⟨p.T + 1,
      Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
  rcases Finset.mem_union.mp hmem with hbad | hsentinel
  · obtain ⟨n, _hn, hround⟩ := Finset.mem_image.mp hbad
    rw [← hround]
    omega
  · simp only [Finset.mem_singleton] at hsentinel
    rw [← hsentinel]
    omega

/-- The inclusive overflow round is an actual physical round; the excluded
date is therefore at most the horizon sentinel. -/
theorem overflowFirstExcluded_bounds (z : Source p) :
    1 ≤ overflowFirstExcluded rate rewards C_star C_h z ∧
      overflowFirstExcluded rate rewards C_star C_h z ≤ p.T + 1 := by
  classical
  cases hcrossing :
      (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing with
  | none =>
      have hno := ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
        rate rewards C_star C_h z hcrossing
      simp [overflowFirstExcluded, hno.2.2.2.2]
  | some crossing =>
      have hcross :
          (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true := by
        simp [hcrossing]
      let s : Fin (p.T + 1) :=
        ⟨physicalStart rate rewards C_star C_h z,
          Nat.lt_succ_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate z rewards C_star C_h)⟩
      let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val :=
        ⟨z, by
          change (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true ∧
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s.val
          exact ⟨hcross, rfl⟩⟩
      cases hover : ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
          rate rewards C_star C_h z with
      | none => simp [overflowFirstExcluded, hover]
      | some v =>
          have hreadouts := ReferenceFirstLiveOverflowReadout.wholeFirstLive_readouts_on_fiber
            rate rewards C_star C_h s x
          have hfirst :
              ReferenceFirstLiveOverflowReadout.firstLiveOverflowRound rate rewards C_star C_h
                s.val (p.T - s.val) (ReferenceFirstLiveOverflowReadout.maximal_span s) x = some v := by
            rw [← hreadouts.2.2.2.2.2]
            exact hover
          obtain ⟨k, hkpos, hklen, hv, _hc, _hprior⟩ :=
            (ReferenceFirstLiveOverflowReadout.firstLiveOverflowRound_spec
              rate rewards C_star C_h s.val (p.T - s.val)
              (ReferenceFirstLiveOverflowReadout.maximal_span s) x v).mp hfirst
          have hlen := ReferenceFirstLiveOverflowReadout.firstLiveLength_le_count
            rate rewards C_star C_h s.val (p.T - s.val)
            (ReferenceFirstLiveOverflowReadout.maximal_span s) x
          have hvle : v ≤ p.T := by omega
          simp [overflowFirstExcluded, hover]

/-- Both independent stop observations are one-based and horizon-bounded. -/
theorem firstExcluded_bounds (z : Source p) :
    1 ≤ firstExcluded rate rewards C_star C_h z ∧
      firstExcluded rate rewards C_star C_h z ≤ p.T + 1 := by
  have hd := decoderFirstExcluded_bounds rate rewards C_star C_h z
  have ho := overflowFirstExcluded_bounds rate rewards C_star C_h z
  simp only [firstExcluded]
  omega

private theorem actual_first_release_interval_of_launch (z : Source p)
    (hcross :
      (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true) :
    actualFirstReleaseSupport rate rewards C_star C_h z =
        Finset.Ico (firstReleaseSigma rate rewards C_star C_h z)
          (firstReleaseTheta rate rewards C_star C_h z) ∧
      1 ≤ firstReleaseSigma rate rewards C_star C_h z ∧
      firstReleaseSigma rate rewards C_star C_h z ≤ firstReleaseTheta rate rewards C_star C_h z ∧
      firstReleaseTheta rate rewards C_star C_h z ≤ p.T + 1 := by
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hspan : physicalStart rate rewards C_star C_h z +
      (p.T - physicalStart rate rewards C_star C_h z) ≤ p.T := by
    have hs' : physicalStart rate rewards C_star C_h z ≤ p.T := by
      simpa [physicalStart] using hs
    omega
  have hrestrict :=
    ReferenceLocalReleaseGateChronology.source_gate_interval_restrict
      rate z rewards C_star C_h hcross (physicalStart rate rewards C_star C_h z)
      (p.T - physicalStart rate rewards C_star C_h z) rfl hspan
      (physicalStart rate rewards C_star C_h z)
      (firstExcluded rate rewards C_star C_h z) (firstExcluded_bounds rate rewards C_star C_h z)
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some
        (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross) :=
    ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hcross
  have hrecords :
      (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross
        (physicalStart rate rewards C_star C_h z)
        (p.T - physicalStart rate rewards C_star C_h z) rfl hspan).records =
          completeRecords rate rewards C_star C_h z := by
    exact (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross) hlaunch
      ).symm
  let stoppedGateInterval := fun
      (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate)) =>
    (ReferenceLocalReleaseGateChronology.gateSupport
        (physicalStart rate rewards C_star C_h z) records).filter
        (fun v => v < firstExcluded rate rewards C_star C_h z) =
      Finset.Ico
        (if ReferenceLocalReleaseGateChronology.gateAlpha
            (physicalStart rate rewards C_star C_h z) records <
              min (ReferenceLocalReleaseGateChronology.gateBeta
                  (physicalStart rate rewards C_star C_h z) records)
                (firstExcluded rate rewards C_star C_h z)
          then ReferenceLocalReleaseGateChronology.gateAlpha
            (physicalStart rate rewards C_star C_h z) records else p.T + 1)
        (if ReferenceLocalReleaseGateChronology.gateAlpha
            (physicalStart rate rewards C_star C_h z) records <
              min (ReferenceLocalReleaseGateChronology.gateBeta
                  (physicalStart rate rewards C_star C_h z) records)
                (firstExcluded rate rewards C_star C_h z)
          then min (ReferenceLocalReleaseGateChronology.gateBeta
              (physicalStart rate rewards C_star C_h z) records)
            (firstExcluded rate rewards C_star C_h z) else p.T + 1) ∧
      1 ≤ (if ReferenceLocalReleaseGateChronology.gateAlpha
          (physicalStart rate rewards C_star C_h z) records <
            min (ReferenceLocalReleaseGateChronology.gateBeta
                (physicalStart rate rewards C_star C_h z) records)
              (firstExcluded rate rewards C_star C_h z)
        then ReferenceLocalReleaseGateChronology.gateAlpha
          (physicalStart rate rewards C_star C_h z) records else p.T + 1) ∧
      (if ReferenceLocalReleaseGateChronology.gateAlpha
          (physicalStart rate rewards C_star C_h z) records <
            min (ReferenceLocalReleaseGateChronology.gateBeta
                (physicalStart rate rewards C_star C_h z) records)
              (firstExcluded rate rewards C_star C_h z)
        then ReferenceLocalReleaseGateChronology.gateAlpha
          (physicalStart rate rewards C_star C_h z) records else p.T + 1) ≤
        (if ReferenceLocalReleaseGateChronology.gateAlpha
            (physicalStart rate rewards C_star C_h z) records <
              min (ReferenceLocalReleaseGateChronology.gateBeta
                  (physicalStart rate rewards C_star C_h z) records)
                (firstExcluded rate rewards C_star C_h z)
          then min (ReferenceLocalReleaseGateChronology.gateBeta
              (physicalStart rate rewards C_star C_h z) records)
            (firstExcluded rate rewards C_star C_h z) else p.T + 1) ∧
      (if ReferenceLocalReleaseGateChronology.gateAlpha
          (physicalStart rate rewards C_star C_h z) records <
            min (ReferenceLocalReleaseGateChronology.gateBeta
                (physicalStart rate rewards C_star C_h z) records)
              (firstExcluded rate rewards C_star C_h z)
        then min (ReferenceLocalReleaseGateChronology.gateBeta
            (physicalStart rate rewards C_star C_h z) records)
          (firstExcluded rate rewards C_star C_h z) else p.T + 1) ≤ p.T + 1
  have hsource : stoppedGateInterval
      (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hcross
        (physicalStart rate rewards C_star C_h z)
        (p.T - physicalStart rate rewards C_star C_h z) rfl hspan).records := by
    dsimp [stoppedGateInterval]
    exact hrestrict
  have htransport := congrArg stoppedGateInterval hrecords
  change stoppedGateInterval (completeRecords rate rewards C_star C_h z)
  exact htransport.mp hsource

/-- The exact actual source support is the clipped local gate interval.
No launch and terminal launch retain their original empty-calendar semantics. -/
theorem actual_first_release_interval (z : Source p) :
    actualFirstReleaseSupport rate rewards C_star C_h z =
        Finset.Ico (firstReleaseSigma rate rewards C_star C_h z)
          (firstReleaseTheta rate rewards C_star C_h z) ∧
      1 ≤ firstReleaseSigma rate rewards C_star C_h z ∧
      firstReleaseSigma rate rewards C_star C_h z ≤ firstReleaseTheta rate rewards C_star C_h z ∧
      firstReleaseTheta rate rewards C_star C_h z ≤ p.T + 1 := by
  classical
  by_cases hcross :
      (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true
  · exact actual_first_release_interval_of_launch rate rewards C_star C_h z hcross
  · have hnone : (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing = none := by
      cases h : (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing with
      | none => rfl
      | some crossing => simp [h] at hcross
    have hlaunch := (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
      rate z rewards C_star C_h).2 hnone
    have hhistory := ReferenceCompletePhysicalHistory.no_launch_complete_history
      rate z rewards C_star C_h hlaunch
    have hgate : actualGateSupport rate rewards C_star C_h z = ∅ := by
      unfold actualGateSupport
      rw [show completeRecords rate rewards C_star C_h z = [] from hhistory.2.1]
      simp [ReferenceLocalReleaseGateChronology.gateSupport]
    have hendpoints := ReferenceLocalReleaseGateChronology.gate_endpoints_empty
      (physicalStart rate rewards C_star C_h z) (completeRecords rate rewards C_star C_h z) hgate
    have hAlpha : actualGateAlpha rate rewards C_star C_h z = p.T + 1 := by
      simpa [actualGateAlpha, actualGateSupport] using hendpoints.1
    have hBeta : actualGateBeta rate rewards C_star C_h z = p.T + 1 := by
      simpa [actualGateBeta, actualGateSupport] using hendpoints.2
    have hsentinel :
        firstReleaseSigma rate rewards C_star C_h z = p.T + 1 ∧
          firstReleaseTheta rate rewards C_star C_h z = p.T + 1 := by
      simp [firstReleaseSigma, firstReleaseTheta, hAlpha, hBeta]
    rw [hsentinel.1, hsentinel.2]
    simp [actualFirstReleaseSupport, hgate]

/-- Empty stopped support has the exact source sentinel endpoint. -/
theorem empty_first_release_endpoints (z : Source p)
    (hempty : actualFirstReleaseSupport rate rewards C_star C_h z = ∅) :
    firstReleaseSigma rate rewards C_star C_h z = p.T + 1 ∧
      firstReleaseTheta rate rewards C_star C_h z = p.T + 1 := by
  rcases actual_first_release_interval rate rewards C_star C_h z with
    ⟨hinterval, hlow, horder, hhigh⟩
  let α := actualGateAlpha rate rewards C_star C_h z
  let β := min (actualGateBeta rate rewards C_star C_h z)
    (firstExcluded rate rewards C_star C_h z)
  by_cases hnonempty : α < β
  · have hmem : α ∈ Finset.Ico α β := Finset.mem_Ico.mpr ⟨le_rfl, hnonempty⟩
    have hemptyIco : Finset.Ico α β = ∅ := by
      calc
        Finset.Ico α β = Finset.Ico
            (firstReleaseSigma rate rewards C_star C_h z)
            (firstReleaseTheta rate rewards C_star C_h z) := by
              simp [firstReleaseSigma, firstReleaseTheta, α, β, hnonempty]
        _ = actualFirstReleaseSupport rate rewards C_star C_h z := hinterval.symm
        _ = ∅ := hempty
    rw [hemptyIco] at hmem
    simp at hmem
  · simp [firstReleaseSigma, firstReleaseTheta, α, β, hnonempty]

end Bandits.Support.ReferenceFirstLiveSourceStoppedReleaseEndpoint

end
