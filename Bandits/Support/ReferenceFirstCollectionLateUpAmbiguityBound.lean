/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionLateUpSourceAwaited
public import Bandits.Support.ReferenceGeneratedUpAwaitedAmbiguityTail

/-!
# Actual late first-collection second-batch ambiguity

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,240-296,327-348`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The literal event below records an actual late collection window, retained
DOWN seed, ordinary receiver/coordinator branch, and an ambiguous second UP
batch on the original source.  Its inclusion uses the actual-source awaited
coverage theorem and then the existing finite all-J survival envelope.  The
result is a local physical ambiguity consumer; it does not remove the displayed
seed or endpoint restrictions or claim service attainment or manuscript
closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical

namespace Bandits.Support.ReferenceFirstCollectionLateUpAmbiguityBound

open Bandits.Support.ConstructorDimensions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferenceAcceptedUpFollowerHistory
open Bandits.Support.ReferenceCoordinatorUpIntervalWindow
open Bandits.Support.ReferenceGeneratedUpBatchPrefixEvent
open Bandits.Support.ReferenceGeneratedUpPrefixPositiveHalf
open Bandits.Support.ReferenceGeneratedUpSourceCalendar
open Bandits.Support.ReferenceGeneratedUpSourceTail
open Bandits.Support.ReferenceFirstCollectionEpochAlignment
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceFirstCollectionLateUpSourceAwaited
open Bandits.Support.ReferenceGeneratedUpAwaitedAmbiguityTail

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The displayed actual late second-batch ambiguity branch.  Every run,
record, decoder bank, sample, selected coordinate, and reward is computed from
the same original source input. -/
def lateSecondBatchAmbiguityEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  {source | ∃ (count : ℕ)
      (hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
      (hspan : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
      (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length < count),
      let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source rewards C_star C_h hcross
      let s := ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
      let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1
      let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
      let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
      ∃ (k : Fin B.length) (i : Fin (p.m - 1))
        (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
        ReferenceAcceptedUpFollowerHistory.RetainedDown B[k.val] i M ∧
        let j := w + k.val
        let r := B[k.val]
        let b := j + 1
        let Wlate := (E.records.drop b).takeWhile
          (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
        r.output.next.followers i ≠ .dagger ∧
        r.output.next.coordinator ≠ .dagger ∧
        ∃ (n : ℕ), 0 < n ∧ n ≤ Wlate.length ∧
          ∃ (hbspan : s + b ≤ p.T) (hnspan : s + (b + n) ≤ p.T),
          let preRun := ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
            hbspan active
          let Cn := ReferenceActivePhysicalHorizon.run I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
            hnspan active
          let interval := Cn.records.drop b
          let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
          let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b (b + n)
            hnspan active
          let positive := AffineBatchDecoder.positives p trace rounds
          let channel := preRun.finalState.upDecoderBank i
          let Q := AffineBatchDecoder.quota p
          let window := positive.drop (Q - channel.pending.length)
          Cn.finalState.coordinator ≠ .dagger ∧
          positive.length = Q - channel.pending.length + Q ∧
          (∃ v₁ v₂ : AffineChannelLaw.Word (AffineBatchDecoder.width p),
            v₁ ≠ v₂ ∧
            AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v₁ ∧
            AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v₂) ∧
          ∃ (current : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
            Cn.records[b + n - 1]? = some current ∧
            ReferenceSelectedAffinePairLaw.selectedChannel p
              ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
                current.input.time).1 = some (1, i) ∧
            ReferenceActiveAffinePositiveTest.upPositive current.input = true}

private theorem activeRecord_eq_of_input_eq
    {left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hinput : left.input = right.input) : left = right := by
  cases left with
  | mk x output houtput =>
    cases right with
    | mk y output' houtput' =>
      dsimp only at hinput
      cases hinput
      cases houtput
      cases houtput'
      rfl

/-- Restore the corrected launch and every original source coordinate through
the public fixed-control split. -/
private theorem originalSourceRunInput_val_eq_actual
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (hsource : z.1 = source) :
    (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
      (rate := rate) rewards C_star C_h q t s hs control0 i z).val =
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source rewards C_star C_h hcross,
        source.1.2, ActualInitializationPhysicalStep.selectedRowIndex p source, rewards) := by
  let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hrestored := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput_eq
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  let control := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1
  let x := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
  have hsplitSource : ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1 = z.1 :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm_apply_apply z.1
  rw [hsource] at hsplitSource
  have hrows : input.val.2.1 = source.1.2 := by
    have h := congrArg
      (fun a : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s =>
        a.val.2.1) hrestored
    dsimp only [ReferenceGeneratedUpBatchPrefixEvent.retainedRunInput] at h
    rw [hsplitSource] at h
    exact h
  have hselected : input.val.2.2.1 = ActualInitializationPhysicalStep.selectedRowIndex p source := by
    have h := congrArg
      (fun a : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s =>
        a.val.2.2.1) hrestored
    dsimp only [ReferenceGeneratedUpBatchPrefixEvent.retainedRunInput] at h
    rw [hsplitSource] at h
    exact h
  have hreward : input.val.2.2.2 = rewards := by
    have h := congrArg
      (fun a : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s =>
        a.val.2.2.2) hrestored
    dsimp only [ReferenceGeneratedUpBatchPrefixEvent.retainedRunInput] at h
    exact h
  have hlaunch := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput_launch
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  rw [hsource] at hlaunch
  have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h).isSome = true :=
    (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).2 hcross
  have hstate : input.val.1 = ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross := by
    unfold ReferenceFirstCollectionEpochAlignment.actualLaunchState
    exact (Option.get_of_eq_some hsome hlaunch).symm
  apply Prod.ext
  · exact hstate
  · apply Prod.ext
    · exact hrows
    · apply Prod.ext
      · exact hselected
      · exact hreward

/-- The public original-source current record is the same physical record as
the actual run's indexed successor at that calendar time. -/
private theorem originalSourceCurrentRecord_eq_actualRunRecordAt
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (hsource : z.1 = source)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source rewards C_star C_h hcross) s) :
    ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
        (rate := rate) rewards C_star C_h q t s hs control0 i z =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
        (t.val - s) (by omega) active := by
  let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  have hinput := originalSourceRunInput_val_eq_actual
    source rewards C_star C_h hcross q t s hs control0 i z hsource
  have hwhole : input = (⟨(initial, source.1.2,
      ActualInitializationPhysicalStep.selectedRowIndex p source, rewards), active⟩ :
        ReferenceActiveHorizonMeasurability.ActiveRunInput
          (p := p) (rate := rate) s) := Subtype.ext hinput
  have hentry : (⟨s + (t.val - s), by omega, by omega⟩ :
      ReferenceActivePhysicalHorizon.CalendarEntry p s) = ⟨t.val, hs, t.isLt⟩ := by
    apply Subtype.ext
    exact Nat.add_sub_of_le hs
  unfold ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
  apply activeRecord_eq_of_input_eq
  change ReferenceActivePhysicalHorizon.roundInputAt input.val.1 input.val.2.1
      input.val.2.2.1 input.val.2.2.2 s input.property
      (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input)
      ⟨t.val, ⟨by omega, by omega⟩⟩ =
    ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s active
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
        (t.val - s) (by omega) active)
      ⟨s + (t.val - s), by omega, by omega⟩
  rw [hwhole, ReferenceActiveHorizonMeasurability.runOfInput, hentry]

private theorem run_last_record_at
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hcount : 0 < count) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records[count - 1]? =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected
        rewards start (count - 1) (by omega) active) := by
  have hsucc := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
    initial rows selected rewards start (count - 1) (by omega) active
  have hlen := ReferenceActivePhysicalHorizon.run_record_count
    initial rows selected rewards start (count - 1) (by omega) active
  have hsucc' :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (count - 1)
          (by omega) active).records ++
          [ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected rewards
            start (count - 1) (by omega) active] := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ count)] using hsucc
  rw [hsucc', List.getElem?_append_right (by rw [hlen]), hlen]
  simp only [Nat.sub_self, List.getElem?_cons_zero]

/-- The literal late physical ambiguity event is contained in the admitted
all-J awaited-UP ambiguity envelope.  A's fixed first-collection cutoff and
retained query are applied at this same source, count, and `B[k]`. -/
theorem lateSecondBatchAmbiguityEvent_subset_envelope
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    lateSecondBatchAmbiguityEvent (rate := rate) rewards C_star C_h ⊆
      ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope
        (rate := rate) rewards C_star C_h control0 := by
  intro source hsource
  simp only [lateSecondBatchAmbiguityEvent, Set.mem_ofPred_eq] at hsource
  rcases hsource with ⟨count, hcross, hspan, hshort, k, i, retainedMessage, hretained,
    hseed, hcoord, n, hnpos, hn, hbspan, hnspan, hOrd, hlength, hamb,
    current, hcurrentGet, hselected, hpositive⟩
  let x0 := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b0 := ReferenceInitializationRun.output x0
  let s := ReferenceInitializationRun.elapsed p b0.completed
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let j := w + k.val
  let r := B[k.val]
  let b := j + 1
  let Wlate := (E.records.drop b).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hcoverage :=
    ReferenceFirstCollectionLateUpSourceAwaited.actual_late_second_batch_ambiguous_source_coverage
      rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨cutoffRecord, suffix, registers, owned, base, P0, birth,
      hsplit, hindex, htime, hstate, hcutoff, hP0, hP0sigma, hqueues,
      hfirstCutoff, hbirth, hbirthInstall, hbirthTime, hwindow, hqueries⟩ := hcoverage
  have hnotFollowerDagger : ¬ r.output.next.followers i = .dagger := hseed
  have hnotCoordinatorDagger : ¬ r.output.next.coordinator = .dagger := hcoord
  have hordinary := (hqueries k i retainedMessage hretained).resolve_left hnotFollowerDagger
    |>.resolve_left hnotCoordinatorDagger
  obtain ⟨out, memory, ledger, saved, hfollower, hcoordinator, hstatus,
      hreply, hM, hMsigma, hlastDown, hstart, hledgerSigma, hpending,
      hb, hbspanA, hlate, hprefix, hWlate, hlookup, U, hUfields,
      hUnumeric, hUpositive, hquery⟩ := hordinary
  have htimeBound : s + b + n - 1 < p.T := by
    have hcountSpan : s + count ≤ p.T := hspan
    have hrest : b + n ≤ count := by
      have hncount : n ≤ count - b := le_trans hn hlate
      omega
    omega
  let tFin : Fin p.T := ⟨s + b + n - 1, htimeBound⟩
  have hcurrentActual : current =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
        (b + n - 1) (by omega) active := by
    have hactual := run_last_record_at initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
      hnspan active (by omega)
    exact Option.some.inj (hcurrentGet.symm.trans hactual)
  have hcurrentTime : current.input.time = tFin := by
    rw [hcurrentActual]
    apply Fin.ext
    simp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt, tFin]
    omega
  have hselect : ReferenceSelectedAffinePairLaw.selectedChannel p
      ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 tFin).1 =
        some (1, i) := by
    rw [← hcurrentTime]
    exact hselected
  obtain ⟨hs, hz, hspan_n, hqueryResult⟩ :=
    hquery n hn hnpos control0 hselect
  have hcurrentOriginal : current =
      ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
        (rate := rate) rewards C_star C_h
        (ActualInitializationPhysicalStep.selectedRowIndex p source) tFin s hs
        control0 i ⟨source, hz⟩ := by
    have hcurrActual := hcurrentActual
    have activeAtStart : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
      simpa only [s, initial] using
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
    have hsourceActual := originalSourceCurrentRecord_eq_actualRunRecordAt
      source rewards C_star C_h hcross (ActualInitializationPhysicalStep.selectedRowIndex p source)
      tFin s hs control0 i ⟨source, hz⟩ rfl activeAtStart
    have hidx : tFin.val - s = b + n - 1 := by simp [tFin]; omega
    have hcurrActual' : current =
        ReferenceAssignmentPayloadChronology.actualRunRecordAt
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState
            rate source rewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
          (b + n - 1) (by omega) activeAtStart := by
      simpa only [initial, active] using hcurrActual
    have hsourceActual' :
        ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
            (rate := rate) rewards C_star C_h
            (ActualInitializationPhysicalStep.selectedRowIndex p source) tFin s hs
            control0 i ⟨source, hz⟩ =
          ReferenceAssignmentPayloadChronology.actualRunRecordAt
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState
              rate source rewards C_star C_h hcross)
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
            (b + n - 1) (by omega) activeAtStart := by
      simpa only [hidx] using hsourceActual
    exact hcurrActual'.trans hsourceActual'.symm
  have hpositive' : ReferenceActiveAffinePositiveTest.upPositive
      (ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
        (rate := rate) rewards C_star C_h
        (ActualInitializationPhysicalStep.selectedRowIndex p source) tFin s hs
        control0 i ⟨source, hz⟩).input = true := by
    rw [← hcurrentOriginal]
    exact hpositive
  have hqueryReady := hqueryResult hOrd hpositive' hlength hamb
  obtain ⟨diagnostic, hdiag, hdiagFollower, hquota, hwindow,
      hawaited, hpendingClear, hcompleted, hrawNone, alpha, hAlphaLower,
      hAlphaUpper, hbirthAlpha, hkeptLen, hkeptOrder, hcoordinates,
      hsent, candidate, hcandidateSolves, hcandidateNe, hsurvival⟩ := hqueryReady
  have hAlphaLt : alpha < p.T := lt_of_le_of_lt hAlphaUpper tFin.isLt
  let alphaFin : Fin p.T := ⟨alpha, hAlphaLt⟩
  simp only [ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope,
    Set.mem_iUnion]
  refine ⟨i, alphaFin, candidate, ?_⟩
  change source ∈ ⋃ q' : Fin (ConstructorDimensions.M p),
    ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
      rewards C_star C_h q' control0 alpha candidate i (AffineBatchDecoder.quota p)
  exact Set.mem_iUnion.mpr ⟨ActualInitializationPhysicalStep.selectedRowIndex p source,
    hsurvival⟩

/-- The event has the admitted finite-union bound.  Its measure is the source
law's outer measure when the literal event is not known to be measurable. -/
theorem lateSecondBatchAmbiguityEvent_measure_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (lateSecondBatchAmbiguityEvent (rate := rate) rewards C_star C_h) ≤
      ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
        ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p := by
  calc
    _ ≤ BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope
          (rate := rate) rewards C_star C_h control0) :=
      measure_mono (lateSecondBatchAmbiguityEvent_subset_envelope
        (rate := rate) rewards C_star C_h control0)
    _ ≤ _ := ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope_measure_le
      (rate := rate) rewards C_star C_h control0

private theorem ambiguityUnionFactor_ne_top (p : ConstructorDimensions.Parameters) :
    ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
      (2 ^ AffineBatchDecoder.quota p : ℝ≥0∞)⁻¹ ≠ ∞ := by
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))
      (ENNReal.pow_ne_top (by norm_num)))
    (ENNReal.inv_ne_top.mpr (pow_ne_zero _ (by norm_num)))

private theorem halfPow_eq_invPow (n : ℕ) :
    ((1 : ℝ≥0∞) / 2) ^ n = (2 ^ n : ℝ≥0∞)⁻¹ := by
  rw [one_div, ← ENNReal.inv_pow]

/-- The real outer measure bound follows from the explicit finite ENNReal
factor and the existing quota arithmetic. -/
theorem lateSecondBatchAmbiguityEvent_measureReal_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (lateSecondBatchAmbiguityEvent (rate := rate) rewards C_star C_h) ≤
      1 / (4 * (N p : ℝ) ^ 2) := by
  have hbound := lateSecondBatchAmbiguityEvent_measure_le
    (rate := rate) rewards C_star C_h control0
  have hbound' :
      BootstrapPrivateRoundStreams.sourceInputLaw p
        (lateSecondBatchAmbiguityEvent (rate := rate) rewards C_star C_h) ≤
      ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
        (2 ^ AffineBatchDecoder.quota p : ℝ≥0∞)⁻¹ := by
    calc
      _ ≤ ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
          ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p := hbound
      _ = _ := by rw [halfPow_eq_invPow]
  have htoReal := ENNReal.toReal_mono (ambiguityUnionFactor_ne_top p) hbound'
  have hreal :
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (lateSecondBatchAmbiguityEvent (rate := rate) rewards C_star C_h) ≤
      ((p.m - 1 : ℕ) : ℝ) * p.T * 2 ^ AffineBatchDecoder.width p *
        (2 ^ AffineBatchDecoder.quota p : ℝ)⁻¹ := by
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_inv] using htoReal
  exact hreal.trans (ReferenceSuppressedDownTail.quota_union_factor_le p)

end Bandits.Support.ReferenceFirstCollectionLateUpAmbiguityBound

end
