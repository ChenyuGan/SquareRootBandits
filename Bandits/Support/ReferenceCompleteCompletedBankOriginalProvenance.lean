/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteDownOriginalPositiveCensus
public import Bandits.Support.ReferenceLiteralAwaitedAmbiguityRowObservation

import Lean.Elab.Tactic.Omega

/-!
# Original physical origins of completed banks

Every retained completed DOWN or UP bank entry is tied to its actual
prelaunch test or to the original postlaunch physical receiver call. The
classification preserves the bank accumulated across launch and includes the
completion-round positive, regardless of the later decoder or finish result.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.ReferenceCompleteDownOriginalPositiveCensus
open Bandits.Support.ReferenceFollowerDownDecoderReplay
open Bandits.Support.ReferenceGeneratedPrelaunchDownCohort
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceCoordinatorUpDecoderReplay
open Bandits.Support.ReferenceCoordinatorUpPhysicalCall
open Bandits.Support.ReferenceUpDecoderBankInvariant
open Bandits.Support.ReferenceCollectionUpFailureReadoutV2
open Bandits.Support.ReferenceSelectedAffinePairLaw
open scoped Classical

namespace Bandits.Support.ReferenceCompleteCompletedBankOriginalProvenance

variable {p : ConstructorDimensions.Parameters}

private theorem actualDownPositive_origin
    (rate : ReferenceActivePhysicalStep.RateInput p) (i : Fin (p.m - 1))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i records) :
    ∃ (re : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (call : ReferenceFollowerDownDecoderReplay.Call p),
      re ∈ records ∧ ReferenceFollowerDownDecoderReplay.actualDownCall i re = some call ∧
      AffineBatchDecoder.eligible call.2 ∧
      e = ⟨call.1, call.2.sample⟩ := by
  classical
  obtain ⟨call, hcall, hentry⟩ := List.mem_flatMap.mp he
  obtain ⟨re, hre, hcall⟩ := List.mem_filterMap.mp hcall
  have hcallPositive : AffineBatchDecoder.eligible
      ((ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1) := by
    by_contra hbad
    simp [AffineBatchDecoder.positiveAt, hbad] at hentry
  have hpositive : AffineBatchDecoder.eligible call.2 := by
    simpa [ActiveFollowerDownAcceptance.currentInputExtension] using hcallPositive
  have hmem : e ∈ [AffineBatchDecoder.entry p
      (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1] := by
    simpa [AffineBatchDecoder.positiveAt, hcallPositive] using hentry
  have hentryEq := List.mem_singleton.mp hmem
  refine ⟨re, call, hre, hcall, hpositive, ?_⟩
  simpa [ActiveFollowerDownAcceptance.currentInputExtension,
    AffineBatchDecoder.entry] using hentryEq

private theorem run_prefix_record_actual
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hstart : start = ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active start)
    (re : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hre : re ∈ (ReferenceActivePhysicalHorizon.run active z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start count hspan hmode).records) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      re.input.time z = some re ∧ start ≤ re.input.time.val ∧
      re.input.time.val < start + count := by
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hre
  have hcount := ReferenceActivePhysicalHorizon.run_record_count active z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start count hspan hmode
  have hjCount : j < count := by rw [← hcount]; exact hj
  let jFin : Fin count := ⟨j, hjCount⟩
  have hrecordAt := ReferenceLocalReleaseGateChronology.run_record_at active z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start hmode count hspan
    jFin
  have hrecordAt' : (ReferenceActivePhysicalHorizon.run active z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start count hspan hmode).records[j]'hj =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start j
        (by omega) hmode := by simpa only [jFin] using hrecordAt
  have htime : re.input.time.val = start + j := by
    rw [← hget]
    rw [hrecordAt']
    rfl
  have hs : start ≤ re.input.time.val := by omega
  have ht : re.input.time.val < start + count := by omega
  have hactual := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h re.input.time z active hlaunch (by rw [← hstart]; exact hs)
  have hidxStart : re.input.time.val - start = j := by omega
  have hidx : re.input.time.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = j := by
    rw [← hstart]
    exact hidxStart
  have hmodePhysical : ReferenceActivePhysicalHorizon.allActiveAtStart active
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) := by
    simpa only [hstart] using hmode
  have hrunRecord : ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) j
      (by omega) hmodePhysical = re := by
    have h := hrecordAt'.symm.trans hget
    simpa only [hstart] using h
  have hactualRecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h re.input.time z = some re := by
    calc
      _ = some (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) j
          (by omega) hmodePhysical) := by simpa only [hidx] using hactual
      _ = some re := congrArg some hrunRecord
  exact ⟨hactualRecord, hs, ht⟩

private theorem actualUpPositive_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i) :
    ∃ d, r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
      e.time = r.input.time ∧
      e.sample = ((r.input.rows r.input.selected).2 r.input.time).2 (1, i) ∧
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((r.input.rows r.input.selected).2 r.input.time).1 = some (1, Fin.cast rfl i) := by
  classical
  cases hup : r.output.coordinator.up with
  | none => simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hup] at he
  | some d =>
      have hselected : ReferenceCoordinatorUpDecoderReplay.retainedUpFollower d = i := by
        by_contra hne
        simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hup, hne] at he
      have hpositive : e ∈ AffineBatchDecoder.positiveAt p
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
          (ReferenceCoordinatorUpDecoderReplay.retainedUpTime d) := by
        simpa [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
          hup, hselected] using he
      have hentry : e = AffineBatchDecoder.entry p
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
          (ReferenceCoordinatorUpDecoderReplay.retainedUpTime d) := by
        simp only [AffineBatchDecoder.positiveAt] at hpositive
        split at hpositive
        · simpa only [List.mem_singleton, AffineBatchDecoder.entry] using hpositive
        · simp at hpositive
      have hfields := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hup
      rcases hfields with ⟨ledger, hsite, hledger, hbank, htime, hobs, hsender,
        hsample, hslot, henabled, hselectedFlag, hroundSample, hroundReward, hfeedback⟩
      have hentryEligible : AffineBatchDecoder.eligible
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input
            (ReferenceCoordinatorUpDecoderReplay.retainedUpTime d)) := by
        by_contra hbad
        simp [AffineBatchDecoder.positiveAt, hbad] at hpositive
      have heligible : AffineBatchDecoder.eligible
          (CoordinatorUpReception.roundInput d.input) := by
        change AffineBatchDecoder.eligible
          (CoordinatorUpReception.roundInput d.input) at hentryEligible
        exact hentryEligible
      have hgateFacts := (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput_eligible_iff d).mp
        heligible
      have hgate : CoordinatorUpReception.receptionGate d.input := hgateFacts.1
      have htimeEntry : e.time = r.input.time := by
        rw [hentry]
        simp [AffineBatchDecoder.entry, ReferenceCoordinatorUpDecoderReplay.retainedUpTime,
          htime]
      have hsampleEntry : e.sample = ((r.input.rows r.input.selected).2 r.input.time).2 (1, i) := by
        rw [hentry]
        change d.input.affineSample = ((r.input.rows r.input.selected).2 r.input.time).2 (1, i)
        rw [hsample]
        have hindex : CoordinatorUpMeasurability.selectedChannelFollower
            ((r.input.rows r.input.selected).2 r.input.time) = Fin.cast rfl i := by
          apply Fin.ext
          rw [CoordinatorUpMeasurability.selectedChannelFollower_val,
            ← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
          exact congrArg Fin.val (hsender.symm.trans hselected)
        rw [hindex]
        rfl
      have hchan : ReferenceSelectedAffinePairLaw.selectedChannel p
          ((r.input.rows r.input.selected).2 r.input.time).1 = some (1, Fin.cast rfl i) := by
        have hslotUp : d.input.slot = PublicDiscreteDraws.upSlot := hgate.2.1
        have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            ((r.input.rows r.input.selected).2 r.input.time).1 = i := by
          rw [← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
          exact hsender.symm.trans hselected
        have hslotSource : PublicDiscreteDraws.slotDraw
            ((r.input.rows r.input.selected).2 r.input.time).1 = PublicDiscreteDraws.upSlot := by
          simpa only [hslot] using hslotUp
        rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _ hslotSource]
        apply congrArg some
        apply Prod.ext
        · rfl
        · have hchannelIndex : PublicDiscreteDraws.selectedFollowerDraw
              p.two_le_m p.m_lt_K ((r.input.rows r.input.selected).2 r.input.time).1 =
                Fin.cast rfl i := by
            apply Fin.ext
            simp only [Fin.val_cast]
            exact congrArg Fin.val hdraw
          exact hchannelIndex
      exact ⟨d, rfl, hselected, htimeEntry, hsampleEntry, hchan⟩

theorem completedDownBatch_original_entry_provenance
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (W : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (hW : ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i = some W) :
    ∀ e, e ∈ W →
      (∃ test ∈ ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
          rate rewards C_star C_h z i,
        ReferenceGeneratedPrelaunchDownCohort.testEntry test = e ∧
        test.time.val < ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h ∧ test.sent = none ∧
        test.sample = ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2
          test.time).2 (0, i)) ∨
      (∃ re : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          e.time z = some re ∧
        e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [re] ∧
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
          e.time.val ∧ e.time.val ≤ t.val ∧
        e.sample = ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2
          e.time).2 (0, i) ∧
        ReferenceSelectedAffinePairLaw.selectedChannel p
          ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 e.time).1 =
            some (0, i) ∧
        re.input.rows = z.1.2 ∧
        re.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        re.input.time = e.time ∧ re.input.rewards = rewards ∧
        (e.time.val < t.val ∨ e.time.val = t.val)) := by
  classical
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let k := t.val - s
  have hby : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z := by
    by_contra hnot
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hnot] at hrecord
    cases hrecord
  have hsle : s ≤ t.val := hby.2
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := hby.1
  let active := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z rewards C_star C_h hcross
  have hstartStrict : s < p.T := by
    have ht := t.isLt
    omega
  have hfullSpan : s + (p.T - s) ≤ p.T := by omega
  have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
    rate z rewards C_star C_h active hlaunch
  have hfullRun := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate z rewards C_star C_h active hlaunch
  have hcount := ReferenceActivePhysicalHorizon.run_record_count active z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s)
    hfullSpan hmode
  have hRlength : R.length = p.T - s := by
    change (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length = p.T - s
    rw [hfullRun]
    simpa [s] using hcount
  have hk : k < R.length := by rw [hRlength]; dsimp [k]; omega
  let kFin : Fin R.length := ⟨k, hk⟩
  have hspan : s + k ≤ p.T := by dsimp [k]; omega
  let prefixRun := ReferenceActivePhysicalHorizon.run active z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k hspan hmode
  have hprefixCount := ReferenceActivePhysicalHorizon.run_record_count active z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k hspan hmode
  have hfullCount := hcount
  have hkFull : k < p.T - s := by rw [← hRlength]; exact hk
  have hprefixRecords : R.take k = prefixRun.records := by
    change (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).take k = prefixRun.records
    rw [hfullRun]
    apply List.ext_getElem
    · rw [List.length_take, hfullCount, hprefixCount,
        Nat.min_eq_left (Nat.le_of_lt hkFull)]
    · intro j hjLeft hjRight
      have hj : j < k := by rw [ReferenceActivePhysicalHorizon.run_record_count] at hjRight; exact hjRight
      let jp : Fin k := ⟨j, hj⟩
      let jf : Fin (p.T - s) := ⟨j, by omega⟩
      have hfa := ReferenceLocalReleaseGateChronology.run_record_at active z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s hmode
        (p.T - s) hfullSpan jf
      have hpa := ReferenceLocalReleaseGateChronology.run_record_at active z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s hmode k hspan jp
      simpa only [List.getElem_take, jf, jp] using hfa.trans hpa.symm
  have hrecordValue : r = ReferenceAssignmentPayloadChronology.actualRunRecordAt active
      z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
      (by dsimp [k, s]; omega) hmode := by
    apply Option.some.inj
    calc
      some r = ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z := hrecord.symm
      _ = some (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
          (by dsimp [k, s]; omega) hmode) := by
            simpa only [s, k, hmode] using
              ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
                rate rewards C_star C_h t z active hlaunch hsle
  have hlogged := ReferenceFirstLiveDownCompletionReadout.completedDownBatch_spec r i W hW
  obtain ⟨_, logged, cut, hlogged, hcut, hcmp, happended, _, _⟩ := hlogged
  have hincoming := ReferenceCompleteDownOriginalPositiveCensus.actual_incoming_down_collected_eq
    rate rewards C_star C_h z t r i logged hrecord hlogged
  have hloggedCurrent : logged.downBatch.pending ++
      AffineBatchDecoder.positiveAt p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged))
        r.input.time = W := by
    simpa only [ReferenceFirstLiveDownCompletionReadout.appendedDownBatch] using happended.symm
  intro e he
  have heappend : e ∈ logged.downBatch.pending ++
      AffineBatchDecoder.positiveAt p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged))
        r.input.time := by rw [hloggedCurrent]; exact he
  rcases List.mem_append.mp heappend with hold | hcurrent
  · have hecollected : e ∈ AffineBatchDecoder.collected logged.downBatch := by
      simp only [AffineBatchDecoder.collected, List.mem_append]
      exact Or.inr hold
    rw [hincoming] at hecollected
    rcases List.mem_append.mp hecollected with htest | hsuffix
    · obtain ⟨test, htestSource, heqTest⟩ := List.mem_map.mp htest
      have hprov := ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_test_provenance
        rate rewards C_star C_h z i test htestSource
      rcases hprov with ⟨a, ha, hact, hpretime, hsample, hslot, hdraw, q, hq,
        hcrossq, hactivation, hqstart, hqend, u, hu, hown, hpositive, hlearner,
        hcoordAction, hfollowerAction, hsent⟩
      have hpretime' : test.time.val < s := by
        simpa [s, ReferenceCompletePhysicalHistory.physicalStart,
          ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using hpretime
      exact Or.inl ⟨test, htestSource, heqTest, hpretime', hsent, hsample⟩
    · obtain ⟨re, call, hre, hcall, hpositive, heentry⟩ :=
        actualDownPositive_origin rate i (R.take k) e hsuffix
      have hactualAndRange := run_prefix_record_actual rate rewards C_star C_h z active
        hlaunch s k hspan (by rfl) hmode re (by rwa [hprefixRecords] at hre)
      rcases hactualAndRange with ⟨hreActual, htimeLo, htimeHi⟩
      have hcallFields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
        re i call hcall
      have hentryTime : e.time = re.input.time := by
        have h := congrArg AffineBatchDecoder.Entry.time heentry
        rw [hcallFields.1] at h
        exact h
      have hcallTime : call.1 = e.time := hcallFields.1.trans hentryTime.symm
      have hreActualE : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h e.time z = some re := by
        rw [hentryTime]
        exact hreActual
      have hfields := ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
        rate rewards C_star C_h z e.time re hreActualE
      have hsample : e.sample = ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2
          e.time).2 (0, i) := by
        rw [heentry, hcallFields.2.1]
        simp only [ReferenceActivePhysicalStep.RoundInput.row, hfields.1,
          hfields.2.1, hfields.2.2.1, hcallTime]
        rfl
      have hchan : ReferenceSelectedAffinePairLaw.selectedChannel p
          ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 e.time).1 =
            some (0, i) := by
        have hsel := hcallFields.2.2.mp hpositive.1
        have hdrawRe : PublicDiscreteDraws.slotDraw (re.input.row.2 re.input.time).1 =
            PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (re.input.row.2 re.input.time).1 = i := by
          simpa only [ActiveFollowerDownAcceptance.downSelected] using hsel
        have hdraw : PublicDiscreteDraws.slotDraw
            ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 e.time).1 =
              PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 e.time).1 = i := by
          simpa only [ReferenceActivePhysicalStep.RoundInput.row, hfields.1,
            hfields.2.1, ← hfields.2.2.1] using hdrawRe
        have hchannel := ReferenceSelectedAffinePairLaw.selectedChannel_of_down p _ hdraw.1
        rw [hdraw.2] at hchannel
        exact hchannel
      have htimeLE : e.time.val ≤ t.val := by
        rw [hentryTime]
        dsimp [s, k] at htimeHi ⊢
        omega
      have htimeLoEntry : s ≤ e.time.val := by simpa [hentryTime] using htimeLo
      have hbefore : e.time.val < t.val := by
        rw [hentryTime]
        dsimp [s, k] at htimeHi ⊢
        omega
      have hpositiveEntry : e ∈ AffineBatchDecoder.positiveAt p
          (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 := by
        apply (ReferencePrelaunchFollower.mem_positiveAt_iff p
          (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 e).2
        constructor
        · exact hpositive
        · simpa [AffineBatchDecoder.entry,
            ActiveFollowerDownAcceptance.currentInputExtension] using heentry
      have hocc : e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [re] := by
        change e ∈ ReferenceFollowerDownDecoderReplay.positiveCallEntries
          (ReferenceFollowerDownDecoderReplay.actualDownCalls i [re])
        change e ∈ List.flatMap
          (fun call => AffineBatchDecoder.positiveAt p
            (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1)
          (ReferenceFollowerDownDecoderReplay.actualDownCalls i [re])
        rw [List.mem_flatMap]
        refine ⟨call, ?_, hpositiveEntry⟩
        simp [ReferenceFollowerDownDecoderReplay.actualDownCalls, hcall]
      exact Or.inr ⟨re, hreActualE, hocc,
        by simpa [s] using htimeLoEntry, htimeLE, hsample, hchan, hfields.1, hfields.2.1,
        hfields.2.2.1, hfields.2.2.2,
        Or.inl hbefore⟩
  · have hpositiveLogged :
        AffineBatchDecoder.eligible
          (ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged)
            r.input.time) := by
      by_cases heligible : AffineBatchDecoder.eligible
          (ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged)
            r.input.time)
      · exact heligible
      · simp [AffineBatchDecoder.positiveAt, heligible] at hcurrent
    obtain ⟨inputState, inputMemory, actualChoice, hinput, _hinputDomain,
      hstartActual, hchoiceActual, _hchoiceDomain, _hoperationDomain⟩ :=
      ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
        (rate := rate) rewards C_star C_h z kFin i
    have hRrecord : R[k] = r := by
      have hRactualRunRecord : R[k] =
          ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
            (by dsimp [s, k]; omega) hmode := by
        simpa only [R, hfullRun, s] using ReferenceLocalReleaseGateChronology.run_record_at active
          z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s hmode
          (p.T - s) hfullSpan ⟨k, hkFull⟩
      exact hRactualRunRecord.trans hrecordValue.symm
    have hordinary : prefixRun.finalState.followers i = .ordinary inputState inputMemory := by
      have hinput' := hinput
      rw [hRrecord] at hinput'
      rw [hrecordValue] at hinput'
      change prefixRun.finalState.followers i = .ordinary inputState inputMemory at hinput'
      exact hinput'
    have hchoiceConfig :
        ((R[k]).output.preparation.followers.followers i).configuration =
          .ordinary actualChoice inputMemory := by
      simpa only [ReferenceFollowerFixedReply.actualChoice] using hchoiceActual
    let record := R[k]
    let prepared := record.output.preparation.followers.followers i
    let own := record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    have hpreparedConfig : prepared.configuration = .ordinary actualChoice inputMemory := by
      simpa only [record, prepared] using hchoiceConfig
    have hloggedAtR : (R[k].output.followers i).downInput = some logged := by
      rw [hRrecord]
      exact hlogged
    have hloggedObservation : (record.output.preparation.observeFollower i).downInput =
        some logged := by
      have h := hloggedAtR
      rw [← ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics
        record i] at h
      exact h
    have hloggedFinish :
        (ReferenceActivePhysicalStep.finishFollower record.output.preparation.coordinator.downView
          prepared own).downInput = some logged := by
      change (ReferenceActivePhysicalStep.finishFollower
        record.output.preparation.coordinator.downView prepared own).downInput = some logged
        at hloggedObservation
      exact hloggedObservation
    have hfinishFrame :
        (ReferenceActivePhysicalStep.finishFollower record.output.preparation.coordinator.downView
          prepared own).downInput =
        (ReferenceActivePhysicalStep.recordFollower record.output.preparation.coordinator.downView
          prepared.follower prepared.row prepared.activation prepared.time prepared.active
          prepared.arm own actualChoice).downInput := by
      classical
      rw [ReferenceActivePhysicalStep.finishFollower, hpreparedConfig]
      cases hrecorded : ReferenceActivePhysicalStep.recordFollower
          record.output.preparation.coordinator.downView prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm own actualChoice with
      | mk result downInput down =>
          cases result with
          | error failure => simp [hrecorded]
          | ok post =>
              cases hrelease : DeclaredFollowerLocalRound.releaseAndFinish rate
                  prepared.follower prepared.row prepared.time own actualChoice inputMemory post with
              | error failure => simp [hrecorded, hrelease]
              | ok next => cases next; simp [hrecorded, hrelease]
    have hrecordedInput := hfinishFrame.symm.trans hloggedFinish
    have hlogging : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
        prepared.activation prepared.time (prepared.arm, own) actualChoice = .ok logged := by
      by_cases hstatus : actualChoice.status = .unoccupied
      · cases hlog : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
            prepared.activation prepared.time (prepared.arm, own) actualChoice with
        | error failure =>
            simp [ReferenceActivePhysicalStep.recordFollower, hstatus, hlog] at hrecordedInput
        | ok loggedState =>
            have heq : loggedState = logged := by
              simpa [ReferenceActivePhysicalStep.recordFollower, hstatus, hlog] using
                hrecordedInput
            exact congrArg Except.ok heq
      · simp [ReferenceActivePhysicalStep.recordFollower, hstatus] at hrecordedInput
    have hloggingFrame := ActiveFollowerLogging.checkedLogging_success_frame
      prepared.follower prepared.row prepared.activation prepared.time (prepared.arm, own)
      actualChoice logged hlogging
    have hstatus : logged.status = actualChoice.status := hloggingFrame.2.2.2.2.1
    have hcall : ReferenceFollowerDownDecoderReplay.actualDownCall i r = some
        (r.input.time, ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row
          r.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i)
          rate actualChoice) := by
      have hcfg : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration r i =
          .ordinary actualChoice inputMemory := by
        change (r.output.preparation.followers.followers i).configuration =
          .ordinary actualChoice inputMemory
        rw [← hRrecord]
        exact hchoiceConfig
      have hc := ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary r i actualChoice
        inputMemory hcfg
      have hrow : ReferenceFollowerDownDecoderReplay.preparedChoiceRow r i = r.input.row :=
        (r.output.preparation.follower_alignment i).1
      rw [ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime, hrow] at hc
      exact hc
    have heCall : e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [r] := by
      have htrace :
          ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged) =
          ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate actualChoice) := by
        funext v
        simp [ActiveFollowerDownAcceptance.currentInputExtension,
          ActiveFollowerDownAcceptance.currentRoundInput, hstatus]
      have hentry : e ∈ AffineBatchDecoder.positiveAt p
          (ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate actualChoice))
          r.input.time := by
        rw [htrace] at hcurrent
        exact hcurrent
      change e ∈ ReferenceFollowerDownDecoderReplay.positiveCallEntries
        (ReferenceFollowerDownDecoderReplay.actualDownCalls i [r])
      change e ∈ List.flatMap
        (fun call => AffineBatchDecoder.positiveAt p
          (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1)
        (ReferenceFollowerDownDecoderReplay.actualDownCalls i [r])
      rw [List.mem_flatMap]
      refine ⟨(r.input.time,
        ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate actualChoice),
        ?_, hentry⟩
      simp [ReferenceFollowerDownDecoderReplay.actualDownCalls, hcall]
    obtain ⟨re, call, hre, hcall', hpositive, heentry⟩ :=
      actualDownPositive_origin rate i [r] e heCall
    have hreEq : re = r := by simpa using hre
    subst re
    have hcallFields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
      r i call hcall'
    have hrecordFields := ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
      rate rewards C_star C_h z t r hrecord
    have htimeEq : e.time = t := by
      have hentryTime := congrArg AffineBatchDecoder.Entry.time heentry
      have htime : e.time = r.input.time := by
        rw [hcallFields.1] at hentryTime
        exact hentryTime
      exact htime.trans hrecordFields.2.2.1
    have hreActual :
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          e.time z = some r := by
      rw [htimeEq]
      exact hrecord
    have hfields := ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
      rate rewards C_star C_h z e.time r hreActual
    have hsample : e.sample = ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2
        e.time).2 (0, i) := by
      have hcallTime : call.1 = e.time := by
        calc
          call.1 = r.input.time := hcallFields.1
          _ = t := hrecordFields.2.2.1
          _ = e.time := htimeEq.symm
      rw [heentry, hcallFields.2.1]
      simp only [ReferenceActivePhysicalStep.RoundInput.row, hfields.1,
        hfields.2.1, hfields.2.2.1, hcallTime]
      rfl
    have hchan : ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 e.time).1 =
          some (0, i) := by
      have hsel := hcallFields.2.2.mp hpositive.1
      have hdrawR : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
          PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r.input.row.2 r.input.time).1 = i := by
        simpa only [ActiveFollowerDownAcceptance.downSelected] using hsel
      have hdraw : PublicDiscreteDraws.slotDraw
          ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 e.time).1 =
            PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 e.time).1 = i := by
        simpa only [ReferenceActivePhysicalStep.RoundInput.row, hfields.1,
          hfields.2.1, ← hfields.2.2.1] using hdrawR
      have hchannel := ReferenceSelectedAffinePairLaw.selectedChannel_of_down p _ hdraw.1
      rw [hdraw.2] at hchannel
      exact hchannel
    have htimeVal : e.time.val = t.val := congrArg Fin.val htimeEq
    have htimeLo : ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h ≤ e.time.val := by
      simpa [s, htimeVal] using hsle
    exact Or.inr ⟨r, hreActual, by simpa using heCall,
      htimeLo, le_of_eq htimeVal,
      hsample, hchan, hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2,
      Or.inr (by exact congrArg Fin.val htimeEq)⟩

theorem completedUpBatch_original_entry_provenance
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (W : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (hW : ReferenceCollectionUpFailureReadoutV2.completedUpBatch rate r i = some W) :
    ∀ e, e ∈ W →
      ∃ re : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          e.time z = some re ∧
        e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries re i ∧
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
          e.time.val ∧ e.time.val ≤ t.val ∧
        e.sample = ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2
          e.time).2 (1, i) ∧
        ReferenceSelectedAffinePairLaw.selectedChannel p
          ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 e.time).1 =
            some (1, Fin.cast rfl i) ∧
        re.input.rows = z.1.2 ∧
        re.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        re.input.time = e.time ∧ re.input.rewards = rewards ∧
        (e.time.val < t.val ∨ e.time.val = t.val) := by
  classical
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let k := t.val - s
  have hby : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z := by
    by_contra hnot
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hnot] at hrecord
    cases hrecord
  have hsle : s ≤ t.val := hby.2
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := hby.1
  let active := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z rewards C_star C_h hcross
  have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
    rate z rewards C_star C_h active hlaunch
  have hspan : s + k ≤ p.T := by dsimp [s, k]; omega
  let prefixRun := ReferenceActivePhysicalHorizon.run active z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k hspan hmode
  have hrecordValue : r = ReferenceAssignmentPayloadChronology.actualRunRecordAt active
      z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
      (by dsimp [s, k]; omega) hmode := by
    apply Option.some.inj
    calc
      some r = ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z := hrecord.symm
      _ = some (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
          (by dsimp [s, k]; omega) hmode) := by
            simpa only [s, k, hmode] using
              ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
                rate rewards C_star C_h t z active hlaunch hsle
  have hstate : r.input.state = prefixRun.finalState := by
    rw [hrecordValue]
    rfl
  have hcompleted := ReferenceCollectionUpFailureReadoutV2.completedUpBatch_spec
    rate r i W hW
  obtain ⟨_, d, hd, hselected, _, _⟩ := hcompleted
  have hfields := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd
  obtain ⟨ledger, hsite, hledger, hbank, htime, hobs, hsender, hsample,
    hslot, henabled, hselectedFlag, hroundSample, hroundReward, hfeedback⟩ := hfields
  have hordinaryRecord : r.input.state.coordinator ≠ .dagger := by
    intro hdagger
    simp [ReferenceCoordinatorUpPhysicalCall.siteLedger?,
      ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      hdagger] at hsite
  have hordinary : prefixRun.finalState.coordinator ≠ .dagger := by
    intro hdagger
    apply hordinaryRecord
    simpa [hstate] using hdagger
  obtain ⟨canonical, hcanonical, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate z rewards C_star C_h hcross
  rcases hcanonical with ⟨hcanonicalLaunch, hfirst, hinitialBank, _, _⟩
  have hactive : active = canonical := Option.some.inj (hlaunch.symm.trans hcanonicalLaunch)
  have hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant active := by
    have hcan : ReferenceUpDecoderBankInvariant.upBankInvariant canonical := by
      simpa [ReferenceUpDecoderBankInvariant.upBankInvariant, hfirst, hinitialBank] using
        ReferenceUpDecoderBankInvariant.firstState_upBankInvariant
          canonical.activations canonical.followers
    rw [hactive]
    exact hcan
  have hempty : AffineBatchDecoder.collected (active.upDecoderBank i) = [] := by
    rw [hactive, hinitialBank]
    simp [CoordinatorUpReception.initialUpDecoderBank, AffineBatchDecoder.initial,
      AffineBatchDecoder.collected]
  have hcollect := ReferenceCoordinatorUpDecoderReplay.run_collected_upPositiveEntries
    active z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
    hspan hmode hinitial hordinary i
  have hcollectInput : AffineBatchDecoder.collected (r.input.state.upDecoderBank i) =
      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries prefixRun.records i := by
    rw [hstate]
    simpa [prefixRun, hempty] using hcollect
  obtain ⟨d', hd', hselected', hcheck, heligible, hthreshold, happended⟩ :=
    (ReferenceCollectionUpFailureReadoutV2.completedUpBatch_eq_some_iff rate r i W).mp hW
  have hdEq : d' = d := Option.some.inj (hd'.symm.trans hd)
  subst d'
  have hWentries : (r.input.state.upDecoderBank i).pending ++
      AffineBatchDecoder.positiveAt p (CoordinatorUpReception.traceAt d.input) d.input.time = W := by
    simpa only [ReferenceCollectionUpFailureReadoutV2.appendedUp, hbank, hselected] using
      happended
  intro e he
  have heappend : e ∈ (r.input.state.upDecoderBank i).pending ++
      AffineBatchDecoder.positiveAt p (CoordinatorUpReception.traceAt d.input) d.input.time := by
    rw [hWentries]
    exact he
  rcases List.mem_append.mp heappend with hold | hcurrent
  · have hcollected : e ∈ AffineBatchDecoder.collected (r.input.state.upDecoderBank i) := by
      simp only [AffineBatchDecoder.collected, List.mem_append]
      exact Or.inr hold
    rw [hcollectInput] at hcollected
    obtain ⟨re, hre, hepos⟩ := List.mem_flatMap.mp hcollected
    have hactualAndRange := run_prefix_record_actual rate rewards C_star C_h z active
      hlaunch s k hspan (by rfl) hmode re hre
    rcases hactualAndRange with ⟨hreActual, htimeLo, htimeHi⟩
    obtain ⟨d0, hd0, hreceiver, hentryTime, hentrySample, hentryChannel⟩ :=
      actualUpPositive_fields rate re i e hepos
    have hactualE : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h e.time z = some re := by
      rw [hentryTime]
      exact hreActual
    have horiginal := ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
      rate rewards C_star C_h z e.time re hactualE
    have hbefore : e.time.val < t.val := by
      have htimeHi' : re.input.time.val < t.val := by
        dsimp [s, k] at htimeHi ⊢
        omega
      have heq := congrArg Fin.val hentryTime
      omega
    have htimeLE : e.time.val ≤ t.val := hbefore.le
    have hsampleSource : e.sample = ((z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 e.time).2 (1, i) := by
      rw [horiginal.1, horiginal.2.1, horiginal.2.2.1] at hentrySample
      exact hentrySample
    have hchannelSource : ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 e.time).1 =
          some (1, Fin.cast rfl i) := by
      rw [horiginal.1, horiginal.2.1, horiginal.2.2.1] at hentryChannel
      exact hentryChannel
    exact ⟨re, hactualE, hepos, by simpa [hentryTime] using htimeLo,
      htimeLE, hsampleSource, hchannelSource,
      horiginal.1, horiginal.2.1, horiginal.2.2.1, horiginal.2.2.2, Or.inl hbefore⟩
  · have hrecordEntry : e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i := by
      have hcurrent' : e ∈ AffineBatchDecoder.positiveAt p
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time := by
        change e ∈ AffineBatchDecoder.positiveAt p
          (fun _ => CoordinatorUpReception.roundInput d.input) d.input.time at hcurrent
        change e ∈ AffineBatchDecoder.positiveAt p
          (fun _ => CoordinatorUpReception.roundInput d.input) d.input.time
        exact hcurrent
      simpa [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
        ReferenceCoordinatorUpDecoderReplay.retainedUpFollower,
        ReferenceCoordinatorUpDecoderReplay.retainedUpTime, hd, hselected] using hcurrent'
    obtain ⟨d0, hd0, hreceiver, hentryTime, hentrySample, hentryChannel⟩ :=
      actualUpPositive_fields rate r i e hrecordEntry
    have horiginalAtT := ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
      rate rewards C_star C_h z t r hrecord
    have htimeEqFin : e.time = t := hentryTime.trans horiginalAtT.2.2.1
    have hactualE : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h e.time z = some r := by
      rw [htimeEqFin]
      exact hrecord
    have horiginal := ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
      rate rewards C_star C_h z e.time r hactualE
    have hsampleSource : e.sample = ((z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 e.time).2 (1, i) := by
      rw [horiginalAtT.1, horiginalAtT.2.1, horiginalAtT.2.2.1] at hentrySample
      rw [← htimeEqFin] at hentrySample
      exact hentrySample
    have hchannelSource : ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 e.time).1 =
          some (1, Fin.cast rfl i) := by
      rw [horiginalAtT.1, horiginalAtT.2.1, horiginalAtT.2.2.1] at hentryChannel
      rw [← htimeEqFin] at hentryChannel
      exact hentryChannel
    have htimeVal : e.time.val = t.val := congrArg Fin.val htimeEqFin
    have htimeLo : ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h ≤ e.time.val := by
      simpa [s, htimeVal] using hsle
    exact ⟨r, hactualE, hrecordEntry, htimeLo,
      by rw [htimeEqFin], hsampleSource, hchannelSource, horiginal.1, horiginal.2.1,
      horiginal.2.2.1, horiginal.2.2.2, Or.inr (congrArg Fin.val htimeEqFin)⟩

end Bandits.Support.ReferenceCompleteCompletedBankOriginalProvenance

end
