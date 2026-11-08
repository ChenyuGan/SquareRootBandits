/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceCollectionUpFailureReadoutV2
public import Bandits.Support.ReferenceGeneratedUpAwaitedAmbiguityTail

/-!
# Probability bound for the literal fixed-awaited UP decoder failure

The finite-calendar event is covered by the original-source awaited UP
ambiguity event. The pointwise argument reconstructs the actual launch branch,
run, retained diagnostic and awaited interval from the physical readout.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceCollectionUpFailureReadoutV2
open Bandits.Support.ReferenceGeneratedUpAwaitedAmbiguityTail
open scoped Classical

namespace Bandits.Support.ReferenceAwaitedUpDecoderErrorProbability

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

/-- The literal finite-calendar event of an actual fixed-awaited UP failure. -/
def fixedAwaitedUpFailureEvent : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  {z | ∃ t : Fin p.T,
    ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt rate rewards C_star C_h z t}

private theorem actualLookup_start_le (v : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hlookup : ReferenceCollectionUpFailureReadoutV2.lookup rate rewards C_star C_h v z = some r) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ v.val := by
  by_contra hnot
  have hfuture : v.val < ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h :=
    Nat.lt_of_not_ge hnot
  have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
    rate rewards C_star C_h v z hfuture
  change ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h v z =
    some r at hlookup
  rw [hnone] at hlookup
  cases hlookup

private theorem roundInput_ext
    {left right : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  simp_all

private theorem originalSourceCurrentRecord_eq_runRecord
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
        (rate := rate) rewards C_star C_h q t s hs control0 i z =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
        s (t.val - s) (by omega)
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).property := by
  let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hinput :
      ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z =
        ReferenceActivePhysicalHorizon.roundInputAt input.val.1 input.val.2.1
          input.val.2.2.1 input.val.2.2.2 s input.property
          (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1
            input.val.2.2.1 input.val.2.2.2 s (t.val - s) (by omega) input.property)
          ⟨s + (t.val - s), by omega, by omega⟩ := by
    apply roundInput_ext
    · rfl
    · rfl
    · rfl
    · apply Fin.ext
      exact (Nat.add_sub_of_le hs).symm
    · rfl
  dsimp only [ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord,
    ReferenceAssignmentPayloadChronology.actualRunRecordAt]
  exact congrArg (fun x =>
    (⟨x, ReferenceActivePhysicalStep.step x, rfl⟩ :
      ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) hinput

private theorem sourceRun_lookup
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (v : Fin p.T) (hsv : s ≤ v.val) :
    ReferenceCollectionUpFailureReadoutV2.lookup rate rewards C_star C_h v z.1 =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
        s (v.val - s) (by omega)
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).property) := by
  let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hlaunch := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput_launch
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hstartElapsed : ReferenceInitializationRun.elapsed p
      (ReferenceCompletePhysicalHistory.generatedBoundary rate z.1 rewards C_star C_h).completed = s := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using z.2.2.2
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.1 rewards C_star C_h = s := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart] using hstartElapsed
  have hrows : input.val.2.1 = z.1.1.2 := rfl
  have hselected : input.val.2.2.1 =
      ActualInitializationPhysicalStep.selectedRowIndex p z.1 := rfl
  have hrewards : input.val.2.2.2 = rewards := rfl
  have hstartInput : ReferenceCompletePhysicalHistory.physicalStart
      rate z.1 input.val.2.2.2 C_star C_h = s := by
    simpa only [← hrewards] using hstart
  have hrecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h v z.1 input.val.1 hlaunch (by rw [hstart]; exact hsv)
  change ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h v z.1 = _
  simpa only [input, hstartInput, ← hrows, ← hselected, ← hrewards] using hrecord

/-- Every literal detecting date is covered by the same original-source UP
awaited ambiguity event, with its actual run and unsplit pending bank. -/
theorem fixedAwaitedUpFailureAt_mem_upAwaitedAmbiguityEvent
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (hfail : ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt rate rewards C_star C_h z t) :
    z ∈ ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEvent (rate := rate) rewards C_star C_h control0 := by
  classical
  rcases hfail with ⟨r, i, U, W, a, hlookup, hcompleted, hat, hsigma,
    hmulti, hentries, hinterval⟩
  have hby : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z := by
    by_contra hnot
    have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hnot
    change ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
      some r at hlookup
    rw [hnone] at hlookup
    cases hlookup
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
    simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hby.1
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hs : s ≤ t.val := hby.2
  let q := ActualInitializationPhysicalStep.selectedRowIndex p z
  rcases (ReferenceCollectionUpFailureReadoutV2.completedUpBatch_eq_some_iff rate r i W).mp hcompleted with
    ⟨d, hd, hdi, hcheck, heligible, hthreshold, happended⟩
  have hseedLaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z rewards C_star C_h hcross
  let seed := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
    rate z rewards C_star C_h seed hseedLaunch
  have hrRun : r = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      seed z.1.2 q rewards s (t.val - s) (by omega) hmode := by
    have hactual := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t z seed hseedLaunch hs
    have hlookupRun : ReferenceCollectionUpFailureReadoutV2.lookup rate rewards C_star C_h t z =
        some (ReferenceAssignmentPayloadChronology.actualRunRecordAt
          seed z.1.2 q rewards s (t.val - s) (by omega) hmode) := by
      change ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = _
      simpa only [s, q, ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput] using hactual
    exact (Option.some.inj (hlookupRun.symm.trans hlookup)).symm
  have hrows : r.input.rows = z.1.2 := by
    rw [hrRun]
    rfl
  have hselected : r.input.selected = q := by
    rw [hrRun]
    rfl
  have htime : r.input.time = t := by
    rw [hrRun]
    apply Fin.ext
    exact Nat.add_sub_of_le hs
  have hrewards : r.input.rewards = rewards := by
    rw [hrRun]
    rfl
  have hfields := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd
  rcases hfields with ⟨ledger, hsite, hledger, hbank, hdtime, hobs, hsender,
    hsample, hslot, henabled, hselectedFlag, hroundSample, hroundReward, hfeedback⟩
  have hgate : CoordinatorUpReception.receptionGate d.input :=
    (CoordinatorUpReception.roundInput_selected_iff_gate d.input).mp heligible.1
  let slice := (z.1.2 q).2 t
  have hslotUp : PublicDiscreteDraws.slotDraw slice.1 = PublicDiscreteDraws.upSlot := by
    calc
      PublicDiscreteDraws.slotDraw slice.1 =
          PublicDiscreteDraws.slotDraw ((r.input.rows r.input.selected).2 r.input.time).1 := by
        simp [slice, hrows, hselected, htime]
      _ = d.input.slot := hslot.symm
      _ = PublicDiscreteDraws.upSlot := hgate.2.1
  have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K slice.1 = i := by
    have hselectedIndex := hsender.symm.trans hdi
    have hslice : CoordinatorUpMeasurability.selectedFollowerIndex slice = i := by
      simpa [slice, hrows, hselected, htime] using hselectedIndex
    rw [← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
    exact hslice
  have hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p slice.1 = some (1, i) := by
    rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p slice.1 hslotUp, hdraw]
    rfl
  have hrowIndex : PrivateSourceStreams.coordinatorIndex p z.2.1.2 = q := by
    simp [q, ActualInitializationPhysicalStep.selectedRowIndex]
  have hselector : ReferenceSelectedAffinePairLaw.selector p t z = (q, some (1, i)) :=
    (ReferenceSelectedAffinePairLaw.selector_eq_iff p q t (1, i) z).mpr
      ⟨hrowIndex, hchannel⟩
  have hbranch : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h q t (1, i) s := by
    refine ⟨hselector, ?_, ?_⟩
    · simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput] using hby.1
    · simp [s, ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput]
  let launchSource : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i := ⟨z, hbranch⟩
  let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
      (rate := rate) rewards C_star C_h q t s hs control0 i launchSource
  have hlaunch := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput_launch
      (rate := rate) rewards C_star C_h q t s hs control0 i launchSource
  have hinputRows : input.val.2.1 = z.1.2 := rfl
  have hinputSelected : input.val.2.2.1 = q := by
    exact ReferenceGeneratedAffineHashHalf.selectedRowIndex_of_generatedLaunchBranch
      (rate := rate) rewards C_star C_h q t (1, i) s launchSource
  have hinputRewards : input.val.2.2.2 = rewards := rfl
  let current := ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
    (rate := rate) rewards C_star C_h q t s hs control0 i launchSource
  have hcurrentRun := originalSourceCurrentRecord_eq_runRecord
    (rate := rate) rewards C_star C_h q t s hs control0 i launchSource
  have hcurrent : current = r := by
    have hcurrentLookup := sourceRun_lookup (rate := rate) rewards C_star C_h
      q t s hs control0 i launchSource t hs
    change ReferenceCollectionUpFailureReadoutV2.lookup rate rewards C_star C_h t z = _
      at hcurrentLookup
    rw [← hcurrentRun] at hcurrentLookup
    exact Option.some.inj (hcurrentLookup.symm.trans hlookup)
  have hdCurrent : current.output.coordinator.up = some d := by
    rw [hcurrent]
    exact hd
  have hpCurrent : ReferenceActiveAffinePositiveTest.upPositive current.input = true := by
    have h := ReferenceActiveAffinePositiveTest.record_upPositive current
    rw [hdCurrent, ReferenceActiveAffinePositiveTest.upDiagnosticPositive] at h
    simpa [heligible] using h
  have hbankCurrent : d.input.upDecoderBank i = current.input.state.upDecoderBank i := by
    calc
      d.input.upDecoderBank i = r.input.state.upDecoderBank i := congrFun hbank i
      _ = current.input.state.upDecoderBank i := by rw [← hcurrent]
  have hbatch : (current.input.state.upDecoderBank i).pending ++
      [AffineBatchDecoder.entry p
        (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time] = W := by
    calc
      _ = ReferenceCollectionUpFailureReadoutV2.appendedUp rate d := by
        simp only [ReferenceCollectionUpFailureReadoutV2.appendedUp, hbankCurrent, hdi,
          AffineBatchDecoder.positiveAt, CoordinatorUpReception.traceAt, heligible]
        rfl
      _ = W := happended
  have hspec := ReferenceCollectionUpFailureReadoutV2.completedUpBatch_spec rate r i W hcompleted
  have hquota : (current.input.state.upDecoderBank i).pending.length + 1 =
      AffineBatchDecoder.quota p := by
    calc
      _ = ((current.input.state.upDecoderBank i).pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]).length := by
              simp
      _ = W.length := congrArg List.length hbatch
      _ = AffineBatchDecoder.quota p := hspec.1
  have hword : ReferenceCollectionUpFailureReadoutV2.enc rate U = ActiveFollowerArmChoice.offeredUpWord rate.eta U := by
    dsimp [ReferenceCollectionUpFailureReadoutV2.enc, ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord,
      ActiveFollowerArmChoice.offeredUpWord]
    have hcodec := ReferenceUpReception.ledgerCodecParams_eq_followerCodecParams rate
    cases hcodec
    rfl
  have hbeta : ∀ e ∈ W, max a.val s ≤ e.time.val := by
    intro e he
    obtain ⟨hae, _, _, ⟨re, hentryLookup, _, _⟩⟩ := hentries e he
    have hstart := actualLookup_start_le (rate := rate) rewards C_star C_h
      e.time z _ hentryLookup
    have hse : s ≤ e.time.val := by
      simpa [s, ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput] using hstart
    omega
  let beta := max a.val s
  have hbetaT : beta ≤ t.val := by dsimp [beta]; omega
  have hawaited : ∃ (message : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta)) (beta : ℕ),
      ReferenceGeneratedUpAwaitedBatchCoverage.awaited_up_source_trace
        (rate := rate) rewards C_star C_h q t s hs control0 i launchSource beta message ∧
      ∀ entry ∈ (current.input.state.upDecoderBank i).pending ++
        [AffineBatchDecoder.entry p
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time],
        beta ≤ entry.time.val := by
    refine ⟨U, beta, ?_, ?_⟩
    · refine ⟨by dsimp [beta]; exact Nat.le_max_right _ _, hbetaT, ?_⟩
      intro record hrecord hrecordBeta hrecordT hrecordChannel
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hrecord
      obtain ⟨hklt, hget⟩ := List.getElem?_eq_some_iff.mp hk
      have hkFin : k < p.T - s := by
        simpa only [ReferenceActiveHorizonMeasurability.runOfInput,
          ReferenceActivePhysicalHorizon.run_record_count] using hklt
      let j : Fin (p.T - s) := ⟨k, hkFin⟩
      have hfullRecord := ReferenceLocalReleaseGateChronology.run_record_at
        input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s input.property
        (p.T - s) (by omega) j
      have hrecordEq : record =
          ReferenceAssignmentPayloadChronology.actualRunRecordAt input.val.1 input.val.2.1
            input.val.2.2.1 input.val.2.2.2 s k (by omega) input.property := by
        calc
          record = (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s)
              (by omega) input).records[k]'(by
                have hlen := ReferenceActivePhysicalHorizon.run_record_count input.val.1
                  input.val.2.1 input.val.2.2.1 input.val.2.2.2 s (p.T - s)
                  (by omega) input.property
                omega) := by exact hget.symm
          _ = _ := hfullRecord
      have htimeIndex : record.input.time.val = s + k := by
        rw [hrecordEq]
        simp [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
          ReferenceActivePhysicalHorizon.roundInputAt]
      have hsRecord : s ≤ record.input.time.val := by omega
      let v : Fin p.T := record.input.time
      have hsourceChannel : ReferenceSelectedAffinePairLaw.selectedChannel p
          ((z.1.2 q).2 v).1 = some (1, i) := by
        have hrunFields := ReferenceActivePhysicalHorizon.run_record_inputs input.val.1
          input.val.2.1 input.val.2.2.1 input.val.2.2.2 s (p.T - s) (by omega)
          input.property record hrecord
        simpa [v, ReferenceActivePhysicalStep.RoundInput.row,
          hrunFields.1, hrunFields.2.1, hinputRows, hinputSelected] using hrecordChannel
      obtain ⟨actual, hactual, haw⟩ := hinterval v
        (Nat.le_trans (Nat.le_max_left _ _) hrecordBeta)
        (by simpa [v] using hrecordT) hsourceChannel
      have hlookupActual := sourceRun_lookup (rate := rate) rewards C_star C_h
        q t s hs control0 i launchSource v hsRecord
      have hindexEq : v.val - s = k := by simpa [v] using (by omega : record.input.time.val - s = k)
      have hlookupRecord : ReferenceCollectionUpFailureReadoutV2.lookup rate rewards C_star C_h v z = some record := by
        change ReferenceCollectionUpFailureReadoutV2.lookup rate rewards C_star C_h v z = _
          at hlookupActual
        have hrecordEq' : record =
            ReferenceAssignmentPayloadChronology.actualRunRecordAt input.val.1 input.val.2.1
              input.val.2.2.1 input.val.2.2.2 s (v.val - s) (by omega) input.property := by
          simpa only [← hindexEq] using hrecordEq
        rw [← hrecordEq'] at hlookupActual
        exact hlookupActual
      have hactualEq : actual = record := Option.some.inj (hactual.symm.trans hlookupRecord)
      subst actual
      rcases haw with ⟨diag, hdiag, hdi', hcheck', hgate', hexpected, haccept⟩
      have hsent : ReferenceActiveAffinePositiveTest.upSent record.input =
          some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
        calc
          _ = diag.expected := (ReferenceGeneratedUpBatchPrefixEvent.actualRecordUpDiagnostic_expected
            record diag hdiag).symm
          _ = some (ReferenceCollectionUpFailureReadoutV2.enc rate U) := hexpected
          _ = _ := congrArg some hword
      have hselectedRound : (CoordinatorUpReception.roundInput diag.input).selected = true :=
        (CoordinatorUpReception.roundInput_selected_iff_gate diag.input).mpr hgate'
      have hreceiverRound : (CoordinatorUpReception.roundInput diag.input).receiverEnabled = true := by
        rfl
      exact ⟨hsent, diag, hdiag, hdi', hselectedRound, hreceiverRound, haccept⟩
    · intro entry hentry
      exact hbeta entry (by simpa only [hbatch] using hentry)
  have hambiguity : ∃ v₁ v₂ : AffineChannelLaw.Word (AffineBatchDecoder.width p),
      v₁ ≠ v₂ ∧
      AffineBatchDecoder.satisfies
        (((current.input.state.upDecoderBank i).pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]).map
          AffineBatchDecoder.Entry.sample) v₁ ∧
      AffineBatchDecoder.satisfies
        (((current.input.state.upDecoderBank i).pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]).map
          AffineBatchDecoder.Entry.sample) v₂ := by
    rcases (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff W).mp hmulti with
      ⟨v₁, v₂, hv₁, hv₂, hne⟩
    exact ⟨v₁, v₂, hne, by simpa [hbatch, AffineBatchDecoder.samples] using hv₁,
      by simpa [hbatch, AffineBatchDecoder.samples] using hv₂⟩
  simp only [ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEvent, Set.mem_ofPred_eq]
  refine ⟨q, t, s, hs, i, hbranch, d, ?_, ?_, hpCurrent, hquota, hawaited, hambiguity⟩
  · simpa only [current] using hdCurrent
  · exact hdi

/-- The finite union over detecting dates is Borel in the original source
space. -/
theorem fixedAwaitedUpFailureEvent_borel :
    MeasurableSet (fixedAwaitedUpFailureEvent rate rewards C_star C_h) := by
  change MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
    ∃ t : Fin p.T, ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt rate rewards C_star C_h z t}
  rw [show {z : BootstrapPrivateRoundStreams.SourceInput p |
      ∃ t : Fin p.T, ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt rate rewards C_star C_h z t} =
      ⋃ t : Fin p.T, {z | ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt rate rewards C_star C_h z t} by
    ext z
    simp]
  exact MeasurableSet.iUnion fun t => ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt_borel
    rate rewards C_star C_h t

/-- Every calendar witness lies in the same-source UP awaited ambiguity
envelope. -/
theorem fixedAwaitedUpFailureEvent_subset_upAwaitedAmbiguityEvent
    (control0 : ContinuousLearningRows.TimeControl p) :
    fixedAwaitedUpFailureEvent rate rewards C_star C_h ⊆
      ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEvent (rate := rate) rewards C_star C_h control0 := by
  intro z hz
  change ∃ t : Fin p.T, ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt rate rewards C_star C_h z t at hz
  obtain ⟨t, hfail⟩ := hz
  exact fixedAwaitedUpFailureAt_mem_upAwaitedAmbiguityEvent
    rate rewards C_star C_h control0 z t hfail

/-- The original-source probability of the literal finite-calendar UP
failure event is bounded by the all-J awaited ambiguity tail once. -/
theorem fixedAwaitedUpFailureEvent_measureReal_bound
    (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
      (fixedAwaitedUpFailureEvent rate rewards C_star C_h) ≤
        1 / (4 * (N p : ℝ) ^ 2) := by
  apply le_trans (measureReal_mono
    (fixedAwaitedUpFailureEvent_subset_upAwaitedAmbiguityEvent
      rate rewards C_star C_h control0))
  exact ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEvent_measureReal_le
    (rate := rate) rewards C_star C_h control0

end Bandits.Support.ReferenceAwaitedUpDecoderErrorProbability

end
