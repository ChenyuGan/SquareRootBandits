/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpSourceCalendar

/-!
# Actual wrong-local UP diagnostic and reference rejection

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,139-145`,
`sources/zip4/manuscript/05_binary_transport.tex:29-45`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,277-284`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module keeps the actual raw, locally accepted but wrong UP diagnostic and
composes it with the reference-only receiver filter. It proves the actual
receiver rejects that word while preserving the decoder update, even if a
later physical finish fails. It does not prove that the wrong word was absent
from every earlier test in its batch.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceGeneratedUpBatchPrefixEvent
open Bandits.Support.ReferenceGeneratedUpPrefixPositiveHalf
open Bandits.Support.ReferenceGeneratedUpSourceCalendar
open Bandits.Support.ReferenceCoordinatorUpDecoderReplay
open Bandits.Support.ReferenceCoordinatorUpPhysicalCall
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.ReferenceUpReception
open Bandits.Support.ReferenceUpDecoderBankInvariant
open Bandits.Support.ReferenceGeneratedUpBatchCalendar
open Bandits.Support.ReferenceGeneratedAffineHashHalf
open Bandits.Support.AffineBatchDecoder

namespace Bandits.Support.ReferenceGeneratedUpFalseDiagnosticCut

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
variable {p : Parameters} {rate : RateInput p}

/-- An actual UP diagnostic that is locally accepted before the reference-only
expected-word filter, but whose raw word differs from the current offer, is
rejected by the same physical receiver. The actual parser record and its local
acceptance are retained before filtering. The source run, current record,
decoder bank, and site ledger are all computed from the original launch input.
-/
theorem actual_wrong_local_up_rejected
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).output.coordinator.up = some d)
    (hi : d.input.selectedFollower = i)
    (v : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hv : d.raw = some v)
    (hl : d.locallyAccepted = true)
    (hw : some v ≠ d.expected) :
    ∃ (L : ReferenceActivePhysicalStep.Ledger rate)
      (M : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)),
      ReferenceCoordinatorUpPhysicalCall.siteLedger?
          (x := (originalSourceCurrentRecord (rate := rate)
            rewards C_star C_h q t s hs control0 i z).input) = some L ∧
      CoordinatorUpReception.receptionInputCheck
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput
            (originalSourceCurrentRecord (rate := rate)
              rewards C_star C_h q t s hs control0 i z).input L) = true ∧
      d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput
          (originalSourceCurrentRecord (rate := rate)
            rewards C_star C_h q t s hs control0 i z).input L ∧
      d.parsed = some M ∧
      ReferenceUpReception.rawParsedOutput rate d.input = some M ∧
      CoordinatorCollectionLedger.acceptUpCheck L i M = true ∧
      ReferenceActiveAffinePositiveTest.upPositive
          (originalSourceCurrentRecord (rate := rate)
            rewards C_star C_h q t s hs control0 i z).input = true ∧
      ((originalSourceCurrentRecord (rate := rate)
          rewards C_star C_h q t s hs control0 i z).input.state.upDecoderBank i).pending.length + 1 =
        AffineBatchDecoder.quota p ∧
      ReferenceUpReception.filterRawByExpected d.raw d.expected = none ∧
      CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
          (ReferenceUpReception.filterRawByExpected
            (CoordinatorUpReception.decoderTransition
              (ReferenceCoordinatorUpPhysicalCall.actualUpInput
                (originalSourceCurrentRecord (rate := rate)
                  rewards C_star C_h q t s hs control0 i z).input L)).2
            (ReferenceActivePhysicalStep.upExpected
              (ReferenceActivePhysicalStep.prepare
                (originalSourceCurrentRecord (rate := rate)
                  rewards C_star C_h q t s hs control0 i z).input))) =
        (none : Option (OrdinaryMessageCodec.UpRecord
          (CoordinatorCollectionLedger.codecParams p rate.eta.val))) ∧
      (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare
            (originalSourceCurrentRecord (rate := rate)
              rewards C_star C_h q t s hs control0 i z).input) L).result =
        .rejected ({L with phase := CoordinatorCollectionLedger.Phase.decoded},
          CoordinatorUpReception.decoderBankAfter d.input) ∧
      (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q t s hs control0 i z).output.next.upDecoderBank =
          CoordinatorUpReception.decoderBankAfter d.input := by
  let r := originalSourceCurrentRecord (rate := rate)
    rewards C_star C_h q t s hs control0 i z
  let input := originalSourceRunInput (rate := rate)
    rewards C_star C_h q t s hs control0 i z
  let prior := ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s)
    (by omega) input
  let launch := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
  let control := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1
  let fields := ReferenceGeneratedUpBatchCalendar.retained_launch_start_fields
    rate rewards C_star C_h q t s hs control0 launch
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s launch.1 fields.1 control0 control).mp fields.2
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control launch.1
  let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart
  let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart).2.1
  let generatedPrior := ReferenceActivePhysicalHorizon.run active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (t.val - s)
    (by omega) hmode

  have hchronology := ReferenceGeneratedUpBatchCalendar.original_source_up_branch_prefix_bank_chronology
    rate rewards C_star C_h q t i s hs control0 z control (t.val - s) (by omega)
  have hpriorInvariant : ReferenceUpDecoderBankInvariant.upBankInvariant prior.finalState := by
    have hbridge := ReferenceGeneratedUpResetPrefixBridge.original_source_run_eq_generated
      rate rewards C_star C_h q t s hs control0 i z (t.val - s) (by omega)
    have hfinal := hbridge.2.2.2.2
    have hgenerated : ReferenceUpDecoderBankInvariant.upBankInvariant generatedPrior.finalState := by
      change ReferenceUpDecoderBankInvariant.upBankInvariant
        (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (t.val - s)
          (by omega) hmode).finalState
      exact hchronology.1
    have hpriorEq : prior.finalState = generatedPrior.finalState := by
      simpa [prior, generatedPrior, ReferenceActiveHorizonMeasurability.runOfInput,
        input, active, source, hmode] using hfinal
    rw [hpriorEq]
    exact hgenerated

  have hstate : r.input.state = prior.finalState := by
    rfl
  have hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant r.input.state := by
    rw [hstate]
    exact hpriorInvariant

  obtain ⟨L, hsite, hcheck, hinput, hafter, hraw, hparsed, hlocal, _, hexpected,
      _, hbank, _, _⟩ := ReferenceGeneratedUpBatchCalendar.record_up_executed_fields r d hd

  have hsmall : (d.input.upDecoderBank i).pending.length < AffineBatchDecoder.quota p := by
    change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
      r.input.state.coordinator r.input.state.upDecoderBank at hinvariant
    have hwellFormed := hinvariant.1 i
    rw [← hbank] at hwellFormed
    exact hwellFormed.1

  let trace := CoordinatorUpReception.traceAt d.input
  have hstepOutput : AffineBatchDecoder.stepOutput p trace
      (d.input.upDecoderBank i) d.input.time = some v := by
    have htransition : (CoordinatorUpReception.decoderTransition d.input).2 = some v :=
      hraw.symm.trans hv
    simpa [trace, hi, CoordinatorUpReception.decoderTransition,
      CoordinatorUpReception.traceAt,
      AffineBatchDecoder.decodeStep] using htransition
  have hdecoded := (AffineBatchDecoder.stepOutput_eq_some_iff p trace
    (d.input.upDecoderBank i) d.input.time v).mp hstepOutput
  have heligible : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) := by
    by_contra hnot
    have hnotTrace : ¬ AffineBatchDecoder.eligible (trace d.input.time) := by
      simpa [trace, CoordinatorUpReception.traceAt] using hnot
    have hnone : AffineBatchDecoder.positiveAt p trace d.input.time = [] := by
      simp [AffineBatchDecoder.positiveAt, hnotTrace]
    have hlength : ((d.input.upDecoderBank i).pending ++
        AffineBatchDecoder.positiveAt p trace d.input.time).length =
        (d.input.upDecoderBank i).pending.length := by
      rw [hnone, List.append_nil]
    omega
  have hquota : (d.input.upDecoderBank i).pending.length + 1 = AffineBatchDecoder.quota p := by
    have heligibleTrace : AffineBatchDecoder.eligible (trace d.input.time) := by
      simpa [trace, CoordinatorUpReception.traceAt] using heligible
    have hle : AffineBatchDecoder.quota p ≤
        (d.input.upDecoderBank i).pending.length + 1 := by
      simpa [AffineBatchDecoder.positiveAt, heligibleTrace] using hdecoded.1
    omega
  have hupPositive : ReferenceActiveAffinePositiveTest.upPositive r.input = true := by
    rw [ReferenceActiveAffinePositiveTest.record_upPositive r, hd]
    simp [ReferenceActiveAffinePositiveTest.upDiagnosticPositive, heligible]
  have hpositive : ReferenceGeneratedAffineHashHalf.directionPositive 1 r.input = true := by
    simpa [ReferenceGeneratedAffineHashHalf.directionPositive] using hupPositive

  have hparsedLocal : ReferenceUpReception.rawParsedLocalAcceptance rate d.input = true := by
    rw [← hlocal]
    exact hl
  obtain ⟨M, hMParsed, hAccept⟩ :=
    (ReferenceUpReception.rawParsedLocalAcceptance_eq_true_iff rate d.input).mp hparsedLocal
  have hledger : d.input.ledger = L := by
    simpa [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs, ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtControl] using
      congrArg (fun x => x.ledger) hinput
  have haccept : CoordinatorCollectionLedger.acceptUpCheck L i M = true := by
    simpa [hledger, hi] using hAccept
  have hdiagParsed : d.parsed = some M := hparsed.trans hMParsed

  have hexpected' : d.expected = ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare r.input) := by
    calc
      d.expected = ReferenceGeneratedAffineHashHalf.directionSent 1 r.input := hexpected
      _ = ReferenceActiveAffinePositiveTest.upSent r.input := by
        simp [ReferenceGeneratedAffineHashHalf.directionSent]
      _ = ReferenceActivePhysicalStep.upExpected
          (ReferenceActivePhysicalStep.prepare r.input) := rfl
  have hmismatch : (CoordinatorUpReception.decoderTransition d.input).2 ≠
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) := by
    intro heq
    apply hw
    calc
      some v = d.raw := hv.symm
      _ = (CoordinatorUpReception.decoderTransition d.input).2 := hraw
      _ = ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) := heq
      _ = d.expected := hexpected'.symm

  have hfilter : ReferenceUpReception.filterRawByExpected d.raw d.expected = none :=
    ReferenceUpReception.filterRawByExpected_eq_none_of_ne d.raw d.expected
      (fun heq => hw (hv.symm.trans heq))
  have hfilteredInput : ReferenceUpReception.filterRawByExpected
      (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L)).2
      (ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare r.input)) = none := by
    have heq : (CoordinatorUpReception.decoderTransition d.input).2 = d.raw ∧
        ReferenceActivePhysicalStep.upExpected
          (ReferenceActivePhysicalStep.prepare r.input) = d.expected :=
      ⟨hraw.symm, hexpected'.symm⟩
    calc
      _ = ReferenceUpReception.filterRawByExpected
          (CoordinatorUpReception.decoderTransition d.input).2
          (ReferenceActivePhysicalStep.upExpected
            (ReferenceActivePhysicalStep.prepare r.input)) := by
        rw [← hinput]
      _ = ReferenceUpReception.filterRawByExpected d.raw d.expected := by
        congr 1
        · exact heq.1
        · exact heq.2
      _ = none := hfilter
  have hfilteredParsed : CoordinatorUpReception.parseDecoderOutput
      (p := p) (eta := rate.eta.val)
      (ReferenceUpReception.filterRawByExpected
        (CoordinatorUpReception.decoderTransition
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L)).2
        (ReferenceActivePhysicalStep.upExpected
          (ReferenceActivePhysicalStep.prepare r.input))) =
        (none : Option (OrdinaryMessageCodec.UpRecord
          (CoordinatorCollectionLedger.codecParams p rate.eta.val))) := by
    rw [hfilteredInput]
    rfl

  have hreject : (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare r.input) L).result =
        .rejected ({L with phase := CoordinatorCollectionLedger.Phase.decoded},
          CoordinatorUpReception.decoderBankAfter d.input) := by
    have hmisInput : (CoordinatorUpReception.decoderTransition
        (ReferenceUpReception.receptionInputAtRow rate r.input.row
          (ReferenceActivePhysicalStep.upInputs
            (ReferenceActivePhysicalStep.prepare r.input) L) r.input.time)).2 ≠
          ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) := by
      simpa [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
        ReferenceActivePhysicalStep.upInputs, hinput] using hmismatch
    have h := ReferenceActivePhysicalStep.receiveUp_mismatch
      (ReferenceActivePhysicalStep.prepare r.input) L hcheck hmisInput
    simpa [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs, hinput] using h

  rcases ReferenceCoordinatorUpPhysicalCall.record_up_commit_cases r d hd hinvariant with
    ⟨L', hsite', _, _, _, hbranches⟩
  have hL : L' = L := Option.some.inj (hsite'.symm.trans hsite)
  subst L'
  have hnextBank : r.output.next.upDecoderBank = CoordinatorUpReception.decoderBankAfter d.input := by
    rcases hbranches with hinvalid | ⟨out, hresult, houtbank, hnext⟩
    · rw [hreject] at hinvalid
      cases hinvalid.1
    · rcases hresult with hsuccess | hrejected
      · rw [hreject] at hsuccess
        cases hsuccess
      · rw [hreject] at hrejected
        cases hrejected
        simpa using hnext.trans houtbank

  exact ⟨L, M, hsite, hcheck, hinput, hdiagParsed, hMParsed, haccept,
    hupPositive, by simpa [hbank] using hquota, hfilter, hfilteredParsed,
    hreject, hnextBank⟩

end Bandits.Support.ReferenceGeneratedUpFalseDiagnosticCut

end
