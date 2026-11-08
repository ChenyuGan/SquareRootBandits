/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedSelectedAssignmentOrder

/-!
# Earlier DOWN words and selected assignment successors

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:100-106`,
`sources/zip4/manuscript/05_binary_transport.tex:60-88,95-103`,
`sources/zip4/manuscript/06_interruptions.tex:41-70,270-295,327-348`,
`sources/zip4/manuscript/07_public_setup.tex:129-162`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

An earlier actually sent wrong word cannot cross a strict selected assignment
successor. This conditional boundary uses the actual original generated run;
it does not cover same-assignment live pending erasure, no-selection failures,
all decoder tests, or the manuscript regret conclusion.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceGeneratedDownBatchCalendar
open ReferenceGeneratedInheritedDownWrongCompletionWitness

namespace Bandits.Support.ReferenceGeneratedSelectedSuccessorStaleCut

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem actual_wrong_cut_parse_of_raw
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hcut : (record.output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut)
    (hraw : cut.raw = some word) :
    cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate (some word) := by
  obtain ⟨_choice, _memory, logged, _hconfiguration, _hunoccupied, _hlogging,
      hlogged, _hcutFromChoice⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice
      record i cut hcut
  have hcutActual :=
    ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
      record i logged cut hlogged hcut
  have hwrong' := hwrong
  have hraw' := hraw
  rw [hcutActual] at hwrong' hraw'
  have hfalse := hwrong'.1
  let view := record.output.preparation.coordinator.downView
  let row := record.input.row
  let time := record.input.time
  let observation := ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i
  have hselected : ActiveFollowerDownAcceptance.downSelected p i row time := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, row, time, hnot]
      at hfalse
  have hstatus : logged.status = .unoccupied := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, row, time,
      hselected, hnot] at hfalse
  have hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate logged := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, row, time,
      hselected, hstatus, hnot] at hfalse
  have hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, row, time,
      hselected, hstatus, hregisters, hnot] at hfalse
  have hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, row, time,
      hselected, hstatus, hregisters, hbatch, hnot] at hfalse
  have hmatches :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate logged).2 ≠
        ReferenceDownReception.expectedDownFlatWord view i row time := by
    intro hmatch
    simp [ReferenceDownReception.referenceDownCut, view, row, time, observation,
      hselected, hstatus, hregisters, hbatch, hbuffer, hmatch] at hfalse
  have hdecoded :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate logged).2 =
        some word := by
    simpa [ReferenceDownReception.referenceDownCut, view, row, time, observation,
      hselected, hstatus, hregisters, hbatch, hbuffer, hmatches] using hraw'
  have hwordMismatch :
      (some word : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) ≠
        ReferenceDownReception.expectedDownFlatWord view i row time := by
    intro hmatch
    apply hmatches
    rw [hdecoded]
    exact hmatch
  have hparse :
      (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).ordinaryParse =
        ReferenceDownReception.ordinaryParse p rate (some word) := by
    simp [ReferenceDownReception.referenceDownCut, view, row, time, observation,
      hselected, hstatus, hregisters, hbatch, hbuffer, hdecoded, hwordMismatch]
  rw [hcutActual]
  simpa [view, row, time, observation] using hparse

local notation "R" =>
  ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt

/-- If an earlier selected DOWN sender supplied the raw word of a current
wrong unique accepted cut, then the two selected rounds carry the same whole
assignment payload. A strict successor would force an accepted ordinary UP
start at the successor ledger sigma, while the current ordinary DOWN parser
requires its start to be strictly smaller than that same sigma. -/
theorem generated_earlier_sent_wrong_cut_same_selected_payload
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((R rate rewards C_star C_h s hs x n).output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut)
    (k : Fin (p.T - s)) (hkn : k.val < n.val)
    (old : Selection (R rate rewards C_star C_h s hs x k).input)
    (now : Selection (R rate rewards C_star C_h s hs x n).input)
    (hold : (R rate rewards C_star C_h s hs x k).output.preparation.coordinator.selection = some old)
    (hnow : (R rate rewards C_star C_h s hs x n).output.preparation.coordinator.selection = some now)
    (oldCut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (holdCut : ((R rate rewards C_star C_h s hs x k).output.followers i).down = some oldCut)
    (hsent : oldCut.expectedWord = cut.raw) :
    old.view.payload = now.view.payload := by
  classical
  cases hraw : cut.raw with
  | none => exact False.elim (hwrong.2.1 hraw)
  | some word =>
    have hexpected : oldCut.expectedWord = some word := by
      rw [hsent, hraw]
    obtain ⟨oldSelected, holdSelected, _hsender, hword, hparseOld, _hencode⟩ :=
      ReferenceGeneratedInheritedDownCandidateOrigin.actual_expectedDownWord_origin
        (R rate rewards C_star C_h s hs x k) i oldCut word holdCut hexpected
    have hselectedEq : oldSelected = old := Option.some.inj
      (holdSelected.symm.trans hold)
    subst oldSelected
    have hparseCurrent :
        cut.ordinaryParse =
          some (old.view.payload.downRecord i) := by
      calc
        cut.ordinaryParse =
            ReferenceDownReception.ordinaryParse p rate (some word) :=
          actual_wrong_cut_parse_of_raw (R rate rewards C_star C_h s hs x n)
            i cut word hcut hwrong hraw
        _ = some (old.view.payload.downRecord i) := hparseOld

    have horder :=
      ReferenceGeneratedSelectedAssignmentOrder.generated_selected_assignment_first_intervening_installation
        rate rewards C_star C_h s hs x i n k hkn old now hold hnow
    rcases horder with hequal | ⟨hstrict, a, ledger, proposal, hka, han,
        hlater, hstate, hledgerSigma, hempty, hbound, _hminimal⟩
    · exact hequal
    · obtain ⟨currentState, currentMemory, hcurrentChoice, _hcurrentUnoccupied,
        hcurrentStrict⟩ :=
        ReferenceFirstLiveRawDownExclusion.retained_raw_down_parse_acceptance_actual_choice
          (R rate rewards C_star C_h s hs x n) i cut (old.view.payload.downRecord i)
          hcut hparseCurrent hwrong.2.2

      let seed := generatedSourceSeed rate rewards C_star C_h s hs x
      let rows := x.val.1.2
      let selected := ActualInitializationPhysicalStep.selectedRowIndex p x.val
      let full := ReferenceActivePhysicalHorizon.run seed rows selected rewards s
        (p.T - s) (by omega)
        (generatedSourceSeed_spec rate rewards C_star C_h s hs x).2.1
      let prefixRun := ReferenceActivePhysicalHorizon.run seed rows selected rewards s
        a.val (by omega) (generatedSourceSeed_spec rate rewards C_star C_h s hs x).2.1
      have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s :=
        (generatedSourceSeed_spec rate rewards C_star C_h s hs x).2.1
      have hfullLength : full.records.length = p.T - s := by
        exact ReferenceActivePhysicalHorizon.run_record_count seed rows selected rewards s
          (p.T - s) (by omega) hmode
      have hprefixLength : prefixRun.records.length = a.val := by
        exact ReferenceActivePhysicalHorizon.run_record_count seed rows selected rewards s
          a.val (by omega) hmode
      obtain ⟨suffix, hrecords⟩ :=
        ReferenceCollectionPhaseHistory.run_records_prefix seed rows selected rewards s
          a.val (p.T - s - a.val) (by omega) hmode
      have hfullPrefix : full.records = prefixRun.records ++ suffix := by
        simpa [full, prefixRun] using hrecords
      have hfullAt (j : ℕ) (hj : j < a.val) :
          full.records[j]'(by rw [hfullLength]; omega) =
            prefixRun.records[j]'(by rw [hprefixLength]; omega) := by
        have hjAppend : j < (prefixRun.records ++ suffix).length := by
          rw [List.length_append, hprefixLength]
          omega
        calc
          full.records[j]'(by rw [hfullLength]; omega) =
              (prefixRun.records ++ suffix)[j]'hjAppend :=
            (List.getElem_of_eq hfullPrefix.symm hjAppend).symm
          _ = prefixRun.records[j]'(by rw [hprefixLength]; omega) :=
            (List.getElem_append_left' (l₁ := prefixRun.records) (i := j)
              (by rw [hprefixLength]; exact hj) suffix).symm

      have hseedSpec := generatedSourceSeed_spec rate rewards C_star C_h s hs x
      obtain ⟨launchState, hlaunch, hseedFields⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
          rate x.val rewards C_star C_h x.property.1
      have hlaunchSeed : launchState = seed :=
        Option.some.inj (hlaunch.symm.trans hseedSpec.1)
      have hfirstCoordinator : seed.coordinator = .first := by
        obtain ⟨firstState, ⟨hfirstLaunch, hfirstCoord, _hbank, _hacts, _hfollowers⟩,
          _hunique⟩ :=
          ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
            rate x.val rewards C_star C_h x.property.1
        have hfirstSeed : firstState = seed :=
          Option.some.inj (hfirstLaunch.symm.trans hseedSpec.1)
        rw [← hfirstSeed]
        exact hfirstCoord
      have hseedFollowers : ∀ f : Fin (p.m - 1),
          ∃ first firstMemory,
            seed.followers f = .ordinary first firstMemory ∧ first.lastDown = none := by
        intro f
        dsimp only at hseedFields
        obtain ⟨hfields, hlast, _hstart, _hscore, _hdelta, _hqueue, _hstatus,
          _hdomain⟩ := hseedFields f
        exact ⟨ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate))
            (ActualReferenceInitializationBlock.refFollower f),
          ActiveFollowerLifecycle.initialMemory p,
          by simpa [hlaunchSeed] using hfields, hlast⟩

      have hinput : (R rate rewards C_star C_h s hs x a).input =
          ReferenceCollectionPhaseHistory.nextInput seed rows selected rewards s a.val
            (by omega) hmode := by
        rfl
      have hlaterAt : ReferenceCollectionPhaseHistory.laterChosen
          (ReferenceCollectionPhaseHistory.nextInput seed rows selected rewards s a.val
            (by omega) hmode) = true := by
        rw [← hinput]
        exact hlater
      have hlaterSpan : s + (a.val + 1) ≤ p.T := by omega
      have hlaterHistory :=
        ReferenceAcceptedUpFollowerHistory.run_laterStart_prior_down
          seed rows selected rewards s a.val hlaterSpan hmode hfirstCoordinator
          hseedFollowers hlaterAt
      rcases hlaterHistory with ⟨before, cutoff, during, installedPayload, oldLedger,
        oldProposal, hprefixHistory, _hcutoffChosen, hcoordinator, _hempty, _hwindow,
        _heach⟩
      have hsourceUp := ReferenceCollectionPhaseHistory.run_laterStart_all_up_accepted
        seed rows selected rewards s a.val hlaterSpan hmode hfirstCoordinator hlaterAt
      rcases hsourceUp with ⟨_beforeUp, _cutoffUp, _duringUp, installedPayloadUp,
        oldLedgerUp, oldProposalUp, _hrecordsUp, _hcutoffUp, hcoordinatorUp, _hemptyUp,
        _hwindowUp, heachUp⟩
      obtain ⟨upIndex, upRecord, message, _hbefore, hupIndex, hupGet?, haccepted,
        hmessageSigma⟩ := heachUp i

      have hupFullIndex : upIndex < full.records.length := by
        rw [hfullLength]
        omega
      have hupPrefixIndex : upIndex < prefixRun.records.length := by
        rw [hprefixLength]
        exact hupIndex
      have hupFullRecord : full.records[upIndex]'hupFullIndex = upRecord := by
        have hsome := List.getElem?_eq_getElem (l := prefixRun.records)
          (i := upIndex) hupPrefixIndex
        rw [hupGet?] at hsome
        calc
          full.records[upIndex]'hupFullIndex =
              prefixRun.records[upIndex]'hupPrefixIndex := hfullAt upIndex hupIndex
          _ = upRecord := Option.some.inj hsome.symm
      have hacceptedFull : ReferenceCollectionPhaseHistory.AcceptedUp
          (full.records[upIndex]'hupFullIndex).input i message := by
        rw [hupFullRecord]
        exact haccepted
      obtain ⟨first, firstMemory, hfirstFollower⟩ := hseedFollowers i
      let prefixIndex : Fin prefixRun.records.length := ⟨upIndex, hupPrefixIndex⟩
      have hacceptedPrefix : ReferenceCollectionPhaseHistory.AcceptedUp
          (prefixRun.records[prefixIndex.val].input) i message := by
        have hrecord : prefixRun.records[prefixIndex.val] = upRecord := by
          have hsome := List.getElem?_eq_getElem (l := prefixRun.records)
            (i := prefixIndex.val) hupPrefixIndex
          rw [hupGet?] at hsome
          exact Option.some.inj hsome.symm
        rw [hrecord]
        exact haccepted
      have hacceptedPriorDown :=
        ReferenceAcceptedUpFollowerHistory.run_acceptedUp_prior_down
          seed rows selected rewards s a.val (by omega) hmode i first firstMemory
          hfirstFollower.1 hfirstFollower.2 prefixIndex message hacceptedPrefix
      dsimp only [prefixIndex] at hacceptedPriorDown
      have hprefixValue : prefixIndex.val = upIndex := rfl
      obtain ⟨downIndex, hdownBeforeUp, priorDown, hpriorRetained, hpriorApplied,
        hpriorSigma, upSender, upState, upMemory, hsenderChoice, hupConfiguration,
        _hupUnoccupied, _hoff, hstart, _hstarted, _hS, _hdelta, _hbacklog,
        _hlastDown, hpriorMessageSigma, _hpositive⟩ := hacceptedPriorDown
      obtain ⟨acceptedSender, acceptedState, acceptedMemory, hacceptedSender,
          hacceptedIndex, hacceptedConfiguration, _hacceptedUnoccupied, _hoff,
          hacceptedStart, _hacceptedStarted, _hacceptedS, _hacceptedDelta,
          _hacceptedBacklog, _hacceptedPrior, _hacceptedPositive, _hslot⟩ :=
        ReferenceAcceptedUpFollowerHistory.acceptedUp_current_choice hacceptedFull
      have hacceptedSenderChoice : acceptedSender =
          ReferenceFollowerFixedReply.actualChoice (full.records[upIndex]'hupFullIndex) i := by
        unfold ReferenceFollowerFixedReply.actualChoice
        rw [(full.records[upIndex]'hupFullIndex).output_eq]
        simpa [← hacceptedIndex, ReferenceActivePhysicalStep.step] using hacceptedSender
      have hsenderFull : upSender =
          ReferenceFollowerFixedReply.actualChoice (full.records[upIndex]'hupFullIndex) i := by
        have hprefixRecord : prefixRun.records[prefixIndex.val] = upRecord := by
          have hsome := List.getElem?_eq_getElem (l := prefixRun.records)
            (i := upIndex) hupPrefixIndex
          rw [hupGet?] at hsome
          exact Option.some.inj hsome.symm
        calc
          upSender = ReferenceFollowerFixedReply.actualChoice
              (prefixRun.records[prefixIndex.val]) i := hsenderChoice
          _ = ReferenceFollowerFixedReply.actualChoice upRecord i := by rw [hprefixRecord]
          _ = ReferenceFollowerFixedReply.actualChoice
              (full.records[upIndex]'hupFullIndex) i := by rw [← hupFullRecord]
      have hacceptedLocal : acceptedState = upState := by
        have hconfig :
            (DeclaredFollowerLocalRound.LocalConfiguration.ordinary acceptedState
              acceptedMemory) =
              .ordinary upState upMemory := by
          calc
            .ordinary acceptedState acceptedMemory = acceptedSender.configuration :=
              hacceptedConfiguration.symm
            _ = (ReferenceFollowerFixedReply.actualChoice
                (full.records[upIndex]'hupFullIndex) i).configuration := by
              rw [hacceptedSenderChoice]
            _ = upSender.configuration := by rw [hsenderFull]
            _ = .ordinary upState upMemory := hupConfiguration
        exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hconfig).1
      have hmessageStart : message.val.sigma =
          ReferencePrelaunchFollower.acceptedStart upState := by
        calc
          message.val.sigma = ReferencePrelaunchFollower.acceptedStart acceptedState :=
            hacceptedStart
          _ = ReferencePrelaunchFollower.acceptedStart upState :=
            congrArg ReferencePrelaunchFollower.acceptedStart hacceptedLocal

      have hdownFullIndex : downIndex.val < full.records.length := by
        have hdownBeforePrefix : downIndex.val < prefixIndex.val := hdownBeforeUp
        rw [hprefixValue] at hdownBeforePrefix
        have hbeforeA : upIndex < a.val := hupIndex
        rw [hfullLength]
        exact Nat.lt_trans (Nat.lt_trans hdownBeforePrefix hbeforeA) a.isLt
      have hdownFullRetained :
          ReferenceAcceptedUpFollowerHistory.RetainedDown
            (full.records[downIndex.val]'hdownFullIndex) i priorDown := by
        have hrecordEq := hfullAt downIndex.val (by
          have hdownBeforePrefix : downIndex.val < prefixIndex.val := hdownBeforeUp
          rw [hprefixValue] at hdownBeforePrefix
          exact Nat.lt_trans hdownBeforePrefix hupIndex)
        rw [hrecordEq]
        exact hpriorRetained
      have hdownFullApplied :
          ReferenceFollowerReplyChronology.appliedDown
            (full.records[downIndex.val]'hdownFullIndex) i priorDown.val.sigma := by
        have hrecordEq := hfullAt downIndex.val (by
          have hdownBeforePrefix : downIndex.val < prefixIndex.val := hdownBeforeUp
          rw [hprefixValue] at hdownBeforePrefix
          exact Nat.lt_trans hdownBeforePrefix hupIndex)
        rw [hrecordEq]
        exact hpriorApplied
      have hpriorSigmaLedger : priorDown.val.sigma = ledger.sigma := by
        have hcoordinatorSame :
            CoordinatorConfiguration.collection installedPayload oldLedger oldProposal =
              .collection installedPayloadUp oldLedgerUp oldProposalUp :=
          hcoordinator.symm.trans hcoordinatorUp
        have hledgerUp : oldLedger = oldLedgerUp := by
          injection hcoordinatorSame with _ hledgerUp _
        have hstates :
            CoordinatorConfiguration.collection old.view.payload ledger proposal =
              .collection installedPayload oldLedger oldProposal := by
          calc
            _ = (R rate rewards C_star C_h s hs x a).input.state.coordinator := hstate.symm
            _ = (ReferenceCollectionPhaseHistory.nextInput seed rows selected rewards s a.val
                (by omega) hmode).state.coordinator :=
              congrArg (fun input : ReferenceActivePhysicalStep.RoundInput p rate =>
                input.state.coordinator) hinput
            _ = .collection installedPayload oldLedger oldProposal := hcoordinator
        have hledgerEq : oldLedger = ledger := by
          injection hstates with _ hledgerEq _
          exact hledgerEq.symm
        calc
          priorDown.val.sigma = message.val.sigma := hpriorSigma
          _ = oldLedgerUp.sigma := hmessageSigma
          _ = oldLedger.sigma :=
            congrArg (fun l : Ledger rate => l.sigma) hledgerUp.symm
          _ = ledger.sigma := congrArg (fun l : Ledger rate => l.sigma) hledgerEq
      have hpriorActualSigma : ∃ sigma,
          ReferenceFollowerReplyChronology.appliedDown
            (full.records[downIndex.val]'hdownFullIndex) i sigma ∧ sigma = ledger.sigma := by
        exact ⟨priorDown.val.sigma, hdownFullApplied, hpriorSigmaLedger⟩
      obtain ⟨priorSigma, _hpriorActuallyApplied, hpriorActuallySigma⟩ := hpriorActualSigma
      have hpriorSigmaEq : priorDown.val.sigma = priorSigma :=
        hpriorSigmaLedger.trans hpriorActuallySigma.symm
      have hmessageLedger : message.val.sigma = ledger.sigma := by
        calc
          message.val.sigma = priorDown.val.sigma := hpriorMessageSigma.symm
          _ = priorSigma := hpriorSigmaEq
          _ = ledger.sigma := hpriorActuallySigma
      have hacceptedLedger :
          ReferencePrelaunchFollower.acceptedStart upState = ledger.sigma :=
        hmessageStart.symm.trans hmessageLedger

      have hcurrentIndex : n.val < full.records.length := by
        rw [hfullLength]
        exact n.isLt
      have hupBeforeA : upIndex < a.val := hupIndex
      have hupBeforeCurrent : upIndex < n.val := Nat.lt_of_lt_of_le hupBeforeA han
      have hcurrentRecord : full.records[n.val]'hcurrentIndex =
          R rate rewards C_star C_h s hs x n := by
        have hsource := generatedSourceRecordAt_getElem?
          rate rewards C_star C_h s hs x n
        have hfullRun : generatedSourceRun rate rewards C_star C_h s hs x = full := rfl
        rw [hfullRun, List.getElem?_eq_getElem (by rw [hfullLength]; exact n.isLt)] at hsource
        exact Option.some.inj hsource
      have hleftChoice :
          (ReferenceFollowerFixedReply.actualChoice
            (full.records[upIndex]'hupFullIndex) i).configuration =
            .ordinary upState upMemory := by
        calc
          _ = upSender.configuration := by rw [hsenderFull]
          _ = .ordinary upState upMemory := hupConfiguration
      have hrightChoice :
          (ReferenceFollowerFixedReply.actualChoice (full.records[n.val]'hcurrentIndex) i).configuration =
            .ordinary currentState currentMemory := by
        rw [hcurrentRecord]
        exact hcurrentChoice
      have hmono :=
        ReferenceFollowerReplyChronology.run_acceptedStart_mono
          seed rows selected rewards s (p.T - s) (by omega) hmode i
          ⟨upIndex, hupFullIndex⟩ ⟨n.val, hcurrentIndex⟩
          (Fin.le_iff_val_le_val.mpr (Nat.le_of_lt hupBeforeCurrent))
          upState currentState upMemory currentMemory hleftChoice hrightChoice
      have hrecordSigma :
          (old.view.payload.downRecord i).val.sigma = ledger.sigma := by
        rw [old.view.payload.downRecord_fields i, hledgerSigma]
      have hcontradiction : False := by
        rw [hrecordSigma] at hcurrentStrict
        have hledgerCurrent : ledger.sigma ≤
            ReferencePrelaunchFollower.acceptedStart currentState :=
          (le_of_eq hacceptedLedger.symm).trans hmono.1
        exact (not_lt_of_ge hledgerCurrent) hcurrentStrict
      exact False.elim hcontradiction

end Bandits.Support.ReferenceGeneratedSelectedSuccessorStaleCut

end
