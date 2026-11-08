/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInheritedDownPostcutExclusion
public import Bandits.Support.ReferenceCollectionPriorDownHistory

import Lean.Elab.Tactic.Omega

/-!
# Generated retained-collection stale DOWN word cut

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109`,
`sources/zip4/manuscript/05_binary_transport.tex:70-124`,
`sources/zip4/manuscript/06_interruptions.tex:246-295,303-348`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

These internal results concern the actual generated physical run and one
retained DOWN diagnostic. They do not assert source-event coverage or close
the manuscript's all-test stale-word claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceGeneratedDownBatchCalendar
open ReferenceGeneratedInheritedDownWrongCompletionWitness
open ReferenceGeneratedInheritedDownCandidateOrigin
open ReferenceSelectedPayloadChronology
open ReferenceFirstLiveRawDownExclusion
open ReferenceDownReception
open ReferenceCorrectedInitializationLaunch
open ReferenceCollectionPhaseHistory

namespace Bandits.Support.ReferenceGeneratedRetainedCollectionStaleWordCut

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private abbrev Record :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

private abbrev DownRecord := OrdinaryMessageCodec.DownRecord
  (ReferencePrelaunchFollower.codecParams p rate.eta)

private abbrev FlatWord := AffineChannelLaw.Word (AffineBatchDecoder.width p)

private theorem generatedSeed_initial_state
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs) :
    let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
      rate rewards C_star C_h s hs x
    ReferenceActivePhysicalHorizon.allActiveAtStart seed s ∧
      seed.coordinator = .first ∧
      ∀ j : Fin (p.m - 1), ∃ state memory,
        seed.followers j = .ordinary state memory ∧ state.lastDown = none := by
  classical
  dsimp only
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs x
  have hseedSpec := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
    rate rewards C_star C_h s hs x
  obtain ⟨active, hactive, _hunique⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate x.val rewards C_star C_h x.property.1
  have hseedActive : seed = active := Option.some.inj (hseedSpec.1.symm.trans hactive.1)
  obtain ⟨activeFields, hfieldsLaunch, hfields⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
      rate x.val rewards C_star C_h x.property.1
  have hseedFields : seed = activeFields :=
    Option.some.inj (hseedSpec.1.symm.trans hfieldsLaunch)
  have hfirst : seed.coordinator = .first := by
    rw [hseedActive]
    exact hactive.2.1
  have hfollowers : ∀ j : Fin (p.m - 1), ∃ state memory,
      seed.followers j = .ordinary state memory ∧ state.lastDown = none := by
    intro j
    rcases hfields j with ⟨hconfiguration, hlastDown, _, _, _, _, _, _⟩
    refine ⟨ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate))
        (ActualReferenceInitializationBlock.refFollower j),
      ActiveFollowerLifecycle.initialMemory p, ?_, hlastDown⟩
    rw [hseedFields]
    exact hconfiguration
  exact ⟨hseedSpec.2.1, hfirst, hfollowers⟩

private theorem dispatch_origin (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    match (ReferenceActivePhysicalStep.prepare x).coordinator with
    | .first _ => x.state.coordinator = .first
    | .live registers owned base _ => x.state.coordinator = .live registers owned base
    | .collection payload ledger _ _ _ =>
        ∃ proposal, x.state.coordinator = .collection payload ledger proposal
    | .invalidCollectionCutoff => True
    | .dagger => x.state.coordinator = .dagger := by
  change match ReferenceActivePhysicalStep.dispatch x with
    | .first _ => _
    | .live registers owned base _ => _
    | .collection payload ledger _ _ _ => _
    | .invalidCollectionCutoff => _
    | .dagger => _
  cases hc : x.state.coordinator with
  | first => rw [ReferenceActivePhysicalStep.dispatch_first x hc]
  | live registers owned base =>
      have he : ReferenceActivePhysicalStep.dispatch x =
          .live registers owned base
            (CoordinatorRoundDispatch.dispatchLive
              (ReferenceActivePhysicalStep.liveInput x registers owned base)) := by
        simp only [ReferenceActivePhysicalStep.dispatch, hc,
          CoordinatorRoundDispatch.dispatch]
        rfl
      rw [he]
  | dagger => rw [ReferenceActivePhysicalStep.dispatch_dagger x hc]
  | collection payload ledger proposal =>
      by_cases hv : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        have he : ReferenceActivePhysicalStep.dispatch x =
            .collection payload ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) := by
          simp only [ReferenceActivePhysicalStep.dispatch, hc, hv,
            CoordinatorRoundDispatch.dispatch]
          rfl
        rw [he]
        exact ⟨proposal, rfl⟩
      · rw [(ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff
          x payload ledger proposal hc hv).1]
        trivial

private theorem generatedRecord_input_eq_nextInput
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (n : Fin (p.T - s)) :
    (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x n).input =
    ReferenceCollectionPhaseHistory.nextInput
      (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
        rate rewards C_star C_h s hs x)
      x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s n.val
      (by omega)
      (generatedSeed_initial_state rate rewards C_star C_h s hs x).1 := by
  classical
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs x
  have hseed := generatedSeed_initial_state rate rewards C_star C_h s hs x
  let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := hseed.1
  let rows := x.val.1.2
  let selectedRow := ActualInitializationPhysicalStep.selectedRowIndex p x.val
  let total := ReferenceActivePhysicalHorizon.run seed rows selectedRow rewards s
    (p.T - s) (by omega) hmode
  let prefixRun := ReferenceActivePhysicalHorizon.run seed rows selectedRow rewards s n.val
    (by omega) hmode
  let through := ReferenceActivePhysicalHorizon.run seed rows selectedRow rewards s
    (n.val + 1) (by omega) hmode
  let xn := ReferenceCollectionPhaseHistory.nextInput seed rows selectedRow rewards s n.val
    (by omega) hmode
  have hgen : ReferenceGeneratedDownBatchCalendar.generatedSourceRun
      rate rewards C_star C_h s hs x = total := rfl
  have htotalCount : total.records.length = p.T - s :=
    ReferenceActivePhysicalHorizon.run_record_count seed rows selectedRow rewards s
      (p.T - s) (by omega) hmode
  have hrecord (j : Fin (p.T - s)) :
      total.records[j.val]'(by omega) =
        ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x j := by
    have hget :=
      ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
        rate rewards C_star C_h s hs x j
    rw [hgen, List.getElem?_eq_getElem (by rw [htotalCount]; exact j.isLt)] at hget
    exact Option.some.inj hget
  obtain ⟨suffix, hrecords⟩ :=
    ReferenceCollectionPhaseHistory.run_records_prefix seed rows selectedRow rewards s
      (n.val + 1) (p.T - s - (n.val + 1)) (by omega) hmode
  have hrecordsTotal : total.records = through.records ++ suffix := by
    simpa [total, through, hgen] using hrecords
  have happendCount : (through.records ++ suffix).length = p.T - s := by
    calc
      (through.records ++ suffix).length = total.records.length :=
        congrArg List.length hrecordsTotal.symm
      _ = p.T - s := htotalCount
  have hthroughCount : through.records.length = n.val + 1 :=
    ReferenceActivePhysicalHorizon.run_record_count seed rows selectedRow rewards s
      (n.val + 1) (by omega) hmode
  have hcurrentRecord :
      through.records[n.val]'(by omega) =
        ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x n := by
    calc
      through.records[n.val]'(by rw [hthroughCount]; omega) =
          (through.records ++ suffix)[n.val]'(by rw [happendCount]; exact n.isLt) :=
        List.getElem_append_left' (l₁ := through.records) (i := n.val)
          (by rw [hthroughCount]; omega) suffix
      _ = total.records[n.val]'(by rw [htotalCount]; exact n.isLt) :=
        (List.getElem_of_eq hrecordsTotal (by rw [htotalCount]; exact n.isLt)).symm
      _ = ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x n := hrecord n
  have hsuccessor : through =
      ReferenceActivePhysicalHorizon.foldRound seed rows selectedRow rewards s hmode
        prefixRun ⟨s + n.val, by omega, by omega⟩ := by
    simpa [through, prefixRun] using
      ReferenceActivePhysicalHorizon.run_successor_step seed rows selectedRow rewards s n.val
        (by omega) hmode
  have hsuccessorRecords : through.records =
      (ReferenceActivePhysicalHorizon.foldRound seed rows selectedRow rewards s hmode
        prefixRun ⟨s + n.val, by omega, by omega⟩).records :=
    congrArg (fun run : ReferenceActivePhysicalHorizon.Run seed => run.records) hsuccessor
  have hprefixCount : prefixRun.records.length = n.val :=
    ReferenceActivePhysicalHorizon.run_record_count seed rows selectedRow rewards s n.val
      (by omega) hmode
  have hthroughInput : (through.records[n.val]'(by omega)).input = xn := by
    calc
      (through.records[n.val]'(by omega)).input =
          ((ReferenceActivePhysicalHorizon.foldRound seed rows selectedRow rewards s hmode
            prefixRun ⟨s + n.val, by omega, by omega⟩).records[n.val]'(by
              simpa [hsuccessorRecords] using (show n.val < through.records.length by
                rw [hthroughCount]
                omega))).input := congrArg (fun record : Record => record.input)
                  (List.getElem_of_eq hsuccessorRecords (by rw [hthroughCount]; omega))
      _ = xn := by
        simp [ReferenceActivePhysicalHorizon.foldRound, hprefixCount,
          ReferenceCollectionPhaseHistory.nextInput, xn,
          ReferenceActivePhysicalHorizon.roundInputAt]; rfl
  calc
    (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n).input =
        (through.records[n.val]'(by omega)).input :=
      congrArg (fun record : Record => record.input) hcurrentRecord.symm
    _ = xn := hthroughInput

private theorem generatedRecord_mem_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (k n : Fin (p.T - s)) (hkn : k.val < n.val) :
    ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x k ∈
    (ReferenceActivePhysicalHorizon.run
      (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h s hs x)
      x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s n.val
      (by omega)
      (generatedSeed_initial_state rate rewards C_star C_h s hs x).1).records := by
  classical
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs x
  have hseed := generatedSeed_initial_state rate rewards C_star C_h s hs x
  let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := hseed.1
  let rows := x.val.1.2
  let selectedRow := ActualInitializationPhysicalStep.selectedRowIndex p x.val
  let total := ReferenceActivePhysicalHorizon.run seed rows selectedRow rewards s
    (p.T - s) (by omega) hmode
  let prefixRun := ReferenceActivePhysicalHorizon.run seed rows selectedRow rewards s n.val
    (by omega) hmode
  have hgen : ReferenceGeneratedDownBatchCalendar.generatedSourceRun
      rate rewards C_star C_h s hs x = total := rfl
  have htotalCount : total.records.length = p.T - s :=
    ReferenceActivePhysicalHorizon.run_record_count seed rows selectedRow rewards s
      (p.T - s) (by omega) hmode
  have hrecord (j : Fin (p.T - s)) :
      total.records[j.val]'(by omega) =
        ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x j := by
    have hget :=
      ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
        rate rewards C_star C_h s hs x j
    rw [hgen, List.getElem?_eq_getElem (by rw [htotalCount]; exact j.isLt)] at hget
    exact Option.some.inj hget
  obtain ⟨suffix, hrecords⟩ :=
    ReferenceCollectionPhaseHistory.run_records_prefix seed rows selectedRow rewards s
      n.val (p.T - s - n.val) (by omega) hmode
  have hrecordsTotal : total.records = prefixRun.records ++ suffix := by
    simpa [total, prefixRun, hgen] using hrecords
  have happendCount : (prefixRun.records ++ suffix).length = p.T - s := by
    calc
      (prefixRun.records ++ suffix).length = total.records.length :=
        congrArg List.length hrecordsTotal.symm
      _ = p.T - s := htotalCount
  have hprefixCount : prefixRun.records.length = n.val :=
    ReferenceActivePhysicalHorizon.run_record_count seed rows selectedRow rewards s n.val
      (by omega) hmode
  have hget :
      prefixRun.records[k.val]'(by omega) =
        ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x k := by
    calc
      prefixRun.records[k.val]'(by omega) = total.records[k.val]'(by omega) := by
        calc
          prefixRun.records[k.val]'(by rw [hprefixCount]; omega) =
              (prefixRun.records ++ suffix)[k.val]'(by rw [happendCount]; exact k.isLt) :=
            List.getElem_append_left' (l₁ := prefixRun.records) (i := k.val)
              (by rw [hprefixCount]; exact hkn) suffix
          _ = total.records[k.val]'(by rw [htotalCount]; exact k.isLt) :=
            (List.getElem_of_eq hrecordsTotal (by rw [htotalCount]; exact k.isLt)).symm
      _ = ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x k := hrecord k
  rw [← hget]
  exact List.getElem_mem (by rw [hprefixCount]; exact hkn)

private theorem referenceDownCut_expectedWord
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (logged : ReferencePrelaunchFollower.State p rate.eta) :
    (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).expectedWord =
      ReferenceDownReception.expectedDownFlatWord view i row time := by
  classical
  unfold ReferenceDownReception.referenceDownCut
  split
  · split
    · split
      · split
        · split
          · dsimp only
            split <;> rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

private theorem referenceDownCut_parse_eq
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (logged : ReferencePrelaunchFollower.State p rate.eta) :
    (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).ordinaryParse =
      ReferenceDownReception.ordinaryParse p rate
        (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).raw := by
  classical
  unfold ReferenceDownReception.referenceDownCut
  split
  · split
    · split
      · split
        · split
          · dsimp only
            split <;> rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

private theorem referenceDownCut_acceptance_eq
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (logged : ReferencePrelaunchFollower.State p rate.eta) :
    (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).ordinaryAcceptance =
      ReferenceDownReception.ordinaryLocalAcceptanceTest p rate time logged
        (ReferenceDownReception.ordinaryParse p rate
          (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).raw) := by
  classical
  unfold ReferenceDownReception.referenceDownCut
  split
  · split
    · split
      · split
        · split
          · dsimp only
            split <;> rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

private theorem wrong_cut_excluded_of_selected_word
    (Rn : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (word : FlatWord) (current : ReferenceActivePhysicalStep.Selection Rn.input)
    (hcurrentSelection : Rn.output.preparation.coordinator.selection = some current)
    (hcut : (Rn.output.followers i).down = some cut)
    (hwrongCut : ReferenceDownReception.wrongUniqueAccepted cut)
    (hraw : cut.raw = some word)
    (hpending : i ∈ current.view.pendingAtChoice)
    (hwordCurrent : word =
      CoordinatorLocalArmChoice.storedDownFlatWord current.view.payload i) : False := by
  classical
  obtain ⟨choiceState, memory, logged, _, _, _, _hlogged, _⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice
      Rn i cut hcut
  have hcutActual :=
    ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
      Rn i logged cut _hlogged hcut
  have hfalseActual := hwrongCut.1
  rw [hcutActual] at hfalseActual
  have hcompared :
      (ReferenceDownReception.referenceDownCut p
        Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
        rate logged).rawComparison ≠ none := by
    rw [hfalseActual]
    simp
  have hcomparisonSome :
      (ReferenceDownReception.referenceDownCut p
        Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
        rate logged).rawComparison.isSome = true := by
    rw [hfalseActual]
    rfl
  have hgate := ReferenceActiveAffinePositiveTest.referenceDownCut_has_call
    Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i) logged
  rw [hgate] at hcomparisonSome
  have hdownGate : ReferenceActiveAffinePositiveTest.downReceiverGate i Rn.input.row
      Rn.input.time logged := of_decide_eq_true hcomparisonSome
  have hrawDecode :=
    ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
      Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
      rate logged hcompared
  have hrawActual := hraw
  rw [hcutActual] at hrawActual
  have hdecoded :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i Rn.input.row Rn.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
        rate logged).2 = some word := hrawDecode.symm.trans hrawActual
  have hview : Rn.output.preparation.coordinator.downView = some current.view := by
    simp only [ReferenceActivePhysicalStep.DispatchCut.downView,
      hcurrentSelection, Option.map_some]
  have hsenderCurrent :
      ReferenceDownReception.selectedDownSenderBranch current.view i
        Rn.input.row Rn.input.time :=
    ⟨hdownGate.1.1, hdownGate.1.2, hpending⟩
  have hselectedExpected :=
    ReferenceActivePhysicalStep.Selection.expected_down_word current i hsenderCurrent
  have hselectedExpected' :
      ReferenceDownReception.expectedDownFlatWord (some current.view) i
        Rn.input.row Rn.input.time =
      some (CoordinatorLocalArmChoice.storedDownFlatWord current.view.payload i) := by
    simpa only [ReferenceActivePhysicalStep.RoundInput.row] using hselectedExpected
  have hcutExpected : cut.expectedWord =
      ReferenceDownReception.expectedDownFlatWord
        Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time := by
    calc
      cut.expectedWord =
          (ReferenceDownReception.referenceDownCut p
            Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
            rate logged).expectedWord := congrArg
              ReferenceDownReception.ReferenceDownCutOutput.expectedWord hcutActual
      _ = ReferenceDownReception.expectedDownFlatWord
          Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time :=
        referenceDownCut_expectedWord _ _ _ _ _ _
  have hcutExpectedCurrent : cut.expectedWord =
      ReferenceDownReception.expectedDownFlatWord
        (some current.view) i Rn.input.row Rn.input.time := by
    rw [hview] at hcutExpected
    exact hcutExpected
  have hactualExpected : cut.expectedWord = some word := by
    rw [hcutExpectedCurrent, hselectedExpected']
    exact congrArg some hwordCurrent.symm
  have hdecodedMatchesExpected :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i Rn.input.row Rn.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
        rate logged).2 =
      ReferenceDownReception.expectedDownFlatWord
        Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time := by
    calc
      _ = some word := hdecoded
      _ = cut.expectedWord := hactualExpected.symm
      _ = ReferenceDownReception.expectedDownFlatWord
          Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time := hcutExpected
  have hcomparisonTrue :
      (ReferenceDownReception.referenceDownCut p
        Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
        rate logged).rawComparison = some true := by
    simp [ReferenceDownReception.referenceDownCut, hdownGate.1, hdownGate.2.1,
      hdownGate.2.2.1, hdownGate.2.2.2.1, hdownGate.2.2.2.2,
      hdecodedMatchesExpected]
  rw [hcomparisonTrue] at hfalseActual
  cases hfalseActual

/-- A retained wrong accepted DOWN word in the actual continuing collection
branch differs from that branch's complete stored word for this follower. -/
theorem generated_retained_collection_wrong_word
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x n).output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut) :
    match (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x n).output.preparation.coordinator with
    | .collection payload _ledger _clock _cutoff
        (.continuing _core _snapshot _boundary _scores) =>
        cut.raw ≠ some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)
    | _ => True := by
  classical
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs x
  obtain ⟨hmode, hfirst, hseedFollowers⟩ :=
    generatedSeed_initial_state rate rewards C_star C_h s hs x
  let rows := x.val.1.2
  let selectedRow := ActualInitializationPhysicalStep.selectedRowIndex p x.val
  let E := ReferenceActivePhysicalHorizon.run seed rows selectedRow rewards s
    (p.T - s) (by omega) hmode
  have hgen : ReferenceGeneratedDownBatchCalendar.generatedSourceRun
      rate rewards C_star C_h s hs x = E := rfl
  have hlength : E.records.length = p.T - s :=
    ReferenceActivePhysicalHorizon.run_record_count seed rows selectedRow rewards s
      (p.T - s) (by omega) hmode
  have hrecord (j : Fin (p.T - s)) :
      E.records[j.val]'(by omega) =
        ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x j := by
    have hget :=
      ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
        rate rewards C_star C_h s hs x j
    rw [hgen, List.getElem?_eq_getElem (by omega)] at hget
    exact Option.some.inj hget
  let prefixRun := ReferenceActivePhysicalHorizon.run seed rows selectedRow rewards s n.val
    (by omega) hmode
  let xn := ReferenceCollectionPhaseHistory.nextInput seed rows selectedRow rewards s n.val
    (by omega) hmode
  have hinput :
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n).input = xn := by
    simpa [seed, xn] using generatedRecord_input_eq_nextInput rate rewards C_star C_h s hs x n
  cases hcoord : (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x n).output.preparation.coordinator with
  | first outcome => trivial
  | live registers owned base outcome => trivial
  | invalidCollectionCutoff => trivial
  | dagger => trivial
  | collection payload ledger clock cutoff outcome =>
    cases outcome with
    | continuing core snapshot boundary scores =>
      let Rn := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n
      have hcoordPrep : (ReferenceActivePhysicalStep.prepare Rn.input).coordinator =
          .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) := by
        have hh := hcoord
        rw [Rn.output_eq] at hh
        exact hh
      have horigin := dispatch_origin Rn.input
      rw [hcoordPrep] at horigin
      obtain ⟨proposal, hstate⟩ := horigin
      have hstate' : xn.state.coordinator = .collection payload ledger proposal := by
        have hstateInput := congrArg
          (fun y : ReferenceActivePhysicalStep.RoundInput p rate => y.state.coordinator) hinput
        exact hstateInput.symm.trans hstate
      have hcollection : prefixRun.finalState.coordinator = .collection payload ledger proposal := by
        simpa [xn, prefixRun, ReferenceCollectionPhaseHistory.nextInput,
          ReferenceActivePhysicalHorizon.roundInputAt] using hstate'
      have hmode' : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := hmode
      obtain ⟨firstState, firstMemory, hfirstFollower, hfirstNoDown⟩ := hseedFollowers i
      obtain ⟨choiceState, currentMemory, logged, hloggedChoice, hunoccupied,
          hlogging, hdownInput, hcutEq⟩ :=
        ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice
          Rn i cut hcut
      have hcutActual :=
        ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
          Rn i logged cut hdownInput hcut
      have hparseFromRaw (hraw : cut.raw =
          some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) :
          cut.ordinaryParse = some (payload.downRecord i) := by
        have hrawActual :
            (ReferenceDownReception.referenceDownCut p
              Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
              rate logged).raw =
            some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
          simpa only [hcutActual] using hraw
        calc
          cut.ordinaryParse =
              (ReferenceDownReception.referenceDownCut p
                Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
                (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
                rate logged).ordinaryParse := congrArg
                  ReferenceDownReception.ReferenceDownCutOutput.ordinaryParse hcutActual
          _ = ReferenceDownReception.ordinaryParse p rate
                (ReferenceDownReception.referenceDownCut p
                  Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
                  (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
                  rate logged).raw := referenceDownCut_parse_eq _ _ _ _ _ _
          _ = some (payload.downRecord i) := by
            rw [hrawActual]
            unfold ReferenceDownReception.ordinaryParse
              CoordinatorLocalArmChoice.storedDownFlatWord
            change OrdinaryMessageCodec.parseDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (some ((OrdinaryMessageCodec.wordEquivFlat
                (ReferencePrelaunchFollower.codecParams p rate.eta)).symm
                ((OrdinaryMessageCodec.wordEquivFlat
                  (ReferencePrelaunchFollower.codecParams p rate.eta))
                  (payload.downWord i)))) = _
            rw [Equiv.symm_apply_apply]
            exact payload.parseDown_downWord i
      have hrawNe : cut.raw ≠ some
          (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
        intro hraw
        have hparse := hparseFromRaw hraw
        obtain ⟨current, currentMemory, hcurrentChoice, _hunoccupied, hstrict⟩ :=
          ReferenceFirstLiveRawDownExclusion.retained_raw_down_parse_acceptance_actual_choice
            Rn i cut (payload.downRecord i) hcut hparse hwrong.2.2
        have hpreparedChoice :
            ((ReferenceActivePhysicalStep.prepare Rn.input).followers.followers i).configuration =
              .ordinary current currentMemory := by
          have h := hcurrentChoice
          simp only [ReferenceFollowerFixedReply.actualChoice] at h
          rw [Rn.output_eq] at h
          simpa [ReferenceActivePhysicalStep.step] using h
        cases hselection : (ReferenceActivePhysicalStep.prepare Rn.input).coordinator.selection with
        | none =>
            have hselectedNone :
                (DispatchCut.collection payload ledger clock cutoff
                  (.continuing core snapshot boundary scores)).selection = none := by
              simpa only [hcoordPrep] using hselection
            simp [DispatchCut.selection] at hselectedNone
        | some selected =>
            have hselected :
                (ReferenceActivePhysicalStep.prepare Rn.input).coordinator.selection = some selected :=
              hselection
            have hselectedRn : Rn.output.preparation.coordinator.selection = some selected := by
              rw [Rn.output_eq]
              simpa [ReferenceActivePhysicalStep.step] using hselected
            have hpendingFields := congrArg
              (Option.map (fun value : ReferenceActivePhysicalStep.Selection Rn.input =>
                value.view.pendingAtChoice)) hselected
            simp only [hcoordPrep, ReferenceActivePhysicalStep.DispatchCut.selection,
              Option.map_some] at hpendingFields
            have hpending : selected.view.pendingAtChoice = ledger.pending :=
              (Option.some.inj hpendingFields).symm.trans snapshot.clockStarted_frame.2.1
            by_cases hpendingI : i ∈ ledger.pending
            ·
                have hpendingSelected : i ∈ selected.view.pendingAtChoice := by
                  rw [hpending]
                  exact hpendingI
                have hpayloadSelected : selected.view.payload = payload := by
                  have hs := hselection
                  rw [hcoordPrep, DispatchCut.selection] at hs
                  cases hs
                  rfl
                have hwordSelected :
                    CoordinatorLocalArmChoice.storedDownFlatWord payload i =
                    CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i :=
                  (congrArg
                    (fun value : AssignmentStartPayload.Input p rate.eta =>
                      CoordinatorLocalArmChoice.storedDownFlatWord value i)
                    hpayloadSelected).symm
                have hnot := wrong_cut_excluded_of_selected_word Rn i cut
                  (CoordinatorLocalArmChoice.storedDownFlatWord payload i) selected
                  hselectedRn hcut hwrong hraw hpendingSelected hwordSelected
                exact hnot.elim
            ·
                have hmissing : i ∉ ledger.pending := hpendingI
                have hcurrent :
                    ((ReferenceActivePhysicalStep.prepare
                      (ReferenceCollectionPhaseHistory.nextInput seed rows selectedRow rewards
                        s n.val (by omega) hmode)).followers.followers i).configuration =
                      .ordinary current currentMemory := by
                  cases hinput
                  exact hpreparedChoice
                have hspan : s + (n.val + 1) ≤ p.T := by omega
                have hguard :=
                  ReferenceCollectionPriorDownHistory.run_collection_continuing_dispatch_prior_down_guard
                    seed rows selectedRow rewards s n.val hspan hmode hfirst i firstState
                    firstMemory hfirstFollower hfirstNoDown payload ledger proposal hcollection
                    hmissing current currentMemory hcurrent
                    ⟨clock, cutoff, core, snapshot, boundary, scores, hcoordPrep⟩
                change ReferenceCollectionPriorDownHistory.ContinuingPriorDownGuard seed xn
                  (ReferenceActivePhysicalHorizon.run seed rows selectedRow rewards s
                    (n.val + 1) hspan hmode) n.val i payload ledger current at hguard
                rcases hguard with ⟨j, k, hj, hk, message, prior, sender, upState,
                  upMemory, hjk, hkcount, haccepted, hretained, happlied,
                  hpriorSigma, hmessageSigma, hsender, hconfiguration, hunoccupied,
                  hoff, hstart, hlast, hpositive, hpriorEq, hledgerSource, hsourceLe,
                  hloggedReject⟩
                have hstrictCurrent : ReferencePrelaunchFollower.acceptedStart current <
                    (payload.downRecord i).val.sigma := by
                  exact hstrict
                have hrejectActual := hloggedReject logged cut hdownInput hcut
                have hstrictLogged : ReferencePrelaunchFollower.acceptedStart logged <
                    (payload.downRecord i).val.sigma := by
                  rw [hrejectActual.1]
                  exact hstrictCurrent
                have hpriorStart : prior.val.sigma =
                    (payload.downRecord i).val.sigma := congrArg
                      (fun value : DownRecord => value.val.sigma) hpriorEq
                have hpriorLedger : prior.val.sigma = ledger.sigma :=
                  hpriorSigma.trans hmessageSigma
                have hrecordLedger : (payload.downRecord i).val.sigma = ledger.sigma :=
                  hpriorStart.symm.trans hpriorLedger
                have hledgerCore : ledger.sigma = payload.sigma.val + 1 := by
                  simpa [ReferenceActivePhysicalStep.collectionInput,
                    CoordinatorRecorderComplementBridge.sourceStart] using
                    core.ledger_sigma_eq
                have hsourceBound : ledger.sigma ≤
                    ReferencePrelaunchFollower.acceptedStart current := by
                  rw [hledgerCore]
                  exact hsourceLe
                rw [hrecordLedger] at hstrictLogged
                have hsourceContradiction : False := by
                  have hloggedFrame :
                      ReferencePrelaunchFollower.acceptedStart logged =
                        ReferencePrelaunchFollower.acceptedStart current := hrejectActual.1
                  omega
                exact hsourceContradiction
      simpa [hcoord] using hrawNe
    | _ => trivial

/-- An earlier actual DOWN sender that retained the current accepted wrong cut
must come from a strictly different assignment start if the current branch is
retained collection-continuing. -/
theorem generated_retained_collection_earlier_sender_cut
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x n).output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut)
    (k : Fin (p.T - s)) (hkn : k.val < n.val)
    (oldCut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hold : ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x k).output.followers i).down = some oldCut)
    (hsent : oldCut.expectedWord = cut.raw) :
    ∃ old : ReferenceActivePhysicalStep.Selection
        (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x k).input,
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x k).output.preparation.coordinator.selection = some old ∧
      ReferenceDownReception.selectedDownSenderBranch old.view i
        (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x k).input.row
        (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x k).input.time ∧
      match (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n).output.preparation.coordinator with
      | .collection payload _ledger _clock _cutoff
          (.continuing _core _snapshot _boundary _scores) =>
          old.view.payload.sigma.val ≠ payload.sigma.val
      | _ => True := by
  classical
  cases hraw : cut.raw with
  | none => exact False.elim (hwrong.2.1 hraw)
  | some word =>
    have hexpected : oldCut.expectedWord = some word := by
      rw [hsent, hraw]
    obtain ⟨old, holdSelection, hsender, _hword, _hparse, _hencode⟩ :=
      ReferenceGeneratedInheritedDownCandidateOrigin.actual_expectedDownWord_origin
        (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x k) i oldCut word hold hexpected
    let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
      rate rewards C_star C_h s hs x
    obtain ⟨hmode, hfirst, _hseedFollowers⟩ :=
      generatedSeed_initial_state rate rewards C_star C_h s hs x
    let rows := x.val.1.2
    let selectedRow := ActualInitializationPhysicalStep.selectedRowIndex p x.val
    let total := ReferenceActivePhysicalHorizon.run seed rows selectedRow rewards s
      (p.T - s) (by omega) hmode
    let prefixRun := ReferenceActivePhysicalHorizon.run seed rows selectedRow rewards s
      n.val (by omega) hmode
    have hgen : ReferenceGeneratedDownBatchCalendar.generatedSourceRun
        rate rewards C_star C_h s hs x = total := rfl
    have hlength : total.records.length = p.T - s :=
      ReferenceActivePhysicalHorizon.run_record_count seed rows selectedRow rewards s
        (p.T - s) (by omega) hmode
    have hrecord (j : Fin (p.T - s)) :
        total.records[j.val]'(by omega) =
          ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
            rate rewards C_star C_h s hs x j := by
      have hget :=
        ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
          rate rewards C_star C_h s hs x j
      rw [hgen, List.getElem?_eq_getElem (by omega)] at hget
      exact Option.some.inj hget
    have hrecordMem :
        ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x k ∈ total.records := by
      have hrecordPrefix := generatedRecord_mem_prefix rate rewards C_star C_h s hs x k n hkn
      have hrecordPrefix' :
          ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
            rate rewards C_star C_h s hs x k ∈ prefixRun.records := by
        simpa [seed, prefixRun] using hrecordPrefix
      obtain ⟨prefixSuffix, hprefixRecords⟩ :=
        ReferenceCollectionPhaseHistory.run_records_prefix seed rows selectedRow rewards s n.val
          (p.T - s - n.val) (by omega) hmode
      have hprefixTotal : total.records = prefixRun.records ++ prefixSuffix := by
        simpa [total, prefixRun, hgen] using hprefixRecords
      rw [hprefixTotal]
      exact List.mem_append.mpr (Or.inl hrecordPrefix')
    cases hcoord : (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n).output.preparation.coordinator with
    | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
        let xn := ReferenceCollectionPhaseHistory.nextInput seed rows selectedRow rewards s n.val
          (by omega) hmode
        have hinput :
            (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
              rate rewards C_star C_h s hs x n).input = xn := by
          simpa [seed, xn] using generatedRecord_input_eq_nextInput rate rewards C_star C_h s hs x n
        let Rn := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x n
        have hcoordPrep : (ReferenceActivePhysicalStep.prepare Rn.input).coordinator =
            .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) := by
          have hh := hcoord
          rw [Rn.output_eq] at hh
          exact hh
        have horigin := dispatch_origin Rn.input
        rw [hcoordPrep] at horigin
        obtain ⟨proposal, hstate⟩ := horigin
        have hstate' : xn.state.coordinator = .collection payload ledger proposal := by
          have hstateInput := congrArg
            (fun y : ReferenceActivePhysicalStep.RoundInput p rate => y.state.coordinator) hinput
          exact hstateInput.symm.trans hstate
        have hcollection : prefixRun.finalState.coordinator = .collection payload ledger proposal := by
          simpa [xn, prefixRun, ReferenceCollectionPhaseHistory.nextInput,
            ReferenceActivePhysicalHorizon.roundInputAt] using hstate'
        have hprefixStored :
            ReferenceAssignmentPayloadPersistence.storedPayload prefixRun.finalState.coordinator =
              some payload := by
          simp [ReferenceAssignmentPayloadPersistence.storedPayload, hcollection]
        have hneqSigma : old.view.payload.sigma.val ≠ payload.sigma.val := by
          intro heqSigma
          have hfullSpan : s + (p.T - s) ≤ p.T := by omega
          have hmem :
              ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
                rate rewards C_star C_h s hs x k ∈ total.records := hrecordMem
          have hselectionPrefix :=
            ReferenceSelectedPayloadChronology.run_actualSelectedPayload_eq_of_prefix_storedPayload_equal_sigma
              seed rows selectedRow rewards s (p.T - s) hfullSpan hmode hfirst
              (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
                rate rewards C_star C_h s hs x k) old hmem holdSelection n.val
              (Nat.le_of_lt n.isLt) payload (by simpa [prefixRun] using hprefixStored)
              heqSigma
          have hwordPayload :
              word = CoordinatorLocalArmChoice.storedDownFlatWord payload i := by
            exact _hword.trans
              (congrArg
                (fun value : AssignmentStartPayload.Input p rate.eta =>
                  CoordinatorLocalArmChoice.storedDownFlatWord value i)
                hselectionPrefix.1)
          have hnotCurrent := generated_retained_collection_wrong_word
            rate rewards C_star C_h s hs x i n cut hcut hwrong
          have hnotCurrent' :
              cut.raw ≠ some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
            simpa [hcoord] using hnotCurrent
          have hcurrentRaw : cut.raw =
              some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
            rw [hraw, hwordPayload]
            rfl
          exact hnotCurrent' hcurrentRaw
        exact ⟨old, holdSelection, hsender, hneqSigma⟩
      | _ => exact ⟨old, holdSelection, hsender, trivial⟩
    | _ => exact ⟨old, holdSelection, hsender, trivial⟩

end Bandits.Support.ReferenceGeneratedRetainedCollectionStaleWordCut

end
