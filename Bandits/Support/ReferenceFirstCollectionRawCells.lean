/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionChosenContext

import Lean.Elab.Tactic.Omega

/-!
# Actual first-collection raw Option cells

For an actual selected input in the first collection window, the raw Option
cells before reception are exactly the positive, pre-freeze recorder
diagnostics in the preceding physical records.  The records remain the
original physical rows; the checked ledger fold is used only to transport
their already validated local operations.

Mathematical sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,
246-295`, `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCollectionSegmentExtraction
open Bandits.Support.ReferenceFirstCollectionEpochAlignment
open Bandits.Support.ReferenceFirstCollectionChosenContext
open Bandits.Support.CollectionBufferProvenance
open Bandits.Support.CollectionCheckedExecution
open Bandits.Support.CoordinatorCollectionLedger

namespace Bandits.Support.ReferenceFirstCollectionRawCells

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters}
variable {rate : RateInput p}

/-- Search the supplied physical prefix for its actual record at `round`.
The caller's physical run supplies uniqueness; this operation has no default
record and does not filter the prefix. -/
def findPhysicalRecord? (records : List (ReferenceActivePhysicalHorizon.RoundRecord
    (p := p) (rate := rate))) (round : Fin p.T) :=
  records.find? fun record => decide (record.input.time = round)

private theorem findPhysicalRecord_eq_none_of_no_match
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (round : Fin p.T)
    (hno : ∀ record ∈ records, record.input.time ≠ round) :
    findPhysicalRecord? records round = none := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      have hhead := hno record (by simp)
      have htail : ∀ later ∈ rest, later.input.time ≠ round := by
        intro later hmem
        exact hno later (List.mem_cons_of_mem record hmem)
      change List.find? (fun item => decide (item.input.time = round))
          (record :: rest) = none
      rw [List.find?_cons]
      have hpred : decide (record.input.time = round) = false := by
        simp [hhead]
      rw [hpred]
      change findPhysicalRecord? rest round = none
      exact ih htail

/-- The raw Option cell named by the first matching physical recorder row.
A diagnostic `(arm, 0)` is retained by `rawDiagnostic` but inserts no cell. -/
def physicalRawCell (records : List (ReferenceActivePhysicalHorizon.RoundRecord
    (p := p) (rate := rate))) (freezeAt : ℕ) (arm : Fin p.K) (round : Fin p.T) : Option ℕ :=
  match findPhysicalRecord? records round with
  | none => none
  | some record =>
      match ReferenceCollectionRawBufferHistory.rawDiagnostic record with
      | none => none
      | some (recordedArm, amount) =>
          if recordedArm = arm ∧ 0 < amount ∧ round.val + 1 < freezeAt then
            some amount
          else none

private theorem physicalRawCell_eq_none_of_no_match
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (freezeAt : ℕ) (arm : Fin p.K) (round : Fin p.T)
    (hno : ∀ record ∈ records, record.input.time ≠ round) :
    physicalRawCell records freezeAt arm round = none := by
  unfold physicalRawCell
  rw [findPhysicalRecord_eq_none_of_no_match records round hno]

private def knownRawColumnEmpty (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (arm : Fin p.K) : Prop :=
  ledger.currentRegisters arm ≠ none → ∀ round, ledger.rawBuffer arm round = none

private theorem roundRecord_eq_step (record : ReferenceActivePhysicalHorizon.RoundRecord
    (p := p) (rate := rate)) :
    record = ⟨record.input, ReferenceActivePhysicalStep.step record.input, rfl⟩ := by
  cases record with
  | mk input output output_eq => cases output_eq; rfl

private theorem connected_append_split
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (left right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hchain : ReferenceActivePhysicalHorizon.Connected initial (left ++ right) final) :
    ∃ middle,
      ReferenceActivePhysicalHorizon.Connected initial left middle ∧
      ReferenceActivePhysicalHorizon.Connected middle right final := by
  induction left generalizing initial with
  | nil => exact ⟨initial, rfl, hchain⟩
  | cons record rest ih =>
      simp only [List.cons_append, ReferenceActivePhysicalHorizon.Connected] at hchain
      obtain ⟨middle, hleft, hright⟩ := ih hchain.2
      exact ⟨middle, ⟨hchain.1, hleft⟩, hright⟩

private theorem choice_none_of_dagger (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hdagger : x.state.coordinator = .dagger) :
    ReferenceCollectionSegmentExtraction.choice x = none := by
  simp [ReferenceCollectionSegmentExtraction.choice, ReferenceActivePhysicalStep.prepare,
    ReferenceActivePhysicalStep.dispatch_dagger x hdagger,
    ReferenceActivePhysicalStep.DispatchCut.selection]

/-- In a carried collection state, a non-later-choice input with no selected
collection operation really enters the absorbing dagger state. -/
private theorem collection_choice_none_dagger
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hnotLater : ReferenceCollectionPhaseHistory.laterChosen x = false)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = none) :
    (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger := by
  classical
  change (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration = .dagger
  by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
    let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
    have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
        .collection payload ledger clock cutoff
          (CoordinatorRoundDispatch.dispatchCollection input) := by
      simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hstate, hcutoff, cutoff, clock, input]
      rfl
    cases hdispatch : CoordinatorRoundDispatch.dispatchCollection input <;>
      simp_all [ReferenceCollectionSegmentExtraction.choice,
        ReferenceCollectionSegmentExtraction.choiceOfCut,
        ReferenceCollectionPhaseHistory.laterChosen,
        ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.coordinatorFailure]
  · have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
        .invalidCollectionCutoff := by
      simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hstate, hcutoff]
    simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
      hprepared, ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.coordinatorFailure]

private theorem endpointState_of_connected
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final) :
    ReferenceCollectionSegmentExtraction.endpointState initial records = final := by
  induction records generalizing initial final with
  | nil => simpa [ReferenceCollectionSegmentExtraction.endpointState] using hchain.symm
  | cons record rest ih =>
      rcases hchain with ⟨hpre, hrest⟩
      simp only [ReferenceCollectionSegmentExtraction.endpointState, List.foldl_cons]
      exact ih record.output.next final hrest

/-- Every selected row in a connected non-later-choice prefix is an actual
completed ordinary collection step. A missing choice, including a failed
pending-empty replacement, would enter dagger and contradict the later
selected endpoint. -/
private theorem connected_collection_prefix_choices
    (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hcontext : ∃ payload ledger proposal,
      initial.coordinator = .collection payload ledger proposal ∧
      CollectionBufferProvenance.collectionContext ledger =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base))
    (hnoLater : ∀ record ∈ records,
      ReferenceCollectionPhaseHistory.laterChosen record.input = false)
    (current : ReferenceActivePhysicalStep.RoundInput p rate)
    (hcurrent : current.state = final)
    (hcurrentChoice : ∃ choice,
      ReferenceCollectionSegmentExtraction.choice current = some choice) :
    ∀ record ∈ records, ∃ choice completed,
      ReferenceCollectionSegmentExtraction.choice record.input = some choice ∧
      choice.initializer = none ∧
      CollectionBufferProvenance.collectionContext choice.preLedger =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base) ∧
      completed.context.initializer = none ∧
      completed.input.round = record.input.time ∧
      completed.input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic record ∧
      ReferenceCollectionSegmentExtraction.extractRound record = some completed := by
  induction records generalizing initial final with
  | nil => intro record hmem; simp at hmem
  | cons record rest ih =>
      rcases hchain with ⟨hpre, hrest⟩
      rcases hcontext with ⟨payload, ledger, proposal, hcoord, hledgerContext⟩
      have hstate : record.input.state.coordinator =
          .collection payload ledger proposal := by
        rw [hpre]
        exact hcoord
      have hnoLaterHead := hnoLater record (by simp)
      cases hchoice : ReferenceCollectionSegmentExtraction.choice record.input with
      | none =>
          have hdagger := collection_choice_none_dagger record.input payload ledger proposal
            hstate hnoLaterHead hchoice
          have hdaggerOutput : record.output.next.coordinator = .dagger := by
            rw [record.output_eq]
            exact hdagger
          have hdaggerTail :=
            ReferenceActivePhysicalHorizon.Connected.coordinator_dagger hrest hdaggerOutput
          have hcurrentDagger : current.state.coordinator = .dagger := by
            rw [hcurrent]
            exact hdaggerTail.1
          have hnone := choice_none_of_dagger current hcurrentDagger
          rcases hcurrentChoice with ⟨choice, hselected⟩
          rw [hnone] at hselected
          contradiction
      | some choice =>
          have hchoicePre := ReferenceCollectionSegmentExtraction.choice_collection_pre
            record.input payload ledger proposal choice hstate hchoice
          have hchoiceContext :
              CollectionBufferProvenance.collectionContext choice.preLedger =
                (initializer.assignment, initializer.sigma, initializer.cutoff,
                  initializer.freezeAt, initializer.base) := by
            rw [hchoicePre.1]
            exact hledgerContext
          have hstep := ReferenceFirstCollectionEpochAlignment.actual_chosen_step_context
            rate record.input choice initializer hchoice hchoiceContext
          rcases hstep with hdagger | ⟨nextLedger, nextProposal, completed,
              hnext, hnextContext, hextract, _, _⟩
          · have hdaggerTail :=
              ReferenceActivePhysicalHorizon.Connected.coordinator_dagger hrest
                (by rw [record.output_eq]; exact hdagger)
            have hcurrentDagger : current.state.coordinator = .dagger := by
              rw [hcurrent]
              exact hdaggerTail.1
            have hnone := choice_none_of_dagger current hcurrentDagger
            rcases hcurrentChoice with ⟨lastChoice, hselected⟩
            rw [hnone] at hselected
            contradiction
          · have hnextContext' :
                ∃ nextPayload nextLedger' nextProposal',
                  record.output.next.coordinator =
                    .collection nextPayload nextLedger' nextProposal' ∧
                  CollectionBufferProvenance.collectionContext nextLedger' =
                    (initializer.assignment, initializer.sigma, initializer.cutoff,
                      initializer.freezeAt, initializer.base) := by
              refine ⟨choice.payload, nextLedger, nextProposal, ?_, hnextContext⟩
              rw [record.output_eq]
              exact hnext
            have hrecordEq := roundRecord_eq_step record
            have hextractRecord :
                ReferenceCollectionSegmentExtraction.extractRound record = some completed := by
              rw [hrecordEq]
              exact hextract
            intro selected hmem
            rcases List.mem_cons.mp hmem with heq | htail
            · subst selected
              have hactual := ReferenceCollectionSegmentExtraction.actual_collection_round_checked
                record completed hextractRecord
              have hcompletedChoice : completed.context = choice :=
                Option.some.inj (hactual.1.symm.trans hchoice)
              have hrawEnabled := ReferenceCollectionRawBufferHistory.actual_completed_input_raw_and_enabled
                record completed hextractRecord
              refine ⟨choice, completed, hchoice, hchoicePre.2, hchoiceContext,
                ?_, hactual.2.1, hrawEnabled.1, hextractRecord⟩
              rw [hcompletedChoice]
              exact hchoicePre.2
            · have hnoLaterTail : ∀ later ∈ rest,
                  ReferenceCollectionPhaseHistory.laterChosen later.input = false := by
                intro later hmemLater
                exact hnoLater later (List.mem_cons_of_mem record hmemLater)
              exact ih record.output.next final hrest hnextContext' hnoLaterTail
                hcurrent selected htail

private theorem takeWhile_eq_self_of_forall
    {α : Type} (predicate : α → Bool) (records : List α)
    (hall : ∀ record ∈ records, predicate record = true) :
    records.takeWhile predicate = records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      have hhead := hall record (by simp)
      have htail : ∀ later ∈ rest, predicate later = true := by
        intro later hmem
        exact hall later (List.mem_cons_of_mem record hmem)
      simp [hhead, ih htail]

private theorem mem_take_subset {α : Type} (records : List α) (count : ℕ)
    {item : α} (hmem : item ∈ records.take count) : item ∈ records := by
  induction records generalizing count with
  | nil => simp at hmem
  | cons head tail ih =>
      cases count with
      | zero => simp at hmem
      | succ count =>
          simp only [List.take_succ_cons, List.mem_cons] at hmem
          rcases hmem with heq | htail
          · exact List.mem_cons.mpr (Or.inl heq)
          · exact List.mem_cons_of_mem head (ih count htail)

private theorem mem_takeWhile_subset {α : Type} (predicate : α → Bool)
    (records : List α) {item : α}
    (hmem : item ∈ records.takeWhile predicate) : item ∈ records := by
  exact List.takeWhile_subset predicate hmem

private theorem mem_take_getElem {α : Type} (records : List α) (count : ℕ)
    {record : α} (hmem : record ∈ records.take count) :
    ∃ index, index < count ∧ ∃ hindex : index < records.length,
      records[index]'hindex = record := by
  obtain ⟨index, hindex, hget⟩ := List.mem_iff_getElem.mp hmem
  have hbounds : index < count ∧ index < records.length := by
    simp only [List.length_take] at hindex
    omega
  refine ⟨index, hbounds.1, ⟨hbounds.2, ?_⟩⟩
  exact (List.getElem_take' hbounds.2 hbounds.1).trans hget

private theorem roundRecord_getElem_eq_tail
    {whole tail : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    {head : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hwhole : whole = head :: tail) (n : Fin whole.length) (hn : n.val ≠ 0) :
    ∃ j : Fin tail.length, j.val + 1 = n.val ∧ whole[n] = tail[j.val] := by
  have hnlt : n.val < tail.length + 1 := by
    have hlen : whole.length = tail.length + 1 := by
      simpa using congrArg List.length hwhole
    omega
  let j : Fin tail.length := ⟨n.val - 1, by omega⟩
  have hj : j.val + 1 = n.val := by
    dsimp [j]
    omega
  have hlookup : whole[n.val]? = some tail[j.val] := by
    calc
      whole[n.val]? = (head :: tail)[n.val]? :=
        congrArg (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
          (p := p) (rate := rate)) => records[n.val]?) hwhole
      _ = (head :: tail)[j.val + 1]? := by rw [hj]
      _ = some tail[j.val] := by simp
  have hget : whole[n.val]? = some whole[n] := by simp [n.isLt]
  exact ⟨j, hj, Option.some.inj (hget.symm.trans hlookup)⟩

private theorem rawDiagnostic_amount_le_D
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (arm : Fin p.K) (amount : ℕ)
    (hdiag : ReferenceCollectionRawBufferHistory.rawDiagnostic record = some (arm, amount)) :
    amount ≤ ConstructorDimensions.D p := by
  unfold ReferenceCollectionRawBufferHistory.rawDiagnostic at hdiag
  cases hrecording : record.output.coordinator.recording with
  | none => simp [hrecording] at hdiag
  | some output =>
      cases hgate : output.gateArm with
      | none => simp [hrecording, hgate] at hdiag
      | some recordedArm =>
          have hpair : (recordedArm, output.rawArrival) = (arm, amount) := by
            simpa [hrecording, hgate] using hdiag
          have hamount := congrArg Prod.snd hpair
          have hamount' : output.rawArrival = amount := by simpa using hamount
          rw [← hamount']
          exact output.rawArrival_le_D

private theorem findRoundInput_eq_physicalFind
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hgood : ∀ record ∈ records, ∃ completed,
      ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
      completed.input.round = record.input.time ∧
      completed.input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic record)
    (round : Fin p.T) :
    CollectionBufferProvenance.findRoundInput?
        (ReferenceCollectionSegmentExtraction.inputs records) round =
      (findPhysicalRecord? records round).bind fun record =>
        (ReferenceCollectionSegmentExtraction.extractRound record).map
          fun completed => completed.input := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      rcases hgood record (by simp) with
        ⟨completed, hextract, hround, hraw⟩
      have htail : ∀ later ∈ rest, ∃ done,
          ReferenceCollectionSegmentExtraction.extractRound later = some done ∧
          done.input.round = later.input.time ∧
          done.input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic later := by
        intro later hmem
        exact hgood later (List.mem_cons_of_mem record hmem)
      have hinputs : ReferenceCollectionSegmentExtraction.inputs (record :: rest) =
          completed.input :: ReferenceCollectionSegmentExtraction.inputs rest := by
        simp [ReferenceCollectionSegmentExtraction.inputs,
          ReferenceCollectionSegmentExtraction.completed, hextract]
      by_cases htime : record.input.time = round
      · have hroundEq : completed.input.round = round := hround.trans htime
        simp [CollectionBufferProvenance.findRoundInput?, findPhysicalRecord?,
          hinputs, htime, hroundEq, hextract]
      · have hroundNe : completed.input.round ≠ round := by
          intro heq
          exact htime (hround.symm.trans heq)
        have hih := ih htail
        simpa [CollectionBufferProvenance.findRoundInput?, findPhysicalRecord?,
          hinputs, htime, hroundNe] using hih

private theorem supplied_cell_eq_physical_cell
    (initial : Fin p.K → Fin p.T → Option ℕ)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (freezeAt : ℕ) (arm : Fin p.K) (round : Fin p.T)
    (hempty : ∀ a r, initial a r = none)
    (hgood : ∀ record ∈ records, ∃ completed,
      ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
      completed.input.round = record.input.time ∧
      completed.input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic record) :
    CollectionBufferProvenance.suppliedRawBufferCell initial
        (ReferenceCollectionSegmentExtraction.inputs records) freezeAt arm round =
      physicalRawCell records freezeAt arm round := by
  unfold CollectionBufferProvenance.suppliedRawBufferCell
  rw [findRoundInput_eq_physicalFind records hgood round]
  cases hfind : findPhysicalRecord? records round with
  | none => simp [physicalRawCell, hfind, hempty]
  | some record =>
      have hrecordMem : record ∈ records := by
        exact List.mem_of_find?_eq_some (by simpa [findPhysicalRecord?] using hfind)
      have hfindList : List.find? (fun record => decide (record.input.time = round)) records =
          some record := by
        simpa [findPhysicalRecord?] using hfind
      have hfindSpec : decide (record.input.time = round) = true := by
        simpa [findPhysicalRecord?] using List.find?_some hfind
      have htime : record.input.time = round := of_decide_eq_true hfindSpec
      rcases hgood record hrecordMem with ⟨completed, hextract, hround, hraw⟩
      cases hdiag : ReferenceCollectionRawBufferHistory.rawDiagnostic record with
      | none =>
          have : completed.input.raw = none := by rw [hraw, hdiag]
          simp [physicalRawCell, findPhysicalRecord?, hfindList, hextract, hdiag, this,
            hempty]
      | some pair =>
          rcases pair with ⟨recordedArm, amount⟩
          have hrawInput : completed.input.raw = some (recordedArm, amount) := by
            rw [hraw, hdiag]
          simp [physicalRawCell, findPhysicalRecord?, hfindList, hextract, hdiag, hrawInput,
            CoordinatorCollectionLedger.sourceRound, hempty]

private theorem physicalRawCell_some_spec
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (freezeAt : ℕ) (arm : Fin p.K) (round : Fin p.T) (amount : ℕ)
    (hcell : physicalRawCell records freezeAt arm round = some amount) :
    ∃ record ∈ records, record.input.time = round ∧
      ∃ recordedArm,
        ReferenceCollectionRawBufferHistory.rawDiagnostic record =
          some (recordedArm, amount) ∧ recordedArm = arm ∧
        0 < amount ∧ round.val + 1 < freezeAt := by
  unfold physicalRawCell at hcell
  cases hfind : findPhysicalRecord? records round with
  | none => simp [hfind] at hcell
  | some record =>
      have hrecordMem : record ∈ records := by
        exact List.mem_of_find?_eq_some (by simpa [findPhysicalRecord?] using hfind)
      have hfindList : List.find? (fun record => decide (record.input.time = round)) records =
          some record := by
        simpa [findPhysicalRecord?] using hfind
      have htime : record.input.time = round := by
        have hpred : decide (record.input.time = round) = true := by
          simpa [findPhysicalRecord?] using List.find?_some hfind
        exact of_decide_eq_true hpred
      rw [hfind] at hcell
      cases hdiag : ReferenceCollectionRawBufferHistory.rawDiagnostic record with
      | none => simp [hdiag] at hcell
      | some pair =>
          rcases pair with ⟨recordedArm, foundAmount⟩
          by_cases hcondition : recordedArm = arm ∧ 0 < foundAmount ∧
              round.val + 1 < freezeAt
          · simp [hdiag, hcondition] at hcell
            cases hcell
            exact ⟨record, hrecordMem, htime, recordedArm, hdiag,
              hcondition.1, hcondition.2.1, hcondition.2.2⟩
          · simp [hdiag, hcondition] at hcell

private theorem rawCell_support_and_future_freshness
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (records W : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (n : Fin W.length) (start windowLength freezeAt : ℕ)
    (hprefix : records = W.take n.val)
    (hraw : ∀ arm round,
      ledger.rawBuffer arm round =
        if ledger.currentRegisters arm = none then physicalRawCell records freezeAt arm round
        else none)
    (htime : ∀ i (hi : i < W.length),
      W[i].input.time.val = start + windowLength + i) :
    (∀ arm round amount, ledger.rawBuffer arm round = some amount →
      start + windowLength + 1 ≤ round.val + 1 ∧
      round.val + 1 < start + windowLength + 1 + n.val ∧
      round.val + 1 < freezeAt ∧ 0 < amount ∧ amount ≤ ConstructorDimensions.D p) ∧
    (∀ arm, ledger.rawBuffer arm W[n].input.time = none) := by
  have hcurrentTime := htime n.val n.isLt
  have hcurrentTime' : W[n].input.time.val = start + windowLength + n.val := by
    simpa using hcurrentTime
  have hnoMatch : ∀ record ∈ records, record.input.time ≠ W[n].input.time := by
    intro record hmem
    rw [hprefix] at hmem
    obtain ⟨i, hi, hiW, hrecord⟩ := mem_take_getElem W n.val hmem
    have htimeIndex := htime i hiW
    rw [hrecord] at htimeIndex
    intro heq
    have heqVal := congrArg Fin.val heq
    rw [htimeIndex, hcurrentTime'] at heqVal
    omega
  refine ⟨?_, ?_⟩
  · intro arm round amount hcell
    have hformula := hraw arm round
    rw [hformula] at hcell
    by_cases hknown : ledger.currentRegisters arm ≠ none
    · simp [hknown] at hcell
    · have hunknown : ledger.currentRegisters arm = none := by
        cases hreg : ledger.currentRegisters arm with
        | none => rfl
        | some value => exact False.elim (hknown (by simp [hreg]))
      simp [hunknown] at hcell
      obtain ⟨record, hmem, htimeRecord, recordedArm, hdiag,
        harm, hpositive, hbeforeFreeze⟩ :=
          physicalRawCell_some_spec records freezeAt arm round amount hcell
      obtain ⟨i, hi, hiW, hrecordAt⟩ := mem_take_getElem W n.val (by simpa [hprefix] using hmem)
      have htimeRound := htime i hiW
      rw [hrecordAt] at htimeRound
      have htimePhysical : round.val = record.input.time.val :=
        congrArg Fin.val htimeRecord.symm
      have hamountBound := rawDiagnostic_amount_le_D record recordedArm amount hdiag
      refine ⟨?_, ?_, hbeforeFreeze, hpositive, hamountBound⟩
      · omega
      · omega
  · intro arm
    let currentTime := W[n].input.time
    have hformula := hraw arm currentTime
    change ledger.rawBuffer arm currentTime = none
    rw [hformula]
    by_cases hknown : ledger.currentRegisters arm ≠ none
    · simp [hknown]
    · have hunknown : ledger.currentRegisters arm = none := by
        cases hreg : ledger.currentRegisters arm with
        | none => rfl
        | some value => exact False.elim (hknown (by simp [hreg]))
      simp only [hunknown, ↓reduceIte]
      exact physicalRawCell_eq_none_of_no_match records freezeAt arm currentTime
        (by simpa [currentTime] using hnoMatch)

private theorem startRoundCandidate_known_raw_column
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (round : Fin p.T)
    (enabled : Bool) (raw : Option (Fin p.K × ℕ)) (arm : Fin p.K)
    (hknown : ledger.currentRegisters arm ≠ none) :
    ∀ r, (CoordinatorCollectionLedger.startRoundCandidate ledger round enabled raw).rawBuffer arm r =
      ledger.rawBuffer arm r := by
  cases raw with
  | none => intro r; rfl
  | some pair =>
      rcases pair with ⟨recordedArm, amount⟩
      by_cases hwrite : ledger.currentRegisters recordedArm = none ∧
          0 < amount ∧ CoordinatorCollectionLedger.sourceRound round < ledger.freezeAt
      · have harm : recordedArm ≠ arm := by
          intro heq
          subst recordedArm
          exact hknown hwrite.1
        intro r
        have hput := CoordinatorCollectionLedger.putRaw_other ledger.rawBuffer
          recordedArm arm round r amount (Or.inl (Ne.symm harm))
        simpa [CoordinatorCollectionLedger.startRoundCandidate, hwrite, harm] using hput
      · intro r
        simp [CoordinatorCollectionLedger.startRoundCandidate, hwrite]

private theorem startRound_success_known_raw_column
    (ledger started : ReferenceActivePhysicalStep.Ledger rate)
    (round : Fin p.T) (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (arm : Fin p.K)
    (hstart : CoordinatorCollectionLedger.startRound ledger
      (CoordinatorCollectionLedger.sourceRound round) enabled raw = .success started)
    (hknown : ledger.currentRegisters arm ≠ none) :
    ∀ r, started.rawBuffer arm r = ledger.rawBuffer arm r := by
  have hcand := CollectionCheckedExecution.startRound_success_candidate
    ledger started (CoordinatorCollectionLedger.sourceRound round) enabled raw hstart
  have hindex :
      (⟨CoordinatorCollectionLedger.sourceRound round - 1, by
        simp [CoordinatorCollectionLedger.sourceRound]⟩ : Fin p.T) = round := by
    apply Fin.ext
    simp [CoordinatorCollectionLedger.sourceRound]
  intro r
  rw [hcand, hindex]
  exact startRoundCandidate_known_raw_column ledger round enabled raw arm hknown r

private theorem startRound_success_preserves_known_raw_empty
    (ledger started : ReferenceActivePhysicalStep.Ledger rate)
    (round : Fin p.T) (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (arm : Fin p.K)
    (hstart : CoordinatorCollectionLedger.startRound ledger
      (CoordinatorCollectionLedger.sourceRound round) enabled raw = .success started)
    (hinvariant : knownRawColumnEmpty ledger arm) :
    knownRawColumnEmpty started arm := by
  intro hknownStarted r
  have hcand := CollectionCheckedExecution.startRound_success_candidate
    ledger started (CoordinatorCollectionLedger.sourceRound round) enabled raw hstart
  have hknownLedger : ledger.currentRegisters arm ≠ none := by
    intro hnone
    rw [hcand] at hknownStarted
    exact hknownStarted (by simp [CoordinatorCollectionLedger.startRoundCandidate, hnone])
  calc
    started.rawBuffer arm r = ledger.rawBuffer arm r :=
      startRound_success_known_raw_column ledger started round enabled raw arm hstart
        hknownLedger r
    _ = none := hinvariant hknownLedger r

private theorem decodeUp_success_none_fields
    (ledger result : ReferenceActivePhysicalStep.Ledger rate)
    (follower : Fin (p.m - 1))
    (hdecode : CoordinatorCollectionLedger.decodeUp ledger follower none = .success result) :
    result.currentRegisters = ledger.currentRegisters ∧ result.rawBuffer = ledger.rawBuffer := by
  by_cases hinput : CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧
      ledger.phase = .started ∧ 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ ledger.cursor ∧
      ledger.cursor ≤ p.T
  · let next : ReferenceActivePhysicalStep.Ledger rate := { ledger with phase := .decoded }
    by_cases hvalid : CoordinatorCollectionLedger.validLedgerCheck next = true
    · have heq : result = next := by
        have h' : (some result : Option (ReferenceActivePhysicalStep.Ledger rate)) =
            some next := by
          simpa [CoordinatorCollectionLedger.decodeUp, hinput, next, hvalid] using hdecode
        exact Option.some.inj h'
      subst result
      exact ⟨rfl, rfl⟩
    · simp [CoordinatorCollectionLedger.decodeUp, hinput, next, hvalid] at hdecode
  · simp [CoordinatorCollectionLedger.decodeUp, hinput] at hdecode

private theorem decodeUp_success_preserves_known_raw_empty
    (ledger result : ReferenceActivePhysicalStep.Ledger rate)
    (follower : Fin (p.m - 1)) (parsed : Option
      (OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (arm : Fin p.K)
    (hinvariant : knownRawColumnEmpty ledger arm)
    (hdecode : CoordinatorCollectionLedger.decodeUp ledger follower parsed = .success result) :
    knownRawColumnEmpty result arm := by
  intro hknown
  cases parsed with
  | none =>
      rcases decodeUp_success_none_fields ledger result follower hdecode with
        ⟨hregisters, hbuffer⟩
      have hknownLedger : ledger.currentRegisters arm ≠ none := by
        rw [hregisters] at hknown
        exact hknown
      intro r
      rw [hbuffer]
      exact hinvariant hknownLedger r
  | some message =>
      rcases CollectionCheckedExecution.decodeUp_success_candidate ledger result follower
          message hdecode with
        ⟨hbound, lastIndex, hlast, past, current, hpast, hcurrent, hunknownAccepted,
          hcandidate⟩
      have hknownCandidate :
          (CoordinatorCollectionLedger.acceptUpCandidate ledger follower message past current).currentRegisters arm ≠ none := by
        rw [← hcandidate]
        exact hknown
      cases hbefore : ledger.currentRegisters arm with
      | some currentRegister =>
          have hnotAcceptedArm : ledger.assignment.arm follower ≠ arm := by
            intro heq
            subst arm
            exact (Option.some_ne_none currentRegister)
              (hbefore.symm.trans hunknownAccepted)
          intro r
          have hclear := CoordinatorCollectionLedger.clearRawArm_other ledger.rawBuffer
            (ledger.assignment.arm follower) arm r (Ne.symm hnotAcceptedArm)
          calc
            result.rawBuffer arm r =
                (CoordinatorCollectionLedger.acceptUpCandidate ledger follower message
                  past current).rawBuffer arm r := by rw [hcandidate]
            _ = CoordinatorCollectionLedger.clearRawArm ledger.rawBuffer
                (ledger.assignment.arm follower) arm r := rfl
            _ = ledger.rawBuffer arm r := hclear
            _ = none := hinvariant (by simp [hbefore]) r
      | none =>
          have hassignment : ledger.assignment.arm follower = arm := by
            by_contra hne
            have hnone :
                (CoordinatorCollectionLedger.acceptUpCandidate ledger follower message
                  past current).currentRegisters arm = none := by
              change Function.update ledger.currentRegisters
                (ledger.assignment.arm follower) _ arm = none
              rw [Function.update_of_ne (Ne.symm hne)]
              exact hbefore
            exact hknownCandidate hnone
          intro r
          calc
            result.rawBuffer arm r =
                (CoordinatorCollectionLedger.acceptUpCandidate ledger follower message
                  past current).rawBuffer arm r := by rw [hcandidate]
            _ = none := by
              simp [CoordinatorCollectionLedger.acceptUpCandidate, hassignment,
                CoordinatorCollectionLedger.clearRawArm]

private theorem decodeUp_rejected_preserves_known_raw_empty
    (ledger result : ReferenceActivePhysicalStep.Ledger rate)
    (follower : Fin (p.m - 1)) (parsed : Option
      (OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)))
    (arm : Fin p.K)
    (hinvariant : knownRawColumnEmpty ledger arm)
    (hdecode : CoordinatorCollectionLedger.decodeUp ledger follower parsed = .rejected result) :
    knownRawColumnEmpty result arm := by
  intro hknown
  have hfields := CollectionBufferProvenance.decodeUp_rejected_preserves_arm
    ledger result follower parsed arm hdecode
  have hknownLedger : ledger.currentRegisters arm ≠ none := by
    intro hnone
    rw [hfields.1] at hknown
    exact hknown hnone
  intro r
  rw [hfields.2]
  exact hinvariant hknownLedger r

private theorem finishRound_success_preserves_known_raw_empty
    (ledger result : ReferenceActivePhysicalStep.Ledger rate) (arm : Fin p.K)
    (hinvariant : knownRawColumnEmpty ledger arm)
    (hfinish : CoordinatorCollectionLedger.finishRound ledger = .success result) :
    knownRawColumnEmpty result arm := by
  intro hknown r
  have hcand := CollectionCheckedExecution.finishRound_success_candidate ledger result hfinish
  rw [hcand] at hknown ⊢
  simpa [CoordinatorCollectionLedger.finishRoundCandidate] using hinvariant hknown r

private theorem checkedRounds_preserves_known_raw_empty
    (initial final : ReferenceActivePhysicalStep.Ledger rate)
    (inputs : List (CollectionCheckedExecution.RoundInput
      (p := p) (eta := rate.eta.val))) (accepted : List Bool)
    (arm : Fin p.K) (hinvariant : knownRawColumnEmpty initial arm)
    (hfold : CollectionCheckedExecution.checkedRounds initial inputs =
      some (accepted, final)) : knownRawColumnEmpty final arm := by
  induction inputs generalizing initial accepted final with
  | nil =>
      simp [CollectionCheckedExecution.checkedRounds] at hfold
      rcases hfold with ⟨rfl, rfl⟩
      exact hinvariant
  | cons input rest ih =>
      cases hstart : CoordinatorCollectionLedger.startRound initial
          (CoordinatorCollectionLedger.sourceRound input.round) input.enabled input.raw with
      | invalid => simp [CollectionCheckedExecution.checkedRounds, hstart] at hfold
      | rejected bad => simp [CollectionCheckedExecution.checkedRounds, hstart] at hfold
      | success started =>
          cases hdecode : CoordinatorCollectionLedger.decodeUp started
              input.selectedFollower input.parsed with
          | invalid => simp [CollectionCheckedExecution.checkedRounds, hstart, hdecode] at hfold
          | rejected decoded =>
              cases hfinish : CoordinatorCollectionLedger.finishRound decoded with
              | invalid => simp [CollectionCheckedExecution.checkedRounds, hstart, hdecode,
                  hfinish] at hfold
              | rejected bad => simp [CollectionCheckedExecution.checkedRounds, hstart,
                  hdecode, hfinish] at hfold
              | success finished =>
                  cases hrest : CollectionCheckedExecution.checkedRounds finished rest with
                  | none => simp [CollectionCheckedExecution.checkedRounds, hstart,
                      hdecode, hfinish, hrest] at hfold
                  | some pair =>
                      simp only [CollectionCheckedExecution.checkedRounds, hstart, hdecode,
                        hfinish, hrest, Option.some.injEq, Prod.mk.injEq,
                        List.cons.injEq, and_true] at hfold
                      rcases hfold with ⟨rfl, rfl⟩
                      have hstartInvariant := startRound_success_preserves_known_raw_empty
                        initial started input.round input.enabled input.raw arm hstart hinvariant
                      have hdecodeInvariant := decodeUp_rejected_preserves_known_raw_empty
                        started decoded input.selectedFollower input.parsed arm
                        hstartInvariant hdecode
                      have hfinishInvariant := finishRound_success_preserves_known_raw_empty
                        decoded finished arm hdecodeInvariant hfinish
                      exact ih finished pair.2 pair.1 hfinishInvariant hrest
          | success decoded =>
              cases hfinish : CoordinatorCollectionLedger.finishRound decoded with
              | invalid => simp [CollectionCheckedExecution.checkedRounds, hstart, hdecode,
                  hfinish] at hfold
              | rejected bad => simp [CollectionCheckedExecution.checkedRounds, hstart,
                  hdecode, hfinish] at hfold
              | success finished =>
                  cases hrest : CollectionCheckedExecution.checkedRounds finished rest with
                  | none => simp [CollectionCheckedExecution.checkedRounds, hstart,
                      hdecode, hfinish, hrest] at hfold
                  | some pair =>
                      simp only [CollectionCheckedExecution.checkedRounds, hstart, hdecode,
                        hfinish, hrest, Option.some.injEq, Prod.mk.injEq,
                        List.cons.injEq, and_true] at hfold
                      rcases hfold with ⟨rfl, rfl⟩
                      have hstartInvariant := startRound_success_preserves_known_raw_empty
                        initial started input.round input.enabled input.raw arm hstart hinvariant
                      have hdecodeInvariant := decodeUp_success_preserves_known_raw_empty
                        started decoded input.selectedFollower input.parsed arm
                        hstartInvariant hdecode
                      have hfinishInvariant := finishRound_success_preserves_known_raw_empty
                        decoded finished arm hdecodeInvariant hfinish
                      exact ih finished pair.2 pair.1 hfinishInvariant hrest
/-! The theorem below is the actual source-facing prefix result. It keeps the
whole chosen-context result as a conclusion, so the selected choice, original
arrays, initializer and actual ledger assignment remain attached to the raw
cell statement. -/

/-- Every pre-reception raw cell of an actual selected input is the literal
Option-valued result of searching the preceding physical rows. -/
theorem actual_first_collection_raw_cells (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (n : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length).length)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length)[n].input = some c) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    let Pn := W.take n.val
    let u := start + w + 1
    let v := u + n.val
    let g := c.preLedger.freezeAt
    (∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
        (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
        (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
        (base : Fin (p.m - 1) → ℕ)
        (c0 : ReferenceCollectionSegmentExtraction.Choice rate)
        (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
        (seg : ReferenceCollectionSegmentExtraction.Segment rate),
      execution.records = firstWindow ++ cut :: suffix ∧
      cut.input.time.val = start + w ∧ c0.payload = r.payload ∧
      initializer = ReferenceCollectionSegmentExtraction.cutoffInitializer
        (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
        (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base
        (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time ∧
      ReferenceCollectionSegmentExtraction.segmentAt execution.records w = some seg ∧
      seg.entry = cut ∧ seg.context = c0 ∧
      ReferenceCollectionSegmentExtraction.choice cut.input = some c0 ∧
      c0.initializer = some initializer ∧ initializer.checkedStart rate = .success c0.preLedger ∧
      initializer.sigma = start + 1 ∧ initializer.cutoff = start + w + 1 ∧
      initializer.freezeAt = r.gridBoundary ∧
      initializer.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val c0.payload.sigma ∧
      initializer.base = (fun _ => 0) ∧
      initializer.assignment.arm = r.payload.assignment.assigned ∧
      initializer.assignment.arm = c0.payload.assignment.assigned ∧
      0 < w ∧ c.payload = c0.payload ∧
      CollectionBufferProvenance.collectionContext c.preLedger =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base) ∧
      W[n].input.time.val = start + w + n.val) ∧
      (∀ a r, c.preLedger.rawBuffer a r =
        if c.preLedger.currentRegisters a = none then physicalRawCell Pn g a r else none) ∧
      (∀ a, c.preLedger.currentRegisters a ≠ none →
        ∀ r, c.preLedger.rawBuffer a r = none) ∧
      (∀ record ∈ Pn, ∃ completed,
        ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
        completed.input.round = record.input.time ∧
        completed.input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic record) ∧
      (∀ left ∈ Pn, ∀ right ∈ Pn,
        left.input.time = right.input.time → left = right) ∧
      (∀ a r amount, c.preLedger.rawBuffer a r = some amount →
        u ≤ r.val + 1 ∧ r.val + 1 < v ∧ r.val + 1 < g ∧
        0 < amount ∧ amount ≤ ConstructorDimensions.D p) ∧
      (∀ a, c.preLedger.rawBuffer a W[n].input.time = none) := by
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  let Pn := W.take n.val
  let u := start + w + 1
  let v := u + n.val
  let g := c.preLedger.freezeAt
  have hctx := ReferenceFirstCollectionChosenContext.actual_first_collection_chosen_context
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice
  have hctxOriginal := hctx
  rcases hctx with ⟨cut, suffix, r, q, base, c0, initializer, seg,
    hsplit, hcutTime, hcutPayload, hcutInitializer, hsegmentAt, hentry,
    hsegContext, hcutChoice, hc0Initializer, hchecked, hSigma, hCutoff,
    hfreeze, hfreezeGrid, hbase, hassignment, hassignmentC0, hwpos,
    hcurrentPayload, hcontext, hcurrentTime⟩
  have hstart : CoordinatorCollectionLedger.startCollectionChecked p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate) rate.n
      rate.n_scale initializer.assignment initializer.sigma initializer.cutoff
      initializer.freezeAt initializer.base initializer.outside = .success c0.preLedger := by
    simpa [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hchecked
  have hinitEmpty := CollectionBufferProvenance.startCollectionChecked_success_empty_rawBuffer
    initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
    initializer.base initializer.outside c0.preLedger hstart
  have hstartFields := CollectionBufferProvenance.startCollectionChecked_success_context
    initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
    initializer.base initializer.outside c0.preLedger hstart
  have hcutContext : CollectionBufferProvenance.collectionContext c0.preLedger =
      (initializer.assignment, initializer.sigma, initializer.cutoff,
        initializer.freezeAt, initializer.base) := by
    simp [CollectionBufferProvenance.collectionContext, hstartFields.1,
      hstartFields.2.1, hstartFields.2.2.2.1,
      hstartFields.2.2.2.2.1, hstartFields.2.2.2.2.2]
  have hcontextEq : CollectionBufferProvenance.collectionContext c0.preLedger =
      CollectionBufferProvenance.collectionContext c.preLedger :=
    hcutContext.trans hcontext.symm
  have hfreezeEq : c0.preLedger.freezeAt = c.preLedger.freezeAt := by
    have h := congrArg (fun fields => fields.2.2.2.1) hcontextEq
    change c0.preLedger.freezeAt = c.preLedger.freezeAt at h
    exact h
  have hsplit' : execution.records = firstWindow ++ cut :: suffix := by
    simpa [execution, firstWindow] using hsplit
  have hdrop : execution.records.drop w = cut :: suffix := by
    rw [hsplit']
    simp [w, firstWindow]
  have hdropNext : execution.records.drop (w + 1) = suffix := by
    rw [hsplit']
    simp [w, firstWindow]
  let during := suffix.takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hwindow : W = cut :: during := by
    dsimp [W, ReferenceCollectionPhaseHistory.collectionWindow, during]
    rw [hdrop, hdropNext]
    simp
  have htimes := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
    rate source rewards C_star C_h count hcross hspan hshort
  have hwindowTime : ∀ i (hi : i < W.length),
      W[i].input.time.val = start + w + i := by
    intro i hi
    let index : Fin W.length := ⟨i, hi⟩
    have htimeIndex := (htimes index).2
    have htimeIndex' : W[index].input.time.val + 1 =
        start + w + 1 + index.val := by
      simpa [W, w, firstWindow, execution, start] using htimeIndex
    have hindex : index.val = i := rfl
    have hrowIndexNat : W[index.val] = W[i] :=
      getElem_congr_idx hindex
    have hrowIndex : W[index] = W[i] := by
      simpa using hrowIndexNat
    rw [hrowIndex] at htimeIndex'
    omega
  have hcurrentTime' : W[n].input.time.val = start + w + n.val :=
    hwindowTime n.val n.isLt
  have hmode :=
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
  have hfull : ReferenceActivePhysicalHorizon.Connected
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
      execution.records execution.finalState := by
    simpa [execution, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      ReferenceActivePhysicalHorizon.run_connected
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start count hspan hmode
  have hsplitChain : ReferenceActivePhysicalHorizon.Connected
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
      (firstWindow ++ cut :: suffix) execution.finalState := by
    rw [← hsplit']
    exact hfull
  obtain ⟨afterWindow, hfirstChain, hcutChain⟩ :=
    connected_append_split firstWindow (cut :: suffix) hsplitChain
  rcases hcutChain with ⟨hcutPre, hafterCut⟩
  by_cases hnzero : n.val = 0
  · have hrowOpt : W[n.val]? = some cut := by
      rw [hwindow]
      simp [hnzero]
    have hget : W[n.val]? = some W[n] := by simp [n.isLt]
    have hrow : W[n] = cut := Option.some.inj (hget.symm.trans hrowOpt)
    have hcEq : c = c0 := by
      apply Option.some.inj
      calc
        some c = ReferenceCollectionSegmentExtraction.choice W[n].input := hchoice.symm
        _ = ReferenceCollectionSegmentExtraction.choice cut.input := by rw [hrow]
        _ = some c0 := hcutChoice
    subst c
    have hprefix : W.take n.val = [] := by simp [hnzero]
    have hprefixExpanded : List.take n.val
        (ReferenceCollectionPhaseHistory.collectionWindow execution.records w) = [] := by
      simpa [W] using hprefix
    refine ⟨hctxOriginal, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a round
      by_cases hunknown : c0.preLedger.currentRegisters a = none
      · rw [hinitEmpty a round, if_pos hunknown]
        rw [hprefixExpanded]
        simp [physicalRawCell, findPhysicalRecord?]
      · rw [hinitEmpty a round, if_neg hunknown]
    · intro a hknown round
      exact hinitEmpty a round
    · intro record hmem
      change record ∈ W.take n.val at hmem
      rw [hprefix] at hmem
      simp at hmem
    · intro left hleft right hright htime
      change left ∈ W.take n.val at hleft
      rw [hprefix] at hleft
      simp at hleft
    · intro a round amount hcell
      rw [hinitEmpty a round] at hcell
      cases hcell
    · intro a
      exact hinitEmpty a _
  · let j : Fin during.length := ⟨n.val - 1, by
      have hnlt : n.val < during.length + 1 := by
        have hnltW : n.val < W.length := n.isLt
        rw [hwindow] at hnltW
        simpa only [List.length_cons] using hnltW
      omega⟩
    have hj : j.val + 1 = n.val := by dsimp [j]; omega
    obtain ⟨j', hj', hrow⟩ := roundRecord_getElem_eq_tail hwindow n hnzero
    have hjEq : j' = j := by
      apply Fin.ext
      dsimp [j] at *
      omega
    subst j'
    let currentRecord := during[j.val]
    have hcurrentChoice :
        ReferenceCollectionSegmentExtraction.choice currentRecord.input = some c := by
      have h := hchoice
      rw [hrow] at h
      simpa [currentRecord] using h
    let before := during.take j.val
    let after := during.drop (j.val + 1)
    have htake : during.take (j.val + 1) = before ++ [currentRecord] := by
      dsimp [before, currentRecord]
      rw [(List.take_append_getElem j.isLt).symm]
    have hsplitDuring : during = before ++ currentRecord :: after := by
      calc
        during = during.take (j.val + 1) ++ during.drop (j.val + 1) :=
          (List.take_append_drop (j.val + 1) during).symm
        _ = (before ++ [currentRecord]) ++ after := by
          rw [htake]
        _ = before ++ currentRecord :: after := by simp
    let remainder := suffix.dropWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    have hsuffixSplit : suffix = during ++ remainder := by
      dsimp [during, remainder]
      exact List.takeWhile_append_dropWhile.symm
    have hafterCutOriginal := hafterCut
    rw [hsuffixSplit] at hafterCut
    obtain ⟨afterDuring, hDuringChain, hafterDuring⟩ :=
      connected_append_split during remainder hafterCut
    have hcutChain' : ReferenceActivePhysicalHorizon.Connected
        cut.output.next (before ++ currentRecord :: after) afterDuring := by
      rw [← hsplitDuring]
      exact hDuringChain
    obtain ⟨middle, hbeforeChain, hcurrentChain⟩ :=
      connected_append_split before (currentRecord :: after) hcutChain'
    rcases hcurrentChain with ⟨hcurrentPre, hcurrentTail⟩
    have hbeforeToCurrent : ReferenceActivePhysicalHorizon.Connected
        cut.output.next before currentRecord.input.state := by
      rw [hcurrentPre]
      exact hbeforeChain
    have hnoLaterDuring : ∀ record ∈ during,
        ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
      intro record hmem
      have hall : (!ReferenceCollectionPhaseHistory.laterChosen record.input) = true :=
        (List.all_eq_true.mp List.all_takeWhile) record hmem
      cases hlater : ReferenceCollectionPhaseHistory.laterChosen record.input <;>
        simp [hlater] at hall ⊢
    have hnoLaterBefore : ∀ record ∈ before,
        ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
      intro record hmem
      exact hnoLaterDuring record (mem_take_subset during j.val hmem)
    have hcutChoiceLocal :=
      ReferenceFirstCollectionEpochAlignment.actual_chosen_step_context
        rate cut.input c0 initializer hcutChoice hcutContext
    have hnoCutDagger :
        (ReferenceActivePhysicalStep.step cut.input).next.coordinator ≠ .dagger := by
      intro hdagger
      have hdaggerState : cut.output.next.coordinator = .dagger := by
        rw [cut.output_eq]
        exact hdagger
      obtain ⟨_, hdaggerRows⟩ :=
        ReferenceActivePhysicalHorizon.Connected.coordinator_dagger hafterCutOriginal hdaggerState
      have hrowMemSuffix : currentRecord ∈ suffix :=
        mem_takeWhile_subset _ _ (List.getElem_mem j.isLt)
      have hrowDagger := hdaggerRows currentRecord hrowMemSuffix
      have hnone := choice_none_of_dagger currentRecord.input hrowDagger
      rw [hcurrentChoice] at hnone
      contradiction
    rcases hcutChoiceLocal with hdagger | ⟨ledgerCut, proposalCut, completedCut,
        hcutNextStep, hledgerCutContext, hcutExtractStep, hcompletedContext,
        hcompletedTime⟩
    · exact False.elim (hnoCutDagger hdagger)
    · have hcutNext : cut.output.next.coordinator =
          .collection c0.payload ledgerCut proposalCut := by
        simpa only [cut.output_eq, hcutChoice] using hcutNextStep
      have hcutRecordExtract : ReferenceCollectionSegmentExtraction.extractRound cut =
          some completedCut := by
        rw [roundRecord_eq_step cut]
        exact hcutExtractStep
      have hcutActual := ReferenceCollectionSegmentExtraction.actual_collection_round_checked
        cut completedCut hcutRecordExtract
      have hcutCompletedChoice : completedCut.context = c0 :=
        Option.some.inj (hcutActual.1.symm.trans hcutChoice)
      have hcutOne : CollectionCheckedExecution.checkedRounds c0.preLedger
          [completedCut.input] = some ([completedCut.accepted], completedCut.final) := by
        simpa [hcutCompletedChoice] using hcutActual.2.2.1
      have hcutFinalLedger : ledgerCut = completedCut.final := by
        rcases hcutActual.2.2.2 with ⟨payloadEnd, proposalEnd, hendpoint⟩
        have hconfig :
            ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
                c0.payload ledgerCut proposalCut =
              ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
                payloadEnd completedCut.final proposalEnd := by
          calc
            _ = cut.output.next.coordinator := hcutNext.symm
            _ = _ := hendpoint
        injection hconfig with _ hledger _
      have hcutRaw := ReferenceCollectionRawBufferHistory.actual_completed_input_raw_and_enabled
        cut completedCut hcutRecordExtract
      have hcurrentChoiceFull : ∃ selected,
          ReferenceCollectionSegmentExtraction.choice currentRecord.input = some selected :=
        ⟨c, hcurrentChoice⟩
      have hprior := connected_collection_prefix_choices initializer before
        cut.output.next currentRecord.input.state hbeforeToCurrent
        ⟨c0.payload, ledgerCut, proposalCut, hcutNext, hledgerCutContext⟩
        hnoLaterBefore currentRecord.input rfl hcurrentChoiceFull
      have hbeforeContinuing : ∀ record ∈ before,
          ReferenceCollectionSegmentExtraction.continuing record = true := by
        intro record hmem
        rcases hprior record hmem with ⟨selected, completed, hselected,
          _, _, hcompletedInit, _, _, hextract⟩
        simp [ReferenceCollectionSegmentExtraction.continuing, hextract, hcompletedInit]
      have hbeforeTake : before.takeWhile ReferenceCollectionSegmentExtraction.continuing = before :=
        takeWhile_eq_self_of_forall ReferenceCollectionSegmentExtraction.continuing
          before hbeforeContinuing
      have hcheckedBefore := ReferenceCollectionSegmentExtraction.continuing_checked
        before cut.output.next currentRecord.input.state c0.payload ledgerCut proposalCut
        hbeforeToCurrent hcutNext
      rw [hbeforeTake] at hcheckedBefore
      rcases hcheckedBefore with ⟨hfoldBefore, hendpointCollection⟩
      have hendpointState := endpointState_of_connected cut.output.next
        currentRecord.input.state before hbeforeToCurrent
      rcases hendpointCollection with ⟨payloadEnd, proposalEnd, hendpointCollection⟩
      have hcurrentStateCollection : currentRecord.input.state.coordinator =
          .collection payloadEnd
            (ReferenceCollectionSegmentExtraction.endpointLedger ledgerCut before)
            proposalEnd := by
        rw [← hendpointState]
        exact hendpointCollection
      have hcurrentPreLedger := ReferenceCollectionSegmentExtraction.choice_collection_pre
        currentRecord.input payloadEnd
        (ReferenceCollectionSegmentExtraction.endpointLedger ledgerCut before)
        proposalEnd c hcurrentStateCollection hcurrentChoice
      have hpreLedgerEq : c.preLedger =
          ReferenceCollectionSegmentExtraction.endpointLedger ledgerCut before :=
        hcurrentPreLedger.1
      rw [hcutFinalLedger] at hfoldBefore hpreLedgerEq
      have hprefix : Pn = cut :: before := by
        dsimp [Pn, before, currentRecord]
        rw [hwindow, ← hj]
        simp [j]
      have hinputPrefix : ReferenceCollectionSegmentExtraction.inputs Pn =
          completedCut.input :: ReferenceCollectionSegmentExtraction.inputs before := by
        simp [hprefix, ReferenceCollectionSegmentExtraction.inputs,
          ReferenceCollectionSegmentExtraction.completed, hcutRecordExtract]
      have hfoldPrefix := ReferenceCollectionSegmentExtraction.checkedRounds_cons
        c0.preLedger completedCut.final
        (ReferenceCollectionSegmentExtraction.endpointLedger completedCut.final before)
        completedCut.input completedCut.accepted
        (ReferenceCollectionSegmentExtraction.inputs before)
        (ReferenceCollectionSegmentExtraction.acceptances before)
        hcutOne hfoldBefore
      rw [← hpreLedgerEq] at hfoldPrefix
      rw [← hinputPrefix] at hfoldPrefix
      have hfold : CollectionCheckedExecution.checkedRounds c0.preLedger
          (ReferenceCollectionSegmentExtraction.inputs Pn) =
            some (completedCut.accepted ::
              ReferenceCollectionSegmentExtraction.acceptances before, c.preLedger) := hfoldPrefix
      have hchron := CollectionCheckedExecution.checkedRounds_success_input_chronology
        c0.preLedger c.preLedger (ReferenceCollectionSegmentExtraction.inputs Pn)
        (completedCut.accepted :: ReferenceCollectionSegmentExtraction.acceptances before) hfold
      have hgood : ∀ record ∈ Pn, ∃ completed,
          ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
          completed.input.round = record.input.time ∧
          completed.input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic record := by
        intro record hmem
        rw [hprefix] at hmem
        rcases List.mem_cons.mp hmem with hcut | hbefore
        · subst record
          exact ⟨completedCut, hcutRecordExtract, hcutActual.2.1, hcutRaw.1⟩
        · rcases hprior record hbefore with ⟨_, completed, _, _, _, _, hround, hraw, hextract⟩
          exact ⟨completed, hextract, hround, hraw⟩
      have hphysicalKnown : ∀ a, c.preLedger.currentRegisters a ≠ none →
          ∀ round, c.preLedger.rawBuffer a round = none := by
        intro a hknown round
        have hinitKnown : knownRawColumnEmpty c0.preLedger a := by
          intro _ r
          exact hinitEmpty a r
        exact checkedRounds_preserves_known_raw_empty c0.preLedger c.preLedger
          (ReferenceCollectionSegmentExtraction.inputs Pn)
          (completedCut.accepted :: ReferenceCollectionSegmentExtraction.acceptances before)
          a hinitKnown hfold hknown round
      have hrawFold := fun a (hunknown : c.preLedger.currentRegisters a = none) =>
        CollectionBufferProvenance.checkedRounds_unknown_arm_buffer c0.preLedger c.preLedger
          (ReferenceCollectionSegmentExtraction.inputs Pn)
          (completedCut.accepted :: ReferenceCollectionSegmentExtraction.acceptances before)
          a hfold hunknown hchron
      have hphysicalFormula : ∀ a round, c.preLedger.rawBuffer a round =
          if c.preLedger.currentRegisters a = none then physicalRawCell Pn g a round else none := by
        intro a round
        by_cases hknown : c.preLedger.currentRegisters a ≠ none
        · simp [hknown, hphysicalKnown a hknown round]
        · have hunknown : c.preLedger.currentRegisters a = none := by
            cases hreg : c.preLedger.currentRegisters a with
            | none => rfl
            | some value => exact False.elim (hknown (by simp [hreg]))
          have hbuffer := (hrawFold a hunknown).2.1 round
          have hcell := supplied_cell_eq_physical_cell c0.preLedger.rawBuffer Pn
            c0.preLedger.freezeAt a round hinitEmpty hgood
          rw [hcell, hfreezeEq] at hbuffer
          simpa [hunknown] using hbuffer
      have hprefixUnique : ∀ left ∈ Pn, ∀ right ∈ Pn,
          left.input.time = right.input.time → left = right := by
        intro left hleft right hright htime
        have hleftW := mem_take_subset W n.val hleft
        have hrightW := mem_take_subset W n.val hright
        have hleftExec : left ∈ execution.records := by
          rw [hwindow] at hleftW
          rcases List.mem_cons.mp hleftW with heq | hmem
          · subst left
            rw [hsplit']
            simp
          · have hsuffix := mem_takeWhile_subset _ _ hmem
            rw [hsplit']
            exact List.mem_append_right firstWindow (List.mem_cons_of_mem cut hsuffix)
        have hrightExec : right ∈ execution.records := by
          rw [hwindow] at hrightW
          rcases List.mem_cons.mp hrightW with heq | hmem
          · subst right
            rw [hsplit']
            simp
          · have hsuffix := mem_takeWhile_subset _ _ hmem
            rw [hsplit']
            exact List.mem_append_right firstWindow (List.mem_cons_of_mem cut hsuffix)
        have htimesValues := ReferenceActivePhysicalHorizon.run_time_values
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start count hspan hmode
        have htimesNoDup :
            (execution.records.map (fun record => record.input.time.val)).Nodup := by
          have htimesEq : execution.records.map
              (fun record => record.input.time.val) =
              ReferenceActivePhysicalHorizon.calendar start count := by
            simpa [execution, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
              using htimesValues
          rw [htimesEq]
          simp [ReferenceActivePhysicalHorizon.calendar, List.nodup_range']
        apply List.inj_on_of_nodup_map htimesNoDup hleftExec hrightExec
        exact congrArg Fin.val htime
      have hlimits := rawCell_support_and_future_freshness c.preLedger Pn W n
        start w g rfl hphysicalFormula hwindowTime
      exact ⟨hctxOriginal, hphysicalFormula, hphysicalKnown, hgood, hprefixUnique,
        hlimits.1, hlimits.2⟩

end Bandits.Support.ReferenceFirstCollectionRawCells

end
