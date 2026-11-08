/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionSegmentExtraction

import Lean.Elab.Tactic.Omega

/-!
# Actual collection prefix-ledger history

For each actual segment selected from the physical horizon, successful checked
round extraction determines the checked ledger on every retained prefix and
identifies the pre-ledger of the next extracted round. The same checked-fold
chronology aligns its calendar indices with those actual inputs. The selected
accepted-UP projection exposes the real recorder, start, filtered receive,
decode, and finish calls for one extracted record.

Mathematical evidence: `sources/zip4/manuscript/06_interruptions.tex:40-70,246-283`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:46-64`. These are
internal execution identities; they do not establish recorder truth, global
queue or score correctness, or a regret conclusion.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCollectionPrefixLedgerHistory

open ConstructorDimensions
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CollectionCheckedExecution
open Bandits.Support.OrdinaryMessageCodec

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem segment_entry_choice
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segment records = some segment) :
    ReferenceCollectionSegmentExtraction.choice segment.entry.input = some segment.context := by
  cases records with
  | nil => simp [ReferenceCollectionSegmentExtraction.segment] at hsegment
  | cons entry rest =>
      unfold ReferenceCollectionSegmentExtraction.segment at hsegment
      cases hchoice : ReferenceCollectionSegmentExtraction.choice entry.input with
      | none => simp [hchoice] at hsegment
      | some context =>
          simp only [hchoice, Option.map_some] at hsegment
          split at hsegment <;> cases Option.some.inj hsegment <;> exact hchoice

private theorem segment_shape
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segment records = some segment) :
    (segment.records = [] ∧ segment.remaining = records) ∨
      ∃ tail, records = segment.entry :: tail ∧ segment.records = segment.entry ::
        (segment.records.drop 1) ∧
        ∀ record ∈ segment.records.drop 1,
          ReferenceCollectionSegmentExtraction.continuing record = true := by
  cases records with
  | nil => simp [ReferenceCollectionSegmentExtraction.segment] at hsegment
  | cons entry tail =>
      unfold ReferenceCollectionSegmentExtraction.segment at hsegment
      cases hchoice : ReferenceCollectionSegmentExtraction.choice entry.input with
      | none => simp [hchoice] at hsegment
      | some context =>
          simp only [hchoice, Option.map_some] at hsegment
          split at hsegment
          · cases Option.some.inj hsegment
            right
            refine ⟨tail, rfl, ?_, ?_⟩
            · simp
            · intro record hrecord
              have hrecord' : record ∈ tail.takeWhile
                  ReferenceCollectionSegmentExtraction.continuing := by
                simpa using hrecord
              exact (List.all_eq_true.mp List.all_takeWhile) record hrecord'
          · cases Option.some.inj hsegment
            exact Or.inl ⟨rfl, rfl⟩

private theorem connected_take
    (initial : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (final : ReferenceActivePhysicalStep.State p rate) (count : ℕ)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final) :
    ReferenceActivePhysicalHorizon.Connected initial (records.take count)
      (ReferenceCollectionSegmentExtraction.endpointState initial (records.take count)) := by
  induction count generalizing initial records final with
  | zero => simp [ReferenceActivePhysicalHorizon.Connected,
      ReferenceCollectionSegmentExtraction.endpointState]
  | succ count ih =>
      cases records with
      | nil => simp [ReferenceActivePhysicalHorizon.Connected,
          ReferenceCollectionSegmentExtraction.endpointState] at hchain ⊢
      | cons record rest =>
          rcases hchain with ⟨hpre, htail⟩
          simpa [ReferenceActivePhysicalHorizon.Connected,
            ReferenceCollectionSegmentExtraction.endpointState,
            List.take_succ_cons] using
            (And.intro hpre (ih record.output.next rest final htail))

private theorem inputs_take
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hgood : ∀ record ∈ records,
      (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true)
    (count : ℕ) :
    (ReferenceCollectionSegmentExtraction.inputs records).take count =
      ReferenceCollectionSegmentExtraction.inputs (records.take count) := by
  induction count generalizing records with
  | zero => simp [ReferenceCollectionSegmentExtraction.inputs,
      ReferenceCollectionSegmentExtraction.completed]
  | succ count ih =>
      cases records with
      | nil => simp [ReferenceCollectionSegmentExtraction.inputs,
          ReferenceCollectionSegmentExtraction.completed]
      | cons record rest =>
          have hhead := hgood record (List.mem_cons_self)
          have htail : ∀ record ∈ rest,
              (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true :=
            fun record hmem => hgood record (List.mem_cons_of_mem _ hmem)
          cases hextract : ReferenceCollectionSegmentExtraction.extractRound record with
          | none => simp [hextract] at hhead
          | some completed =>
              simpa [ReferenceCollectionSegmentExtraction.inputs,
                ReferenceCollectionSegmentExtraction.completed, hextract,
                List.take_succ_cons] using congrArg
                  (List.cons completed.input) (ih rest htail)

private theorem calendarIndices_succ (T start length : ℕ)
    (hbound : start + (length + 1) ≤ T) :
    CoordinatorCollectionLedger.calendarIndices T start (length + 1) hbound =
      (⟨start, by omega⟩ : Fin T) ::
        CoordinatorCollectionLedger.calendarIndices T (start + 1) length (by omega) := by
  simp only [CoordinatorCollectionLedger.calendarIndices, List.ofFn_succ]
  apply congrArg (fun tail => (⟨start, by omega⟩ : Fin T) :: tail)
  apply congrArg List.ofFn
  funext i
  apply Fin.ext
  simp
  omega

private theorem calendarIndices_eq_input_rounds
    (cursor : ℕ)
    (inputs : List (CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val)))
    (hchron : CollectionCheckedExecution.chronologicalFrom cursor inputs)
    (hbound : cursor - 1 + inputs.length ≤ p.T) :
    CoordinatorCollectionLedger.calendarIndices p.T (cursor - 1) inputs.length
        (by omega) = inputs.map CollectionCheckedExecution.RoundInput.round := by
  induction inputs generalizing cursor with
  | nil => simp [CoordinatorCollectionLedger.calendarIndices]
  | cons head rest ih =>
      rcases hchron with ⟨hhead, htail⟩
      have hcursor : 1 ≤ cursor := by
        have hpos := head.round.isLt
        dsimp [CoordinatorCollectionLedger.sourceRound] at hhead
        omega
      have hbound' : cursor - 1 + (rest.length + 1) ≤ p.T := by
        simpa [List.length_cons] using hbound
      have htailBound : cursor + rest.length ≤ p.T := by omega
      have hsplit := calendarIndices_succ p.T (cursor - 1) rest.length hbound'
      have hfirst : (⟨cursor - 1, by omega⟩ : Fin p.T) = head.round := by
        apply Fin.ext
        dsimp [CoordinatorCollectionLedger.sourceRound] at hhead ⊢
        omega
      have htailIndices :
          CoordinatorCollectionLedger.calendarIndices p.T cursor rest.length
              (by omega) = rest.map CollectionCheckedExecution.RoundInput.round := by
        have h := ih (cursor + 1) htail (by omega)
        simpa using h
      have hstart : cursor - 1 + 1 = cursor := by omega
      have hsplit' :
          CoordinatorCollectionLedger.calendarIndices p.T (cursor - 1)
              (rest.length + 1) hbound' =
            (⟨cursor - 1, by omega⟩ : Fin p.T) ::
              CoordinatorCollectionLedger.calendarIndices p.T cursor rest.length htailBound := by
        simpa [hstart] using hsplit
      simp only [List.length_cons]
      rw [hsplit', hfirst, htailIndices]
      simp

private theorem connected_getElem_prestate
    (initial : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (final : ReferenceActivePhysicalStep.State p rate) (k : ℕ) (hk : k < records.length)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final) :
    (records[k]'hk).input.state =
      ReferenceCollectionSegmentExtraction.endpointState initial (records.take k) := by
  induction k generalizing initial records final with
  | zero =>
      cases records with
      | nil => simp at hk
      | cons record rest =>
          rcases hchain with ⟨hpre, _⟩
          simpa [ReferenceCollectionSegmentExtraction.endpointState] using hpre
  | succ k ih =>
      cases records with
      | nil => simp at hk
      | cons record rest =>
          rcases hchain with ⟨_, htail⟩
          have hk' : k < rest.length := by simpa using hk
          have h := ih record.output.next rest final hk' htail
          simpa only [List.getElem_cons_succ, List.take_succ_cons,
            ReferenceCollectionSegmentExtraction.endpointState, List.foldl_cons] using h

private theorem takeWhile_of_all_continuing
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hall : ∀ record ∈ records,
      ReferenceCollectionSegmentExtraction.continuing record = true) :
    List.takeWhile ReferenceCollectionSegmentExtraction.continuing records = records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      have hrecord := hall record (by simp)
      have hrest : ∀ record ∈ rest,
          ReferenceCollectionSegmentExtraction.continuing record = true := by
        intro record hmem
        exact hall record (by simp [hmem])
      simp [hrecord, ih hrest]

theorem run_segment_prefix_checked
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (offset : ℕ) (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records
      offset = some segment)
    (k : ℕ) (hk : k ≤ segment.records.length) :
    ∃ accepted, CollectionCheckedExecution.checkedRounds segment.context.preLedger
      (segment.inputs.take k) = some (accepted,
        ReferenceCollectionSegmentExtraction.endpointLedger segment.context.preLedger
          (segment.records.take k)) := by
  let run := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active
  have hbranch := (ReferenceCollectionSegmentExtraction.segmentAt_branch
    run.records offset segment hsegment).1
  have hgood := ReferenceCollectionSegmentExtraction.segment_all_completed
    _ segment hbranch
  have hshape := segment_shape (run.records.drop offset) segment hbranch
  have hchainDrop := ReferenceCollectionSegmentExtraction.connected_drop run.records initial
    run.finalState offset
    (ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards start count
      span active)
  have hpartition := ReferenceCollectionSegmentExtraction.segment_partition
    (run.records.drop offset) segment hbranch
  have htake : (run.records.drop offset).take segment.records.length = segment.records := by
    rw [← hpartition]
    simp
  have hsegmentChain := connected_take
    (ReferenceCollectionSegmentExtraction.endpointState initial (run.records.take offset))
    (run.records.drop offset) run.finalState segment.records.length hchainDrop
  rw [htake] at hsegmentChain
  rcases hshape with ⟨hempty, _⟩ | ⟨tail, _, hrecords, htailContinuing⟩
  · have hk0 : k = 0 := by simp [hempty] at hk ⊢; omega
    subst k
    refine ⟨[], ?_⟩
    simp [CollectionCheckedExecution.checkedRounds,
      ReferenceCollectionSegmentExtraction.Segment.inputs,
      ReferenceCollectionSegmentExtraction.inputs,
      ReferenceCollectionSegmentExtraction.completed,
      ReferenceCollectionSegmentExtraction.endpointLedger, hempty]
  · have hentryGood := hgood segment.entry (by rw [hrecords]; simp)
    cases hextract : ReferenceCollectionSegmentExtraction.extractRound segment.entry with
    | none => simp [hextract] at hentryGood
    | some headCompleted =>
        have hentryChoice := segment_entry_choice (run.records.drop offset) segment hbranch
        have hentryActual := ReferenceCollectionSegmentExtraction.actual_collection_round_checked
          segment.entry headCompleted hextract
        have hcontext : headCompleted.context = segment.context :=
          (Option.some.inj (hentryChoice.symm.trans hentryActual.1)).symm
        rcases hentryActual with ⟨_, _, hheadChecked, payload, proposal, hnext⟩
        have hheadChecked' : CollectionCheckedExecution.checkedRounds
            segment.context.preLedger [headCompleted.input] =
              some ([headCompleted.accepted], headCompleted.final) := by
          simpa [hcontext] using hheadChecked
        have hsegmentChain' : ReferenceActivePhysicalHorizon.Connected
            (ReferenceCollectionSegmentExtraction.endpointState initial (run.records.take offset))
            (segment.entry :: segment.records.drop 1)
            (ReferenceCollectionSegmentExtraction.endpointState
              (ReferenceCollectionSegmentExtraction.endpointState initial (run.records.take offset))
              (segment.entry :: segment.records.drop 1)) := by
          cases hrecordsList : segment.records with
          | nil => simp [hrecordsList] at hrecords
          | cons head rest =>
              have hhead : head = segment.entry := by
                have hshapeEq := hrecords
                rw [hrecordsList] at hshapeEq
                simp only [List.drop_succ_cons, List.drop_zero] at hshapeEq
                injection hshapeEq with hhead
              subst head
              have hchain := hsegmentChain
              rw [hrecordsList] at hchain
              simpa [hrecordsList] using hchain
        change ReferenceActivePhysicalHorizon.Connected
          (ReferenceCollectionSegmentExtraction.endpointState initial (run.records.take offset))
          (segment.entry :: segment.records.drop 1)
          (ReferenceCollectionSegmentExtraction.endpointState segment.entry.output.next
            (segment.records.drop 1)) at hsegmentChain'
        have htailChain := hsegmentChain'.2
        cases k with
        | zero =>
            refine ⟨[], ?_⟩
            simp [CollectionCheckedExecution.checkedRounds,
              ReferenceCollectionSegmentExtraction.Segment.inputs,
              ReferenceCollectionSegmentExtraction.inputs,
              ReferenceCollectionSegmentExtraction.completed,
              ReferenceCollectionSegmentExtraction.endpointLedger]
        | succ priorCount =>
            have hpriorLength : priorCount ≤ (segment.records.drop 1).length := by
              have hlen : (segment.records.drop 1).length + 1 = segment.records.length := by
                calc
                  (segment.records.drop 1).length + 1 =
                      (segment.entry :: segment.records.drop 1).length := by simp
                  _ = segment.records.length := by rw [← hrecords]
              omega
            let tailPrefix := (segment.records.drop 1).take priorCount
            have htailConnected := connected_take segment.entry.output.next
              (segment.records.drop 1)
              (ReferenceCollectionSegmentExtraction.endpointState
                segment.entry.output.next (segment.records.drop 1)) priorCount htailChain
            have htailAll : ∀ record ∈ tailPrefix,
                ReferenceCollectionSegmentExtraction.continuing record = true := by
              intro record hmem
              exact htailContinuing record (List.mem_of_mem_take hmem)
            have htakeWhile : tailPrefix.takeWhile
                ReferenceCollectionSegmentExtraction.continuing = tailPrefix := by
              exact takeWhile_of_all_continuing tailPrefix htailAll
            have htailChecked := ReferenceCollectionSegmentExtraction.continuing_checked
              tailPrefix segment.entry.output.next
              (ReferenceCollectionSegmentExtraction.endpointState
                segment.entry.output.next tailPrefix)
              payload headCompleted.final proposal
              htailConnected hnext
            have htailChecked' : CollectionCheckedExecution.checkedRounds headCompleted.final
                (ReferenceCollectionSegmentExtraction.inputs tailPrefix) =
                  some (ReferenceCollectionSegmentExtraction.acceptances tailPrefix,
                    ReferenceCollectionSegmentExtraction.endpointLedger headCompleted.final tailPrefix) := by
              simpa [htakeWhile] using htailChecked.1
            have hinputPrefix : segment.inputs.take (priorCount + 1) =
                [headCompleted.input] ++ ReferenceCollectionSegmentExtraction.inputs tailPrefix := by
              have htakeRecords : segment.records.take (priorCount + 1) =
                  segment.entry :: tailPrefix := by
                rw [hrecords, List.take_succ_cons]
              calc
                segment.inputs.take (priorCount + 1) =
                    ReferenceCollectionSegmentExtraction.inputs
                      (segment.records.take (priorCount + 1)) :=
                  inputs_take segment.records hgood (priorCount + 1)
                _ = ReferenceCollectionSegmentExtraction.inputs
                    (segment.entry :: tailPrefix) := by rw [htakeRecords]
                _ = [headCompleted.input] ++ ReferenceCollectionSegmentExtraction.inputs tailPrefix := by
                  simp only [ReferenceCollectionSegmentExtraction.inputs,
                    ReferenceCollectionSegmentExtraction.completed,
                    List.filterMap_cons, hextract, List.map_cons]
                  rfl
            have hfullPrefix := ReferenceCollectionSegmentExtraction.checkedRounds_cons
              segment.context.preLedger headCompleted.final
              (ReferenceCollectionSegmentExtraction.endpointLedger headCompleted.final tailPrefix)
              headCompleted.input headCompleted.accepted
              (ReferenceCollectionSegmentExtraction.inputs tailPrefix)
              (ReferenceCollectionSegmentExtraction.acceptances tailPrefix)
              hheadChecked' htailChecked'
            refine ⟨headCompleted.accepted ::
              ReferenceCollectionSegmentExtraction.acceptances tailPrefix, ?_⟩
            rw [hinputPrefix]
            have htakeRecords : segment.records.take (priorCount + 1) =
                segment.entry :: tailPrefix := by
              rw [hrecords, List.take_succ_cons]
            rw [htakeRecords]
            simpa only [ReferenceCollectionSegmentExtraction.endpointLedger,
              ReferenceCollectionSegmentExtraction.completed,
              List.filterMap_cons, hextract, List.map_cons, List.foldl_cons,
              List.singleton_append] using hfullPrefix

theorem retained_completed_preledger
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (offset : ℕ) (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records
      offset = some segment)
    (k : ℕ) (hk : k < segment.records.length)
    (completed : ReferenceCollectionSegmentExtraction.CompletedRound rate)
    (hextract : ReferenceCollectionSegmentExtraction.extractRound
      (segment.records[k]'hk) = some completed) :
    completed.context.preLedger =
      ReferenceCollectionSegmentExtraction.endpointLedger segment.context.preLedger
        (segment.records.take k) := by
  let run := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active
  have hbranch := (ReferenceCollectionSegmentExtraction.segmentAt_branch
    run.records offset segment hsegment).1
  have hgood := ReferenceCollectionSegmentExtraction.segment_all_completed
    _ segment hbranch
  have hshape := segment_shape (run.records.drop offset) segment hbranch
  rcases hshape with ⟨hempty, _⟩ | ⟨_, _, hrecords, htailContinuing⟩
  · simp [hempty] at hk
  · have hchainDrop := ReferenceCollectionSegmentExtraction.connected_drop run.records initial
      run.finalState offset
      (ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards start count
        span active)
    have hsegmentPartition := ReferenceCollectionSegmentExtraction.segment_partition
      (run.records.drop offset) segment hbranch
    have htake : (run.records.drop offset).take segment.records.length = segment.records := by
      rw [← hsegmentPartition]
      simp
    have hsegmentChain := connected_take
      (ReferenceCollectionSegmentExtraction.endpointState initial (run.records.take offset))
      (run.records.drop offset) run.finalState segment.records.length hchainDrop
    rw [htake] at hsegmentChain
    let record := segment.records[k]'hk
    have hchoice :=
      (ReferenceCollectionSegmentExtraction.actual_collection_round_checked record completed hextract).1
    cases k with
    | zero =>
        have hrecord : record = segment.entry := by
          cases hrecordsList : segment.records with
          | nil => simp [hrecordsList] at hk
          | cons head rest =>
              have hshapeEq := hrecords
              rw [hrecordsList] at hshapeEq
              simp only [List.drop_succ_cons, List.drop_zero] at hshapeEq
              have hhead : head = segment.entry := by injection hshapeEq
              subst head
              simp [record, hrecordsList]
        have hextractEntry :
            ReferenceCollectionSegmentExtraction.extractRound segment.entry = some completed := by
          simpa [record, hrecord] using hextract
        subst record
        have hentryChoice := segment_entry_choice (run.records.drop offset) segment hbranch
        have hentryActual :=
          (ReferenceCollectionSegmentExtraction.actual_collection_round_checked
            segment.entry completed hextractEntry).1
        have hcontext : completed.context = segment.context :=
          (Option.some.inj (hentryChoice.symm.trans hentryActual)).symm
        calc
          completed.context.preLedger = segment.context.preLedger :=
            congrArg (fun context : ReferenceCollectionSegmentExtraction.Choice rate =>
              context.preLedger) hcontext
          _ = ReferenceCollectionSegmentExtraction.endpointLedger segment.context.preLedger
              (segment.records.take 0) := by
            simp [ReferenceCollectionSegmentExtraction.endpointLedger,
              ReferenceCollectionSegmentExtraction.completed]
    | succ priorCount =>
        have hpriorLength : priorCount < (segment.records.drop 1).length := by
          have hlen : (segment.records.drop 1).length + 1 = segment.records.length := by
            calc
              (segment.records.drop 1).length + 1 =
                  (segment.entry :: segment.records.drop 1).length := by simp
              _ = segment.records.length := by rw [← hrecords]
          omega
        let priorTail := (segment.records.drop 1).take priorCount
        have htakeWhileAll : ∀ record ∈ priorTail,
            ReferenceCollectionSegmentExtraction.continuing record = true := by
          intro record hmem
          exact htailContinuing record (List.mem_of_mem_take hmem)
        have htakeWhile := takeWhile_of_all_continuing priorTail htakeWhileAll
        have hsegmentChain' : ReferenceActivePhysicalHorizon.Connected
            (ReferenceCollectionSegmentExtraction.endpointState initial (run.records.take offset))
            (segment.entry :: segment.records.drop 1)
            (ReferenceCollectionSegmentExtraction.endpointState
              (ReferenceCollectionSegmentExtraction.endpointState initial (run.records.take offset))
              (segment.entry :: segment.records.drop 1)) := by
          cases hrecordsList : segment.records with
          | nil => simp [hrecordsList] at hrecords
          | cons head rest =>
              have hshapeEq := hrecords
              rw [hrecordsList] at hshapeEq
              simp only [List.drop_succ_cons, List.drop_zero] at hshapeEq
              have hhead : head = segment.entry := by injection hshapeEq
              subst head
              have hchain := hsegmentChain
              rw [hrecordsList] at hchain
              simpa [hrecordsList] using hchain
        change ReferenceActivePhysicalHorizon.Connected
          (ReferenceCollectionSegmentExtraction.endpointState initial (run.records.take offset))
          (segment.entry :: segment.records.drop 1)
          (ReferenceCollectionSegmentExtraction.endpointState segment.entry.output.next
            (segment.records.drop 1)) at hsegmentChain'
        have htailChain := hsegmentChain'.2
        have hentryCompleted :
            ∃ headCompleted, ReferenceCollectionSegmentExtraction.extractRound segment.entry =
              some headCompleted := by
          cases he : ReferenceCollectionSegmentExtraction.extractRound segment.entry with
          | none => have := hgood segment.entry (by rw [hrecords]; simp); simp [he] at this
          | some headCompleted => exact ⟨headCompleted, rfl⟩
        obtain ⟨headCompleted, hextractEntry⟩ := hentryCompleted
        have hentryActual := ReferenceCollectionSegmentExtraction.actual_collection_round_checked
          segment.entry headCompleted hextractEntry
        have hentryChoice := segment_entry_choice (run.records.drop offset) segment hbranch
        have hheadContext : headCompleted.context = segment.context :=
          (Option.some.inj (hentryChoice.symm.trans hentryActual.1)).symm
        rcases hentryActual with ⟨_, _, _, payload, proposal, hnext⟩
        have hpriorConnected := connected_take segment.entry.output.next
          (segment.records.drop 1)
          (ReferenceCollectionSegmentExtraction.endpointState segment.entry.output.next
            (segment.records.drop 1)) priorCount htailChain
        have hcontinued := ReferenceCollectionSegmentExtraction.continuing_checked
          priorTail segment.entry.output.next
          (ReferenceCollectionSegmentExtraction.endpointState segment.entry.output.next priorTail)
          payload headCompleted.final proposal hpriorConnected hnext
        rcases hcontinued.2 with ⟨tailPayload, tailProposal, htailCoordinator⟩
        have htakeRecords : segment.records.take (priorCount + 1) =
            segment.entry :: priorTail := by
          rw [hrecords, List.take_succ_cons]
        have hstatePre := connected_getElem_prestate
          (ReferenceCollectionSegmentExtraction.endpointState initial (run.records.take offset))
          segment.records
          (ReferenceCollectionSegmentExtraction.endpointState
            (ReferenceCollectionSegmentExtraction.endpointState initial (run.records.take offset))
            segment.records)
          (priorCount + 1) (by omega) hsegmentChain
        have hkIndex : priorCount + 1 < segment.records.length := by omega
        have hrecordEq : record = segment.records[priorCount + 1]'hkIndex := by rfl
        have hstate : record.input.state =
            ReferenceCollectionSegmentExtraction.endpointState segment.entry.output.next priorTail := by
          calc
            record.input.state =
                (segment.records[priorCount + 1]'hkIndex).input.state := by rw [hrecordEq]
            _ = ReferenceCollectionSegmentExtraction.endpointState
                (ReferenceCollectionSegmentExtraction.endpointState initial (run.records.take offset))
                (segment.records.take (priorCount + 1)) := hstatePre
            _ = ReferenceCollectionSegmentExtraction.endpointState
                (ReferenceCollectionSegmentExtraction.endpointState initial (run.records.take offset))
                (segment.entry :: priorTail) := by rw [htakeRecords]
            _ = ReferenceCollectionSegmentExtraction.endpointState
                segment.entry.output.next priorTail := rfl
        have hcoord : record.input.state.coordinator =
            ReferenceActivePhysicalStep.CoordinatorConfiguration.collection tailPayload
              (ReferenceCollectionSegmentExtraction.endpointLedger headCompleted.final priorTail)
              tailProposal := by
          calc
            record.input.state.coordinator =
                (ReferenceCollectionSegmentExtraction.endpointState segment.entry.output.next
                  priorTail).coordinator := congrArg
                    (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator) hstate
            _ = ReferenceActivePhysicalStep.CoordinatorConfiguration.collection tailPayload
                (ReferenceCollectionSegmentExtraction.endpointLedger headCompleted.final priorTail)
                tailProposal := by simpa [htakeWhile] using htailCoordinator
        have hpriorLedger :
            ReferenceCollectionSegmentExtraction.endpointLedger headCompleted.final priorTail =
              ReferenceCollectionSegmentExtraction.endpointLedger segment.context.preLedger
                (segment.records.take (priorCount + 1)) := by
          rw [htakeRecords]
          simp only [ReferenceCollectionSegmentExtraction.endpointLedger,
            ReferenceCollectionSegmentExtraction.completed, List.filterMap_cons,
            hextractEntry, List.foldl_cons]
        have hpre := ReferenceCollectionSegmentExtraction.choice_collection_pre
          record.input tailPayload
          (ReferenceCollectionSegmentExtraction.endpointLedger headCompleted.final priorTail)
          tailProposal completed.context hcoord hchoice
        calc
          completed.context.preLedger =
              ReferenceCollectionSegmentExtraction.endpointLedger headCompleted.final priorTail := hpre.1
          _ = ReferenceCollectionSegmentExtraction.endpointLedger segment.context.preLedger
              (segment.records.take (priorCount + 1)) := hpriorLedger

theorem actual_accepted_round_calls
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (completed : ReferenceCollectionSegmentExtraction.CompletedRound rate)
    (hextract : ReferenceCollectionSegmentExtraction.extractRound record = some completed)
    (haccepted : completed.accepted = true)
    (M : UpRecord (CoordinatorCollectionLedger.codecParams p rate.eta.val))
    (hparsed : completed.input.parsed = some M)
    (i : Fin (p.m - 1)) (hselected : completed.input.selectedFollower = i) :
    ∃ recording started decoded bank finished,
      record.output.coordinator.recording = some recording ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare record.input) completed.context.payload
          completed.context.started completed.context.weights) = some recording ∧
      CoordinatorCollectionLedger.startRound completed.context.preLedger
        (record.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled completed.context.preLedger record.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success started ∧
      (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare record.input)
        started).result = .success (decoded, bank) ∧
      CoordinatorCollectionLedger.decodeUp started i (some M) = .success decoded ∧
      CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
      finished = completed.final ∧
      completed.input = ReferenceCollectionSegmentExtraction.inputOf record.input
        completed.context.preLedger recording started := by
  obtain ⟨recording, started, decoded, bank, hrecording, hrun, hstart, hinput,
      hreceive, _⟩ := ReferenceCollectionSegmentExtraction.actual_collection_round_inputs
    record completed hextract
  have hreceiveSuccess :
      (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare record.input)
        started).result = .success (decoded, bank) := by
    rw [haccepted] at hreceive
    exact hreceive
  have hinputParse := congrArg
    (fun input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val) =>
      input.parsed) hinput
  have hparse : ReferenceCollectionSegmentExtraction.effectiveParse record.input started = some M := by
    calc
      ReferenceCollectionSegmentExtraction.effectiveParse record.input started =
          (ReferenceCollectionSegmentExtraction.inputOf record.input
            completed.context.preLedger recording started).parsed := rfl
      _ = completed.input.parsed := hinputParse.symm
      _ = some M := hparsed
  have hinputSelected := congrArg
    (fun input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val) =>
      input.selectedFollower) hinput
  have hselectedActual : ReferenceActivePhysicalStep.upSenderIndex record.input = i := by
    rw [hselected] at hinputSelected
    simpa [ReferenceCollectionSegmentExtraction.inputOf] using hinputSelected.symm
  have hdecodeSpec := ReferenceCollectionSegmentExtraction.receiveUp_decode_result
    record.input started
  rw [hreceiveSuccess] at hdecodeSpec
  have hdecode : CoordinatorCollectionLedger.decodeUp started i (some M) = .success decoded := by
    simpa [hparse, hselectedActual] using hdecodeSpec
  have hsingle :=
    (ReferenceCollectionSegmentExtraction.actual_collection_round_checked record completed hextract).2.2.1
  rw [hinput, haccepted] at hsingle
  cases hfinish : CoordinatorCollectionLedger.finishRound decoded with
  | invalid =>
      simp only [CollectionCheckedExecution.checkedRounds,
        ReferenceCollectionSegmentExtraction.inputOf,
        CoordinatorCollectionLedger.sourceRound, hstart, hselectedActual,
        hparse, hdecode, hfinish] at hsingle
      cases hsingle
  | rejected rejected =>
      simp only [CollectionCheckedExecution.checkedRounds,
        ReferenceCollectionSegmentExtraction.inputOf,
        CoordinatorCollectionLedger.sourceRound, hstart, hselectedActual,
        hparse, hdecode, hfinish] at hsingle
      cases hsingle
  | success finished =>
      have hpair : ([true], finished) = ([true], completed.final) := by
        have hsome : some ([true], finished) = some ([true], completed.final) := by
          simpa only [CollectionCheckedExecution.checkedRounds,
            ReferenceCollectionSegmentExtraction.inputOf,
            CoordinatorCollectionLedger.sourceRound, hstart, hselectedActual,
            hparse, hdecode, hfinish] using hsingle
        exact Option.some.inj hsome
      exact ⟨recording, started, decoded, bank, finished, hrecording, hrun,
        hstart, hreceiveSuccess, hdecode, hfinish, congrArg Prod.snd hpair, hinput⟩


/-- Taking an actual segment's first `k` physical records and then projecting
its extracted inputs agrees with taking `k` inputs from the segment. -/
theorem run_collection_segment_prefix_inputs_take
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (offset : ℕ) (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records
      offset = some segment)
    (k : ℕ) :
    segment.inputs.take k =
      ReferenceCollectionSegmentExtraction.inputs (segment.records.take k) := by
  have hbranch := (ReferenceCollectionSegmentExtraction.segmentAt_branch _ offset segment hsegment).1
  have hgood := ReferenceCollectionSegmentExtraction.segment_all_completed _ segment hbranch
  exact inputs_take segment.records hgood k

/-- A real extracted segment prefix has the chronology produced by the
successful checked fold; no matching round list is supplied as a premise. -/
theorem run_collection_segment_prefix_chronology
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (offset : ℕ) (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records
      offset = some segment)
    (k : ℕ) (hk : k ≤ segment.records.length) :
    CollectionCheckedExecution.chronologicalFrom segment.context.preLedger.cursor
      (segment.inputs.take k) := by
  obtain ⟨accepted, hfold⟩ := run_segment_prefix_checked initial rows selected rewards start count
    span active offset segment hsegment k hk
  exact CollectionCheckedExecution.checkedRounds_success_input_chronology _ _ _ _ hfold

/-- The canonical `Fin` calendar indices for a real segment prefix are the
actual input rounds in that prefix. Chronology is generated above from the
checked fold, preserving rejected and disabled physical rounds. The explicit
bound is the finite-calendar condition required by `calendarIndices`. -/
theorem run_collection_segment_prefix_calendar_indices
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (offset : ℕ) (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records
      offset = some segment)
    (k : ℕ) (hk : k ≤ segment.records.length)
    (hbound : segment.context.preLedger.cursor - 1 + (segment.inputs.take k).length ≤ p.T) :
    CoordinatorCollectionLedger.calendarIndices p.T
      (segment.context.preLedger.cursor - 1) (segment.inputs.take k).length
      hbound =
      (segment.inputs.take k).map CollectionCheckedExecution.RoundInput.round := by
  have hchron := run_collection_segment_prefix_chronology initial rows selected rewards
    start count span active offset segment hsegment k hk
  exact calendarIndices_eq_input_rounds segment.context.preLedger.cursor
    (segment.inputs.take k) hchron hbound


end Bandits.Support.ReferenceCollectionPrefixLedgerHistory

end
