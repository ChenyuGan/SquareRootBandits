/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCollectionBoundaryHistory

import Lean.Elab.Tactic.Omega

/-!
# Endpoint of a retained complete collection segment

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.

This conditional result identifies the exact endpoint of a maximal retained
collection segment on the original complete physical suffix. The two interval
payload premises are kept explicit; construction of those premises is a
separate component.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCollectionSegmentExtraction
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferenceAssignmentPayloadPersistence

namespace Bandits.Support.ReferenceCompleteRetainedCollectionSegmentEndpoint

variable {p : ConstructorDimensions.Parameters}

private theorem connected_successor_input
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (n : ℕ) (hn : n + 1 < records.length) :
    records[n + 1].input.state = (records[n]'(by omega)).output.next := by
  induction records generalizing initial n with
  | nil => simp at hn
  | cons head tail ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hconnected
      cases n with
      | zero =>
          cases tail with
          | nil => simp at hn
          | cons next rest => exact hconnected.2.1
      | succ n =>
          have ht : n + 1 < tail.length := by simp at hn; omega
          simpa only [List.getElem_cons_succ] using ih hconnected.2 n ht

private theorem takeWhile_false_at_length
    {α : Type*} (f : α → Bool) (xs : List α)
    (hlen : (xs.takeWhile f).length < xs.length) :
    f (xs[(xs.takeWhile f).length]'(by omega)) = false := by
  induction xs with
  | nil => simp at hlen
  | cons head tail ih =>
      cases hf : f head with
      | false => simp [hf]
      | true =>
          have htail : (tail.takeWhile f).length < tail.length := by
            simpa [hf] using hlen
          have h := ih htail
          simpa [hf] using h

private theorem segment_boundary_not_continuing
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (e : ℕ) (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt records e = some seg)
    (hq : e + seg.records.length < records.length) :
    ReferenceCollectionSegmentExtraction.continuing
      (records[e + seg.records.length]'(by omega)) = false := by
  have hbranch := (ReferenceCollectionSegmentExtraction.segmentAt_branch records e seg hseg).1
  cases hdrop : records.drop e with
  | nil =>
      rw [hdrop] at hbranch
      simp [ReferenceCollectionSegmentExtraction.segment] at hbranch
  | cons entry rest =>
      rw [hdrop] at hbranch
      unfold ReferenceCollectionSegmentExtraction.segment at hbranch
      cases hc : ReferenceCollectionSegmentExtraction.choice entry.input with
      | none => simp only [hc, Option.map_none] at hbranch; cases hbranch
      | some context =>
          simp only [hc, Option.map_some] at hbranch
          by_cases hgood : (ReferenceCollectionSegmentExtraction.extractRound entry).isSome = true
          · simp only [hgood, ite_true] at hbranch
            have heq := Option.some.inj hbranch
            have hrecords : seg.records = entry :: rest.takeWhile
                ReferenceCollectionSegmentExtraction.continuing :=
              (congrArg ReferenceCollectionSegmentExtraction.Segment.records heq).symm
            have hlen : seg.records.length =
                1 + (rest.takeWhile ReferenceCollectionSegmentExtraction.continuing).length := by
              rw [hrecords]
              simp
              omega
            have hqDropLen : seg.records.length < (records.drop e).length := by
              rw [List.length_drop]
              omega
            have htailLen :
                (rest.takeWhile ReferenceCollectionSegmentExtraction.continuing).length < rest.length := by
              have hqRest : seg.records.length < rest.length + 1 := by
                simpa [hdrop] using hqDropLen
              rw [hlen] at hqRest
              omega
            have hval : records[e + seg.records.length] =
                rest[(rest.takeWhile ReferenceCollectionSegmentExtraction.continuing).length] := by
              calc
                records[e + seg.records.length] = (records.drop e)[seg.records.length] :=
                  List.getElem_drop' hq
                _ = (entry :: rest)[seg.records.length]'(hdrop ▸ hqDropLen) :=
                  List.getElem_of_eq hdrop hqDropLen
                _ = rest[(rest.takeWhile ReferenceCollectionSegmentExtraction.continuing).length] := by
                  simp only [hlen, Nat.one_add, List.getElem_cons_succ]
            rw [hval]
            exact takeWhile_false_at_length _ rest htailLen
          · simp only [hgood, Bool.false_eq_true, ↓reduceIte] at hbranch
            have heq := Option.some.inj hbranch
            have hnil : seg.records = [] :=
              (congrArg ReferenceCollectionSegmentExtraction.Segment.records heq).symm
            have hzero : seg.records.length = 0 := by rw [hnil]; rfl
            have hextract : ReferenceCollectionSegmentExtraction.extractRound entry = none := by
              cases he : ReferenceCollectionSegmentExtraction.extractRound entry with
              | none => rfl
              | some round => simp [he] at hgood
            have hcontinue : ReferenceCollectionSegmentExtraction.continuing entry = false := by
              simp [ReferenceCollectionSegmentExtraction.continuing, hextract]
            have hqEntry : e < records.length := by rw [hzero] at hq; omega
            have hentry : records[e] = entry := by
              have hget := List.getElem_drop' (i := e) (j := 0) (by simpa using hqEntry)
              simpa [hdrop] using hget
            simp [hzero, hentry, hcontinue]

private theorem collection_tail_stored_payload_implies_collection
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hkeep : ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration =
        some payload) :
    ∃ final proposal,
      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration =
        .collection payload final proposal := by
  classical
  unfold ReferenceActivePhysicalStep.collectionPostChoice at hkeep
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp [hrecord, ReferenceActivePhysicalStep.coordinatorFailure,
      ReferenceAssignmentPayloadPersistence.storedPayload] at hkeep
  | some recording =>
      simp only [hrecord] at hkeep
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [hstart, ReferenceActivePhysicalStep.coordinatorFailure,
          ReferenceAssignmentPayloadPersistence.storedPayload] at hkeep
      | rejected bad => simp [hstart, ReferenceActivePhysicalStep.coordinatorFailure,
          ReferenceAssignmentPayloadPersistence.storedPayload] at hkeep
      | success ledgerStarted =>
          simp only [hstart] at hkeep
          unfold ReferenceActivePhysicalStep.collectionFinish at hkeep
          cases hcut : (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted).result with
          | invalid => simp [hcut, ReferenceActivePhysicalStep.coordinatorFailure,
              ReferenceAssignmentPayloadPersistence.storedPayload] at hkeep
          | success pair | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              simp only [hcut] at hkeep
              cases hfinish : CoordinatorCollectionLedger.finishRound decoded with
              | invalid => simp [hfinish, ReferenceActivePhysicalStep.coordinatorFailure,
                  ReferenceAssignmentPayloadPersistence.storedPayload] at hkeep
              | rejected bad => simp [hfinish, ReferenceActivePhysicalStep.coordinatorFailure,
                  ReferenceAssignmentPayloadPersistence.storedPayload] at hkeep
              | success ledgerFinished =>
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      started.clock ledgerFinished.pending x.row with
                  | error reason =>
                      simp [hfinish, hclock, ReferenceActivePhysicalStep.coordinatorFailure,
                        ReferenceAssignmentPayloadPersistence.storedPayload] at hkeep
                  | ok clockFinished =>
                      refine ⟨ledgerFinished, clockFinished.clock.lastProposal, ?_⟩
                      simp [ReferenceActivePhysicalStep.collectionPostChoice, hrecord,
                        hstart, ReferenceActivePhysicalStep.collectionFinish, hcut,
                        hfinish, hclock]

private theorem retained_collection_record_continues
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : record.input.state.coordinator = .collection payload ledger saved)
    (hretain : ReferenceAssignmentPayloadPersistence.storedPayload
      record.output.next.coordinator = some payload)
    (hnobirth : ∀ fresh,
      ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth record fresh) :
    ReferenceCollectionSegmentExtraction.continuing record = true := by
  classical
  have hprepared : record.output.preparation.coordinator =
      ReferenceActivePhysicalStep.dispatch record.input := by
    rw [record.output_eq]
    exact (ReferenceActivePhysicalStep.prepare record.input).coordinator_eq
  have hprepEq : record.output.preparation.coordinator =
      (ReferenceActivePhysicalStep.prepare record.input).coordinator := by
    rw [hprepared]
    exact (ReferenceActivePhysicalStep.prepare record.input).coordinator_eq.symm
  have hselectionRecord : record.output.preparation.coordinator.selection ≠ none := by
    intro hnone
    have hdrop := ReferenceAssignmentPayloadChronology.actualRecord_next_storedPayload_none_of_no_selection
      record hnone
    rw [hretain] at hdrop
    cases hdrop
  have hselection : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection ≠ none := by
    intro hnone
    apply hselectionRecord
    rw [hprepEq]
    exact hnone
  have hdomain : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    by_contra hbad
    have hnone : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = none := by
      simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hstate, hbad, ReferenceActivePhysicalStep.DispatchCut.selection]
    exact hselection hnone
  let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
  let source := ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff
  have hcut : ReferenceActivePhysicalStep.dispatch record.input =
      .collection payload ledger clock cutoff
        (CoordinatorRoundDispatch.dispatchCollection source) := by
    simp [ReferenceActivePhysicalStep.dispatch, hstate, hdomain, cutoff, clock, source,
      CoordinatorRoundDispatch.dispatch]
    rfl
  cases houtcome : CoordinatorRoundDispatch.dispatchCollection source with
  | continuing core snapshot boundary scores =>
      have hpreparedCut : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
          .collection payload ledger clock cutoff
            (.continuing core snapshot boundary scores) := by
        simp [ReferenceActivePhysicalStep.prepare, hcut, houtcome]
      have hchoice : ReferenceCollectionSegmentExtraction.choice record.input =
          some ⟨payload, ledger, snapshot.clockStarted,
            CoordinatorCollectionInteractive.PreObservationInputs.weights source
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩ := by
        simp [ReferenceCollectionSegmentExtraction.choice, hpreparedCut,
          ReferenceCollectionSegmentExtraction.choiceOfCut,
          ReferenceActivePhysicalStep.DispatchCut.selection, source]
      have hchoicePayload := ReferenceCollectionSegmentExtraction.choice_collection_pre
        record.input payload ledger saved _ hstate hchoice
      have hnextObs : record.output.next.coordinator =
          (ReferenceActivePhysicalStep.collectionPostChoice
            (ReferenceActivePhysicalStep.prepare record.input) payload ledger
            snapshot.clockStarted
            (CoordinatorCollectionInteractive.PreObservationInputs.weights source
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)).configuration := by
        rw [record.output_eq]
        exact congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration
          (ReferenceCollectionSegmentExtraction.choice_tail record.input _ hchoice)
      have hkeep : ReferenceAssignmentPayloadPersistence.storedPayload
          (ReferenceActivePhysicalStep.collectionPostChoice
            (ReferenceActivePhysicalStep.prepare record.input) payload ledger
            snapshot.clockStarted
            (CoordinatorCollectionInteractive.PreObservationInputs.weights source
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)).configuration =
              some payload := by
        rw [← hnextObs]
        exact hretain
      obtain ⟨final, proposal, hfinal⟩ := collection_tail_stored_payload_implies_collection
        record.input (ReferenceActivePhysicalStep.prepare record.input) payload ledger
        snapshot.clockStarted
        (CoordinatorCollectionInteractive.PreObservationInputs.weights source
          snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq) hkeep
      have hnext : record.output.next.coordinator = .collection payload final proposal :=
        hnextObs.trans hfinal
      obtain ⟨done, hdone⟩ := ReferenceCollectionSegmentExtraction.actual_collection_round_complete
        record ⟨payload, ledger, snapshot.clockStarted,
          CoordinatorCollectionInteractive.PreObservationInputs.weights source
            snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩
        payload final proposal hchoice hnext
      have hdoneChoice := (ReferenceCollectionSegmentExtraction.actual_collection_round_checked
        record done hdone).1
      have hdoneContext : done.context =
          ⟨payload, ledger, snapshot.clockStarted,
            CoordinatorCollectionInteractive.PreObservationInputs.weights source
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩ :=
        Option.some.inj (hdoneChoice.symm.trans hchoice)
      have hinitializer : done.context.initializer = none := by
        rw [hdoneContext]
      simp [ReferenceCollectionSegmentExtraction.continuing, hdone, hinitializer]
  | laterChosen core consistent started hstart instruction hinstruction output hlocal
      clockData installed selected =>
      have hpreparedCut : record.output.preparation.coordinator =
          .collection payload ledger clock cutoff
            (.laterChosen core consistent started hstart instruction hinstruction output
              hlocal clockData installed selected) := by
        rw [hprepared, hcut, houtcome]
      have hbirth := ReferenceLaterInstallationProvenance.record_laterChosen_birth record
      rw [hpreparedCut] at hbirth
      exact False.elim (hnobirth installed.registers.payload hbirth)
  | clockFailure failure hstart =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, hprepared, hcut,
        houtcome] at hselectionRecord
  | localFailure started hstart hcore reason =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, hprepared, hcut,
        houtcome] at hselectionRecord
  | coreFailure core started hstart reason =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, hprepared, hcut,
        houtcome] at hselectionRecord
  | laterReconstructionFailure core consistent started hstart instruction hinstruction reason hlater =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, hprepared, hcut,
        houtcome] at hselectionRecord
  | laterPrefixFailure core consistent started hstart instruction hinstruction arm reason hlater =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, hprepared, hcut,
        houtcome] at hselectionRecord
  | laterOrientationFailure core consistent started hstart instruction hinstruction set hlater =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, hprepared, hcut,
        houtcome] at hselectionRecord
  | laterChoiceFailure core consistent started hstart instruction hinstruction output hlocal
      clockData installed reason =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, hprepared, hcut,
        houtcome] at hselectionRecord

private theorem exitOf_laterChosen
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (rest : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (h : ReferenceCollectionPhaseHistory.laterChosen record.input = true) :
    ReferenceCollectionSegmentExtraction.exitOf (record :: rest) = .laterChosen record := by
  unfold ReferenceCollectionPhaseHistory.laterChosen at h
  cases hcoord : (ReferenceActivePhysicalStep.prepare record.input).coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | clockFailure failure startRound_eq => simp [hcoord] at h
      | localFailure started startRound_eq core_invalid reason => simp [hcoord] at h
      | coreFailure core started startRound_eq reason => simp [hcoord] at h
      | continuing core snapshot boundary scores => simp [hcoord] at h
      | laterReconstructionFailure core consistent started startRound_eq instruction
          assignmentStart_eq reason later_eq => simp [hcoord] at h
      | laterPrefixFailure core consistent started startRound_eq instruction
          assignmentStart_eq arm reason later_eq => simp [hcoord] at h
      | laterOrientationFailure core consistent started startRound_eq instruction
          assignmentStart_eq set later_eq => simp [hcoord] at h
      | laterChoiceFailure core consistent started startRound_eq instruction
          assignmentStart_eq output localConsistency_eq clockData installation reason =>
          simp [hcoord] at h
      | laterChosen core consistent started startRound_eq instruction assignmentStart_eq
          output localConsistency_eq clockData installation selection =>
          simp [ReferenceCollectionSegmentExtraction.exitOf, hcoord]
  | first outcome => simp [hcoord] at h
  | live registers owned base outcome => simp [hcoord] at h
  | invalidCollectionCutoff => simp [hcoord] at h
  | dagger => simp [hcoord] at h

/-- Locate the endpoint of an actual retained complete collection segment
from two literal payload-interval conditions on the same physical run. -/
theorem internal_complete_retained_collection_segment_endpoint
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (e : ℕ) (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) e = some seg)
    (hne : seg.records ≠ [])
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (heb : e < b.val)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (hretain : ∀ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      e < k.val → k.val ≤ b.val →
      ReferenceAssignmentPayloadPersistence.storedPayload
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val].input.state.coordinator =
            some seg.context.payload)
    (hnobirth : ∀ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      e < k.val → k.val < b.val →
      ∀ fresh : ReferenceActivePhysicalStep.Payload rate,
        ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val] fresh) :
    b.val = e + seg.records.length ∧
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).drop b.val =
      seg.remaining ∧
    seg.exit = .laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val] ∧
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val].input.state =
      ReferenceCollectionSegmentExtraction.endpointState seg.entry.input.state seg.records ∧
    (∃ saved,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val].input.state.coordinator =
        .collection seg.context.payload seg.final saved) ∧
    seg.final.pending = ∅ ∧
    seg.final.cursor = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
      b.val + 1 := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let q := e + seg.records.length
  have hhistory := ReferenceCompleteCollectionBoundaryHistory.internal_complete_collection_boundary_history
    rate rewards C_star C_h z e seg hseg hne hcut
  dsimp only [R, s, q] at hhistory
  rcases hhistory with ⟨hqle, _hinputs, _hchoices, saved, hend, hcursor, during,
    hrecords, _hprefix, hnotlater, hduring, _hpending, _hnodup, _hwitnesses, hpost⟩
  have hpartition := ReferenceCollectionSegmentExtraction.segmentAt_partition R e seg hseg
  have hnotlaterMem : ∀ r, r ∈ seg.records →
      ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
    intro r hr
    rw [hrecords] at hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r
      exact hnotlater
    · exact (hduring r hr).2
  have hq_le_b : q ≤ b.val := by
    by_contra h
    have hlt : b.val < q := by omega
    have hi : b.val - e < seg.records.length := by dsimp [q] at hlt ⊢; omega
    have hiDrop : b.val - e < (R.drop e).length := by
      rw [← hpartition]
      simp only [List.length_append]
      omega
    have hiPartition : b.val - e < (seg.records ++ seg.remaining).length :=
      hpartition.symm ▸ hiDrop
    have hval : R[b.val]'b.isLt = seg.records[b.val - e]'hi := by
      calc
        R[b.val]'b.isLt = R[e + (b.val - e)] := by congr 1; omega
        _ = (R.drop e)[b.val - e]'hiDrop := by rw [List.getElem_drop]
        _ = (seg.records ++ seg.remaining)[b.val - e]'hiPartition :=
          List.getElem_of_eq hpartition.symm hiDrop
        _ = seg.records[b.val - e]'hi := List.getElem_append_left hi
    have hmem : R[b.val]'b.isLt ∈ seg.records := by
      rw [hval]
      exact List.getElem_mem hi
    have hfalse := hnotlaterMem (R[b.val]'b.isLt) hmem
    rw [hb] at hfalse
    cases hfalse
  have hq_lt : q < R.length := by
    rcases hpost with hhorizon | ⟨hv, _, _, _, _, _⟩
    · omega
    · exact hv
  rcases hpost with hhorizon | ⟨hqIndex, hqstate, hqcoord, hqtime, hqdrop, hqtag⟩
  · omega
  have hconnected : ∃ initial final,
      ReferenceActivePhysicalHorizon.Connected initial R final := by
    cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
    | none =>
        have : b.val < R.length := b.isLt
        simp [R, ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch] at this
    | some initial =>
        exact ⟨initial, _, ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
          rate z rewards C_star C_h initial hlaunch⟩
  obtain ⟨initial, final, hconnected⟩ := hconnected
  have hlen_pos : 0 < seg.records.length := by
    by_contra h
    have hzero : seg.records.length = 0 := by omega
    have hnil : seg.records = [] := List.length_eq_zero_iff.mp hzero
    exact hne hnil
  have hqeq : q = b.val := by
    by_cases hq_lt_b : q < b.val
    · have hnextIndex : q + 1 < R.length := by
        exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hq_lt_b) b.isLt
      have hadj := connected_successor_input R hconnected q hnextIndex
      let kNext : Fin R.length := ⟨q + 1, hnextIndex⟩
      have hkNextE : e < kNext.val := by dsimp [kNext, q]; omega
      have hkNextB : kNext.val ≤ b.val := by dsimp [kNext]; omega
      have hretainNext := hretain kNext hkNextE hkNextB
      have hkeepNext : ReferenceAssignmentPayloadPersistence.storedPayload
          (R[q]'(by omega)).output.next.coordinator = some seg.context.payload := by
        change ReferenceAssignmentPayloadPersistence.storedPayload
          (R[q + 1]'hnextIndex).input.state.coordinator = some seg.context.payload at hretainNext
        rw [hadj] at hretainNext
        exact hretainNext
      let kCurrent : Fin R.length := ⟨q, hq_lt⟩
      have hkCurrentE : e < kCurrent.val := by dsimp [kCurrent, q]; omega
      have hkCurrentB : kCurrent.val < b.val := by dsimp [kCurrent]; omega
      have hnoBirthQ := hnobirth kCurrent hkCurrentE hkCurrentB
      have hcontinue := retained_collection_record_continues
        (R[q]'hq_lt) seg.context.payload seg.final saved hqcoord hkeepNext hnoBirthQ
      have hstop := segment_boundary_not_continuing R e seg hseg hq_lt
      rw [hcontinue] at hstop
      cases hstop
    · omega
  rcases hqtag with htagFalse | ⟨htagTrue, hpending, _hup⟩
  · have hqeq' : e + seg.records.length = b.val := by simpa [q] using hqeq
    have htagFalse' : ReferenceCollectionPhaseHistory.laterChosen
        (R[b.val]'b.isLt).input = false := by simpa only [hqeq'] using htagFalse
    rw [hb] at htagFalse'
    cases htagFalse'
  · have hqeq' : e + seg.records.length = b.val := by simpa [q] using hqeq
    have hdrop : R.drop b.val = seg.remaining := by simpa only [hqeq'] using hqdrop
    have hstate : R[b.val].input.state =
        ReferenceCollectionSegmentExtraction.endpointState seg.entry.input.state seg.records := by
      simpa only [hqeq'] using hqstate
    have hcoord : R[b.val].input.state.coordinator =
        .collection seg.context.payload seg.final saved := by
      simpa only [hqeq'] using hqcoord
    have hexit : seg.exit = .laterChosen R[b.val] := by
      rw [ReferenceCollectionSegmentExtraction.Segment.exit, ← hdrop,
        List.drop_eq_getElem_cons b.isLt]
      exact exitOf_laterChosen (R[b.val]'b.isLt) (R.drop (b.val + 1)) hb
    refine ⟨hqeq.symm, hdrop, hexit, hstate, ⟨saved, hcoord⟩, hpending, ?_⟩
    simpa only [hqeq'] using hcursor

end Bandits.Support.ReferenceCompleteRetainedCollectionSegmentEndpoint
