/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionPureUpWindowCut
public import Bandits.Support.ReferenceCollectionUpReceiverLocal

import Lean.Elab.Tactic.Omega

/-!
# Actual UP receiver and started fields during first replacement collection

For every continuing record in the actual replacement window, expose its
executed collection tail, recorder, started ledger, and literal UP receiver
diagnostic. A dagger successor carries no claim in this query.
-/

@[expose] public section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstReplacementCollectionUpStartedFields

theorem complete_first_replacement_collection_up_started_fields
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            ∀ j : Fin W.length,
              let r := W.get j
              match r.output.next.coordinator with
              | .dagger => True
              | _ =>
                ∃ (ledger : ReferenceActivePhysicalStep.Ledger rate)
                  (saved : Option (Fin p.T × Bool))
                  (t : ReferenceCollectionPhaseHistory.Tail r.input)
                  (recording : CoordinatorRecordingOperation.Output p)
                  (started : ReferenceActivePhysicalStep.Ledger rate)
                  (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                  r.input.state.coordinator = .collection payload ledger saved ∧
                  ReferenceCollectionPhaseHistory.executedTail r.input = some t ∧
                  CoordinatorRecorderComplementBridge.run
                    (ReferenceActivePhysicalStep.collectionRecordingInput
                      (ReferenceActivePhysicalStep.prepare r.input)
                      t.payload t.started t.weights) = some recording ∧
                  CoordinatorCollectionLedger.startRound t.ledger (r.input.time.val + 1)
                    (ReferenceActivePhysicalStep.collectionEnabled t.ledger r.input.time)
                    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                      .success started ∧
                  ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some started ∧
                  CoordinatorUpReception.receptionInputCheck
                    (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input started) = true ∧
                  r.output.coordinator.up = some d ∧
                  d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input started ∧
                  d.expected = ReferenceActivePhysicalStep.upExpected
                    (ReferenceActivePhysicalStep.prepare r.input) ∧
                  t.reception = some (started, ReferenceActivePhysicalStep.receiveUp
                    (ReferenceActivePhysicalStep.prepare r.input) started) ∧
                  (ReferenceActivePhysicalStep.receiveUp
                    (ReferenceActivePhysicalStep.prepare r.input) started).result ≠ .invalid ∧
                  started.sigma = payload.sigma.val + 1 ∧ started.cutoff = u ∧
                  started.cursor = r.input.time.val + 1 ∧ started.cutoff ≤ started.cursor ∧
                  started.pending = Finset.univ \
                    (ReferenceCollectionPhaseHistory.acceptedLabels
                      (K.take (j.val + 1))).toFinset ∧
                  (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) →
                    ReferenceActivePhysicalStep.upSenderIndex r.input ∈ started.pending ∧
                    ReferenceActivePhysicalStep.upSenderIndex r.input ∉
                      (ReferenceCollectionPhaseHistory.acceptedLabels
                        (K.take (j.val + 1))).toFinset) ∧
                  ∃ (receivedLedger : ReferenceActivePhysicalStep.Ledger rate)
                    (bank : CoordinatorUpReception.UpDecoderBank p)
                    (finished : ReferenceActivePhysicalStep.Ledger rate)
                    (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
                    ((ReferenceActivePhysicalStep.receiveUp
                        (ReferenceActivePhysicalStep.prepare r.input) started).result =
                          .success (receivedLedger, bank) ∨
                      (ReferenceActivePhysicalStep.receiveUp
                        (ReferenceActivePhysicalStep.prepare r.input) started).result =
                          .rejected (receivedLedger, bank)) ∧
                    CoordinatorCollectionLedger.finishRound receivedLedger = .success finished ∧
                    CoordinatorPhaseClock.finishRound p rate.eta.val r.input.time t.started.clock
                      finished.pending r.input.row = .ok clockFinished
          | _ => True
      | _ => True := by
  classical
  have hP :=
    ReferenceFirstReplacementCollectionPureUpWindowCut.complete_first_replacement_collection_pure_up_window_cut
      rate source rewards C_star C_h
  have hR :=
    ReferenceFirstReplacementCollectionUpReceiverProvenance.complete_first_replacement_collection_up_receiver_provenance
      rate source rewards C_star C_h
  dsimp only at hP hR ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hP hR ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hP hR ⊢
      cases outcome <;> try trivial
      rename_i core consistent birthStarted hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hP hR ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      rcases hP with ⟨_, _, hP⟩
      rcases hR with ⟨_, _, hR⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [hc] at hP hR ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hP hR ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hP hR ⊢
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.output.next (W.take j)
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          rcases hP with ⟨hcalendar, hZ, _⟩
          rcases hR with ⟨hgeometry, hrecords, _⟩
          intro j
          let r := W.get j
          let k : Fin K.length := ⟨j.val + 1, by
            have hjW : j.val < W.length := by
              change j.val < ((R.drop (c + 1)).takeWhile
                (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length
              exact j.isLt
            change j.val + 1 < W.length + 1
            omega⟩
          have hget : K.get k = r := by simp [K, k, r]
          have hlinks := hZ.2.2 k
          rw [hget] at hlinks
          have hE : Z (j.val + 1) = E j.val :=
            hZ.2.1 j.val (Nat.le_of_lt j.isLt)
          have hE' : Z (j.val + 2) = E (j.val + 1) := by
            simpa [Z, E, K, Nat.add_assoc, List.take_succ_cons] using
              hZ.2.1 (j.val + 1) (by omega)
          have hinputState : r.input.state = E j.val := by
            calc
              r.input.state = Z (j.val + 1) := by
                simpa [k, Z, K, List.take_succ_cons] using hlinks.1
              _ = E j.val := hE
          have hnextState : r.output.next = E (j.val + 1) := by
            calc
              r.output.next = Z (j.val + 2) := by
                simpa [k, Z, K, List.take_succ_cons, Nat.add_assoc] using hlinks.2
              _ = E (j.val + 1) := hE'
          cases hnext : r.output.next.coordinator <;> try trivial
          all_goals
            have hnonD : r.output.next.coordinator ≠ .dagger := by simp [hnext]
            have hinputNonD : r.input.state.coordinator ≠ .dagger := by
              intro hd
              have hstep := ReferenceActivePhysicalStep.step_coordinator_dagger r.input hd
              apply hnonD
              rw [r.output_eq]
              exact hstep.1
            rcases hgeometry j.val (Nat.le_of_lt j.isLt) with
              hinputDagger | ⟨localLedger, saved, hinputCollection, _, _, _⟩
            · have hd : r.input.state.coordinator = .dagger := by
                rw [hinputState, hinputDagger]
              exact (hinputNonD hd).elim
            · have hstate : r.input.state.coordinator =
                  .collection payload localLedger saved := by
                rw [hinputState, hinputCollection]
              have hnextNonD : (E (j.val + 1)).coordinator ≠ .dagger := by
                intro hd
                apply hnonD
                exact (congrArg ReferenceActivePhysicalStep.State.coordinator hnextState).trans hd
              rcases hgeometry (j.val + 1) (by omega) with
                hnextDagger | ⟨nextLedger, nextSaved, hnextCollection, _, _, _⟩
              · exact (hnextNonD hnextDagger).elim
              · have hnextCoordinator : r.output.next.coordinator =
                    .collection payload nextLedger nextSaved := by
                  rw [hnextState]
                  exact hnextCollection
                have hstepCollection :
                    (ReferenceActivePhysicalStep.step r.input).next.coordinator =
                      .collection payload nextLedger nextSaved := by
                  rw [← r.output_eq]
                  exact hnextCoordinator
                obtain ⟨t, htail, _⟩ :=
                  ReferenceCollectionPhaseHistory.step_collection_frame r.input payload
                    nextLedger nextSaved hstepCollection
                obtain ⟨recording, receiverStarted, d, hrecording, hstart, hsite, hcheck,
                    hdiagnostic, hinput, htailReception, hnotInvalid,
                    receivedLedger, bank, finished, clockFinished, hresult, hfinish, hclock,
                    _, _, _, _, hexpected, _, _, _, _, _, _⟩ :=
                  ReferenceCollectionUpReceiverLocal.actual_collection_up_receiver
                    r payload localLedger saved t hstate htail hnonD
                have hrecordInfo := hrecords k
                rw [hget, htail] at hrecordInfo
                cases hrec : t.reception with
                | none =>
                  rw [hrec] at htailReception
                  cases htailReception
                | some pair =>
                  rcases pair with ⟨startedFromProvenance, receivedFromProvenance⟩
                  have hpair : (startedFromProvenance, receivedFromProvenance) =
                      (receiverStarted, ReferenceActivePhysicalStep.receiveUp
                        (ReferenceActivePhysicalStep.prepare r.input) receiverStarted) :=
                    Option.some.inj (hrec.symm.trans htailReception)
                  rcases Prod.mk.inj hpair with ⟨hstartedEq, hreceivedEq⟩
                  subst startedFromProvenance
                  subst receivedFromProvenance
                  simp only [hrec] at hrecordInfo
                  rcases hrecordInfo with
                    ⟨hsigma, hcutoff, hcursor, hpending, hgate, _⟩
                  have hcutCursor : receiverStarted.cutoff ≤ receiverStarted.cursor := by
                    rw [hcutoff, hcursor]
                    have htime := hcalendar k
                    rw [hget] at htime
                    omega
                  refine ⟨localLedger, saved, t, recording, receiverStarted, d,
                    hstate, htail, hrecording, hstart, hsite, hcheck, hdiagnostic,
                    hinput, hexpected, htailReception, hnotInvalid, hsigma, hcutoff,
                    hcursor, hcutCursor, hpending, ?_, ?_⟩
                  · intro heligible
                    have hEligible' : AffineBatchDecoder.eligible
                        (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput d) := by
                      simpa only [ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput]
                        using heligible
                    have eligibleIff :=
                      ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput_eligible_iff d
                    have hgateAnd := eligibleIff.mp hEligible'
                    have hgateD : CoordinatorUpReception.receptionGate d.input := hgateAnd.1
                    have hgateActual : CoordinatorUpReception.receptionGate
                        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input receiverStarted) := by
                      simpa only [hinput] using hgateD
                    have hgateFields := hgate.1 hgateActual
                    have hnotAccepted : ReferenceActivePhysicalStep.upSenderIndex r.input ∉
                        (ReferenceCollectionPhaseHistory.acceptedLabels
                          (K.take (j.val + 1))).toFinset := by
                      simpa [K, k, List.take_succ_cons] using hgateFields.2
                    refine ⟨?_, hnotAccepted⟩
                    rw [hpending]
                    exact Finset.mem_sdiff.mpr
                      ⟨Finset.mem_univ _, hnotAccepted⟩
                  · exact ⟨receivedLedger, bank, finished, clockFinished,
                      hresult, hfinish, hclock⟩

end Bandits.Support.ReferenceFirstReplacementCollectionUpStartedFields

end
