/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionFollowerPrefix

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# Actual dispatch and choice-view origin after a replacement cutoff

Sources: `sources/zip4/manuscript/06_interruptions.tex:40-70,246-295` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:62-64`.

The exported record step is conditional on the actual previous coordinator
phase and on the literal dispatcher not choosing a later assignment. The
suffix theorem below constructs those premises by adjacency and the actual
`takeWhile` boundary. This module does not prove follower survival or a whole
collection-prefix invariant.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementCollectionDispatchOrigin

open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceCollectionPhaseHistory

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem actualPreparation_dispatch_eq
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    record.output.preparation.coordinator = ReferenceActivePhysicalStep.dispatch record.input := by
  calc
    record.output.preparation.coordinator =
        (ReferenceActivePhysicalStep.step record.input).preparation.coordinator :=
      congrArg (fun out : ReferenceActivePhysicalStep.RoundOutput record.input =>
        out.preparation.coordinator) record.output_eq
    _ = ReferenceActivePhysicalStep.dispatch record.input := rfl

private theorem actual_no_selection_dispatch_step
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hselection : record.output.preparation.coordinator.selection = none)
    (hnotDagger : record.output.preparation.coordinator ≠ .dagger) :
    (record.output.next.coordinator = .dagger ∨
      ∃ ledger saved,
        record.output.next.coordinator = .collection payload ledger saved) ∧
    (record.output.preparation.coordinator.selection = none ∨
      ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
        record.output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = payload) ∧
    (record.output.preparation.coordinator.downView = none ∨
      ∃ view : ReferenceDownReception.ChoiceTimeView p rate.eta,
        record.output.preparation.coordinator.downView = some view ∧
          view.payload = payload) ∧
    (∀ i : Fin (p.m - 1),
      let expected := ReferenceDownReception.expectedDownFlatWord
        record.output.preparation.coordinator.downView i record.input.row record.input.time
      expected = none ∨
        expected = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) := by
  have hcoord := actualPreparation_dispatch_eq record
  have hselection' :
      (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = none := by
    change (ReferenceActivePhysicalStep.dispatch record.input).selection = none
    exact (congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut record.input =>
      coordinator.selection) hcoord).symm.trans hselection
  have hnotDagger' :
      (ReferenceActivePhysicalStep.prepare record.input).coordinator ≠ .dagger := by
    change ReferenceActivePhysicalStep.dispatch record.input ≠ .dagger
    intro h
    apply hnotDagger
    exact hcoord.trans h
  have hnext : record.output.next.coordinator = .dagger := by
    calc
      record.output.next.coordinator =
          (ReferenceActivePhysicalStep.step record.input).next.coordinator :=
        congrArg (fun out : ReferenceActivePhysicalStep.RoundOutput record.input =>
          out.next.coordinator) record.output_eq
      _ = (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.configuration := rfl
      _ = .dagger := by
        simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
          ReferenceActivePhysicalStep.coordinatorFailure, hselection']
  have hdown : record.output.preparation.coordinator.downView = none := by
    simp [ReferenceActivePhysicalStep.DispatchCut.downView, hselection]
  refine ⟨Or.inl hnext, Or.inl hselection, Or.inl hdown, ?_⟩
  intro i
  simp [ReferenceDownReception.expectedDownFlatWord, hdown]

/-- The actual one-record collection dispatch step. Its only induction inputs
are the actual old payload phase (or dagger) and the fact that this actual
round is before the literal later-choice dispatcher branch. -/
theorem actual_collection_dispatch_step
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hc : r.input.state.coordinator = .dagger ∨
      ∃ ledger saved,
        r.input.state.coordinator = .collection payload ledger saved)
    (hn : ReferenceCollectionPhaseHistory.laterChosen r.input = false) :
    (r.output.next.coordinator = .dagger ∨
      ∃ ledger saved,
        r.output.next.coordinator = .collection payload ledger saved) ∧
    (r.output.preparation.coordinator.selection = none ∨
      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
        r.output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = payload) ∧
    (r.output.preparation.coordinator.downView = none ∨
      ∃ view : ReferenceDownReception.ChoiceTimeView p rate.eta,
        r.output.preparation.coordinator.downView = some view ∧
          view.payload = payload) ∧
    (∀ i : Fin (p.m - 1),
      let expected := ReferenceDownReception.expectedDownFlatWord
        r.output.preparation.coordinator.downView i r.input.row r.input.time
      expected = none ∨
        expected = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) := by
  rcases hc with hdagger | ⟨ledger, saved, hcollection⟩
  · have hcoord := actualPreparation_dispatch_eq r
    have hselection : r.output.preparation.coordinator.selection = none := by
      calc
        r.output.preparation.coordinator.selection =
            (ReferenceActivePhysicalStep.dispatch r.input).selection :=
          congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut r.input =>
            coordinator.selection) hcoord
        _ = none := by
          simp [ReferenceActivePhysicalStep.dispatch, hdagger,
            ReferenceActivePhysicalStep.DispatchCut.selection]
    have hnext : r.output.next.coordinator = .dagger := by
      calc
        r.output.next.coordinator =
            (ReferenceActivePhysicalStep.step r.input).next.coordinator :=
          congrArg (fun out : ReferenceActivePhysicalStep.RoundOutput r.input =>
            out.next.coordinator) r.output_eq
        _ = (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.configuration := rfl
        _ = .dagger := by
          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
            ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
            ReferenceActivePhysicalStep.DispatchCut.selection, hdagger]
    have hdown : r.output.preparation.coordinator.downView = none := by
      simp [ReferenceActivePhysicalStep.DispatchCut.downView, hselection]
    refine ⟨Or.inl hnext, Or.inl hselection, Or.inl hdown, ?_⟩
    intro i
    simp [ReferenceDownReception.expectedDownFlatWord, hdown]
  · by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
      let collectionInput := ReferenceActivePhysicalStep.collectionInput
        r.input payload ledger clock cutoff
      have hcoord := actualPreparation_dispatch_eq r
      cases hdispatch : CoordinatorRoundDispatch.dispatchCollection collectionInput with
      | continuing core snapshot boundary scores =>
          have hdispatchCut :
              ReferenceActivePhysicalStep.dispatch r.input =
                .collection payload ledger clock cutoff
                  (.continuing core snapshot boundary scores) := by
            simp [ReferenceActivePhysicalStep.dispatch, hcollection, hvalid, cutoff, clock,
              collectionInput, CoordinatorRoundDispatch.dispatch, hdispatch]; rfl
          have hpreparedCoord :
              (ReferenceActivePhysicalStep.prepare r.input).coordinator =
                .collection payload ledger clock cutoff
                  (.continuing core snapshot boundary scores) := by
            exact hdispatchCut
          cases hselection :
              (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection with
          | none =>
              simp [ReferenceActivePhysicalStep.prepare, hdispatchCut,
                ReferenceActivePhysicalStep.DispatchCut.selection] at hselection
          | some selected =>
              have hpayload : selected.view.payload = payload := by
                have hmap := congrArg
                  (fun o : Option (ReferenceActivePhysicalStep.Selection r.input) =>
                    o.map fun selected => selected.view.payload) hselection
                have hmap' : some payload = some selected.view.payload := by
                  simpa [ReferenceActivePhysicalStep.prepare, hdispatchCut,
                    ReferenceActivePhysicalStep.DispatchCut.selection] using hmap
                exact (Option.some.inj hmap').symm
              have hselection' :
                  r.output.preparation.coordinator.selection = some selected := by
                calc
                  r.output.preparation.coordinator.selection =
                      (ReferenceActivePhysicalStep.dispatch r.input).selection :=
                    congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut r.input =>
                      coordinator.selection) hcoord
                  _ = (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection := rfl
                  _ = some selected := hselection
              let weights :=
                CoordinatorCollectionInteractive.PreObservationInputs.weights collectionInput
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
              have hcutSelection :
                  (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
                    (.continuing core snapshot boundary scores)).selection = some selected := by
                calc
                  (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
                    (.continuing core snapshot boundary scores)).selection =
                      (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection :=
                    (congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut r.input =>
                      coordinator.selection) hpreparedCoord).symm
                  _ = some selected := hselection
              have hnext : r.output.next.coordinator =
                  (ReferenceActivePhysicalStep.collectionPostChoice
                    (x := r.input) (ReferenceActivePhysicalStep.prepare r.input)
                    payload ledger snapshot.clockStarted weights).configuration := by
                calc
                  r.output.next.coordinator =
                      (ReferenceActivePhysicalStep.step r.input).next.coordinator :=
                    congrArg (fun out : ReferenceActivePhysicalStep.RoundOutput r.input =>
                      out.next.coordinator) r.output_eq
                  _ = (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.configuration := rfl
                  _ = (ReferenceActivePhysicalStep.collectionPostChoice
                      (x := r.input) (ReferenceActivePhysicalStep.prepare r.input)
                      payload ledger snapshot.clockStarted weights).configuration := by
                    simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                      hpreparedCoord, hcutSelection, weights, collectionInput]
              have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
                (ReferenceActivePhysicalStep.prepare r.input) payload ledger
                snapshot.clockStarted weights
              have hframe := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
                (ReferenceActivePhysicalStep.prepare r.input) payload ledger
                snapshot.clockStarted weights
              have hnextPhase : r.output.next.coordinator = .dagger ∨
                  ∃ nextLedger nextSaved,
                    r.output.next.coordinator = .collection payload nextLedger nextSaved := by
                rcases hphase with hdagger | ⟨nextPayload, nextLedger, nextSaved, hconfiguration⟩
                · exact Or.inl (hnext.trans hdagger)
                · rcases hframe with hnone | hpayload'
                  · simp [ReferenceAssignmentPayloadPersistence.storedPayload,
                      hconfiguration] at hnone
                  · have hpayload'' : nextPayload = payload := by
                      have hsome : some nextPayload = some payload := by
                        simpa [ReferenceAssignmentPayloadPersistence.storedPayload,
                          hconfiguration] using hpayload'
                      exact Option.some.inj hsome
                    exact Or.inr ⟨nextLedger, nextSaved,
                      hnext.trans (hconfiguration.trans (by rw [hpayload'']))⟩
              have hdown : r.output.preparation.coordinator.downView = some selected.view := by
                simp [ReferenceActivePhysicalStep.DispatchCut.downView, hselection']
              refine ⟨hnextPhase, Or.inr ⟨selected, hselection', hpayload⟩,
                Or.inr ⟨selected.view, hdown, hpayload⟩, ?_⟩
              intro i
              exact ReferenceFirstReplacementCollectionFollowerPrefix.actualSelection_expectedDownWord_none_or_payload
                r selected payload hselection' hpayload i
      | laterChosen core consistent started startEq instruction instructionEq output localEq
          clockData installation selected =>
          have hdispatchCut : ReferenceActivePhysicalStep.dispatch r.input =
              .collection payload ledger clock cutoff
                (.laterChosen core consistent started startEq instruction instructionEq output localEq
                  clockData installation selected) := by
            simp [ReferenceActivePhysicalStep.dispatch, hcollection, hvalid, cutoff, clock,
              collectionInput, CoordinatorRoundDispatch.dispatch, hdispatch]; rfl
          have hfalse := hn
          simp [ReferenceCollectionPhaseHistory.laterChosen,
            ReferenceActivePhysicalStep.prepare, hdispatchCut] at hfalse
      | clockFailure failure startEq =>
          have hdispatchCut : ReferenceActivePhysicalStep.dispatch r.input =
              .collection payload ledger clock cutoff (.clockFailure failure startEq) := by
            simp [ReferenceActivePhysicalStep.dispatch, hcollection, hvalid, cutoff, clock,
              collectionInput, CoordinatorRoundDispatch.dispatch, hdispatch]; rfl
          have hselection : r.output.preparation.coordinator.selection = none := by
            calc
              r.output.preparation.coordinator.selection =
                  (ReferenceActivePhysicalStep.dispatch r.input).selection :=
                congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut r.input =>
                  coordinator.selection) hcoord
              _ = none := by rw [hdispatchCut]; simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          have hnotDagger : r.output.preparation.coordinator ≠ .dagger := by
            intro h
            have h' : ReferenceActivePhysicalStep.dispatch r.input = .dagger := hcoord.symm.trans h
            rw [hdispatchCut] at h'
            cases h'
          exact actual_no_selection_dispatch_step r payload hselection hnotDagger
      | localFailure started startEq coreInvalid failure =>
          have hdispatchCut : ReferenceActivePhysicalStep.dispatch r.input =
              .collection payload ledger clock cutoff
                (.localFailure started startEq coreInvalid failure) := by
            simp [ReferenceActivePhysicalStep.dispatch, hcollection, hvalid, cutoff, clock,
              collectionInput, CoordinatorRoundDispatch.dispatch, hdispatch]; rfl
          have hselection : r.output.preparation.coordinator.selection = none := by
            calc
              r.output.preparation.coordinator.selection =
                  (ReferenceActivePhysicalStep.dispatch r.input).selection :=
                congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut r.input =>
                  coordinator.selection) hcoord
              _ = none := by rw [hdispatchCut]; simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          have hnotDagger : r.output.preparation.coordinator ≠ .dagger := by
            intro h
            have h' : ReferenceActivePhysicalStep.dispatch r.input = .dagger := hcoord.symm.trans h
            rw [hdispatchCut] at h'
            cases h'
          exact actual_no_selection_dispatch_step r payload hselection hnotDagger
      | coreFailure core started startEq failure =>
          have hdispatchCut : ReferenceActivePhysicalStep.dispatch r.input =
              .collection payload ledger clock cutoff
                (.coreFailure core started startEq failure) := by
            simp [ReferenceActivePhysicalStep.dispatch, hcollection, hvalid, cutoff, clock,
              collectionInput, CoordinatorRoundDispatch.dispatch, hdispatch]; rfl
          have hselection : r.output.preparation.coordinator.selection = none := by
            calc
              r.output.preparation.coordinator.selection =
                  (ReferenceActivePhysicalStep.dispatch r.input).selection :=
                congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut r.input =>
                  coordinator.selection) hcoord
              _ = none := by rw [hdispatchCut]; simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          have hnotDagger : r.output.preparation.coordinator ≠ .dagger := by
            intro h
            have h' : ReferenceActivePhysicalStep.dispatch r.input = .dagger := hcoord.symm.trans h
            rw [hdispatchCut] at h'
            cases h'
          exact actual_no_selection_dispatch_step r payload hselection hnotDagger
      | laterReconstructionFailure core consistent started startEq instruction instructionEq failure laterEq =>
          have hdispatchCut : ReferenceActivePhysicalStep.dispatch r.input =
              .collection payload ledger clock cutoff
                (.laterReconstructionFailure core consistent started startEq instruction instructionEq failure laterEq) := by
            simp [ReferenceActivePhysicalStep.dispatch, hcollection, hvalid, cutoff, clock,
              collectionInput, CoordinatorRoundDispatch.dispatch, hdispatch]; rfl
          have hselection : r.output.preparation.coordinator.selection = none := by
            calc
              r.output.preparation.coordinator.selection =
                  (ReferenceActivePhysicalStep.dispatch r.input).selection :=
                congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut r.input =>
                  coordinator.selection) hcoord
              _ = none := by rw [hdispatchCut]; simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          have hnotDagger : r.output.preparation.coordinator ≠ .dagger := by
            intro h
            have h' : ReferenceActivePhysicalStep.dispatch r.input = .dagger := hcoord.symm.trans h
            rw [hdispatchCut] at h'
            cases h'
          exact actual_no_selection_dispatch_step r payload hselection hnotDagger
      | laterPrefixFailure core consistent started startEq instruction instructionEq arm failure laterEq =>
          have hdispatchCut : ReferenceActivePhysicalStep.dispatch r.input =
              .collection payload ledger clock cutoff
                (.laterPrefixFailure core consistent started startEq instruction instructionEq arm failure laterEq) := by
            simp [ReferenceActivePhysicalStep.dispatch, hcollection, hvalid, cutoff, clock,
              collectionInput, CoordinatorRoundDispatch.dispatch, hdispatch]; rfl
          have hselection : r.output.preparation.coordinator.selection = none := by
            calc
              r.output.preparation.coordinator.selection =
                  (ReferenceActivePhysicalStep.dispatch r.input).selection :=
                congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut r.input =>
                  coordinator.selection) hcoord
              _ = none := by rw [hdispatchCut]; simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          have hnotDagger : r.output.preparation.coordinator ≠ .dagger := by
            intro h
            have h' : ReferenceActivePhysicalStep.dispatch r.input = .dagger := hcoord.symm.trans h
            rw [hdispatchCut] at h'
            cases h'
          exact actual_no_selection_dispatch_step r payload hselection hnotDagger
      | laterOrientationFailure core consistent started startEq instruction instructionEq set laterEq =>
          have hdispatchCut : ReferenceActivePhysicalStep.dispatch r.input =
              .collection payload ledger clock cutoff
                (.laterOrientationFailure core consistent started startEq instruction instructionEq set laterEq) := by
            simp [ReferenceActivePhysicalStep.dispatch, hcollection, hvalid, cutoff, clock,
              collectionInput, CoordinatorRoundDispatch.dispatch, hdispatch]; rfl
          have hselection : r.output.preparation.coordinator.selection = none := by
            calc
              r.output.preparation.coordinator.selection =
                  (ReferenceActivePhysicalStep.dispatch r.input).selection :=
                congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut r.input =>
                  coordinator.selection) hcoord
              _ = none := by rw [hdispatchCut]; simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          have hnotDagger : r.output.preparation.coordinator ≠ .dagger := by
            intro h
            have h' : ReferenceActivePhysicalStep.dispatch r.input = .dagger := hcoord.symm.trans h
            rw [hdispatchCut] at h'
            cases h'
          exact actual_no_selection_dispatch_step r payload hselection hnotDagger
      | laterChoiceFailure core consistent started startEq instruction instructionEq output localEq clockData installation failure =>
          have hdispatchCut : ReferenceActivePhysicalStep.dispatch r.input =
              .collection payload ledger clock cutoff
                (.laterChoiceFailure core consistent started startEq instruction instructionEq output localEq clockData installation failure) := by
            simp [ReferenceActivePhysicalStep.dispatch, hcollection, hvalid, cutoff, clock,
              collectionInput, CoordinatorRoundDispatch.dispatch, hdispatch]; rfl
          have hselection : r.output.preparation.coordinator.selection = none := by
            calc
              r.output.preparation.coordinator.selection =
                  (ReferenceActivePhysicalStep.dispatch r.input).selection :=
                congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut r.input =>
                  coordinator.selection) hcoord
              _ = none := by rw [hdispatchCut]; simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          have hnotDagger : r.output.preparation.coordinator ≠ .dagger := by
            intro h
            have h' : ReferenceActivePhysicalStep.dispatch r.input = .dagger := hcoord.symm.trans h
            rw [hdispatchCut] at h'
            cases h'
          exact actual_no_selection_dispatch_step r payload hselection hnotDagger
    · have hdispatchCut :
          ReferenceActivePhysicalStep.dispatch r.input = .invalidCollectionCutoff := by
        simp [ReferenceActivePhysicalStep.dispatch, hcollection, hvalid]
      have hcoord := actualPreparation_dispatch_eq r
      have hselection : r.output.preparation.coordinator.selection = none := by
        calc
          r.output.preparation.coordinator.selection =
              (ReferenceActivePhysicalStep.dispatch r.input).selection :=
            congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut r.input =>
              coordinator.selection) hcoord
          _ = none := by rw [hdispatchCut]; simp [ReferenceActivePhysicalStep.DispatchCut.selection]
      have hnotDagger : r.output.preparation.coordinator ≠ .dagger := by
        intro h
        have h' : ReferenceActivePhysicalStep.dispatch r.input = .dagger := hcoord.symm.trans h
        rw [hdispatchCut] at h'
        cases h'
      exact actual_no_selection_dispatch_step r payload hselection hnotDagger

/-- Actual first replacement collection dispatch and old-payload view origin
on every physical record before the next later-choice branch. The physical
suffix, first-live window, replacement birth, cutoff, and collection window
are all the existing source carriers; no successful-chain input is supplied.
-/
theorem complete_first_replacement_collection_dispatch_origin
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
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
          | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let M (i : Fin (p.m - 1)) := payload.downRecord i
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := ReferenceCollectionPhaseHistory.collectionWindow R c
            let E (j : ℕ) := ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            (cut.output.next.coordinator = .dagger ∨
              ∃ ledger saved,
                cut.output.next.coordinator = .collection payload ledger saved) ∧
            ∀ j : Fin W.length,
              let r := W.get j
              (r.input.state.coordinator = .dagger ∨
                ∃ ledger saved,
                  r.input.state.coordinator = .collection payload ledger saved) ∧
              (r.output.next.coordinator = .dagger ∨
                ∃ ledger saved,
                  r.output.next.coordinator = .collection payload ledger saved) ∧
              (r.output.preparation.coordinator.selection = none ∨
                ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
                  r.output.preparation.coordinator.selection = some selected ∧
                    selected.view.payload = payload) ∧
              (r.output.preparation.coordinator.downView = none ∨
                ∃ view : ReferenceDownReception.ChoiceTimeView p rate.eta,
                  r.output.preparation.coordinator.downView = some view ∧
                    view.payload = payload) ∧
              ∀ i : Fin (p.m - 1),
                let expected := ReferenceDownReception.expectedDownFlatWord
                  r.output.preparation.coordinator.downView i r.input.row r.input.time
                expected = none ∨
                  expected = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)
          | _ => True
      | _ => True := by
  classical
  have hcutoff :=
    Bandits.Support.ReferenceFirstReplacementCutoffDownRecovery.complete_first_replacement_cutoff_down_recovery_and_finish
      rate source rewards C_star C_h
  dsimp only at hcutoff ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hbirthGet : R[v]? with
  | none => trivial
  | some birth =>
      simp only [hbirthGet] at hcutoff ⊢
      cases hbirthCoord : birth.output.preparation.coordinator with
      | first _ => trivial
      | live _ _ _ _ => trivial
      | dagger => trivial
      | invalidCollectionCutoff => trivial
      | collection _ _ _ _ outcome =>
          rw [hbirthCoord] at hcutoff
          cases outcome <;> try trivial
          rename_i core consistent started hstart instruction hinstruction output hconsistent
            clockData installed selected
          dsimp only at hcutoff ⊢
          let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
          let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
          cases hcutGet : R[v + 1 + tail.length]? with
          | none => trivial
          | some cut =>
              simp only [tail, hcutGet] at hcutoff ⊢
              cases hcutCoord : cut.output.preparation.coordinator with
              | first _ => trivial
              | collection _ _ _ _ _ => trivial
              | dagger => trivial
              | invalidCollectionCutoff => trivial
              | live registers owned base cutoffOutcome =>
                  rw [hcutCoord] at hcutoff
                  cases cutoffOutcome <;> try trivial
                  rename_i dispatched hstarted ledger hinitEq hledgerEq hdata hclock
                    hpending hassignment selected
                  dsimp only at hcutoff ⊢
                  rcases hcutoff.2 with
                    ⟨hregisterPayload, _, _, _, _, _, _, _, _, _, _, hselectedBlock⟩
                  rcases hselectedBlock with
                    ⟨selectedCut, hselectionCut, _hselectedPayload, _, _, _⟩
                  have hcutPhase : cut.output.next.coordinator = .dagger ∨
                      ∃ nextLedger nextSaved,
                        cut.output.next.coordinator = .collection payload nextLedger nextSaved := by
                    have hcoordEq := actualPreparation_dispatch_eq cut
                    have hselection : cut.output.preparation.coordinator.selection =
                        some selectedCut := by
                      calc
                        cut.output.preparation.coordinator.selection =
                            (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
                              (.cutoffChosen dispatched hstarted ledger hinitEq hledgerEq hdata
                                hclock hpending hassignment selected)).selection :=
                          congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut cut.input =>
                            coordinator.selection) hcutCoord
                        _ = some selectedCut := hselectionCut
                    have hpayload : registers.payload = payload := hregisterPayload
                    have hselection' :
                        (ReferenceActivePhysicalStep.prepare cut.input).coordinator.selection =
                          some selectedCut := by
                      calc
                        (ReferenceActivePhysicalStep.prepare cut.input).coordinator.selection =
                            (ReferenceActivePhysicalStep.dispatch cut.input).selection := rfl
                        _ = cut.output.preparation.coordinator.selection :=
                          (congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut cut.input =>
                            coordinator.selection) hcoordEq).symm
                        _ = some selectedCut := hselection
                    have hcoord' :
                        (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
                          .live registers owned base
                            (.cutoffChosen dispatched hstarted ledger hinitEq hledgerEq hdata
                              hclock hpending hassignment selected) := by
                      calc
                        (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
                            ReferenceActivePhysicalStep.dispatch cut.input := rfl
                        _ = cut.output.preparation.coordinator := hcoordEq.symm
                        _ = .live registers owned base
                              (.cutoffChosen dispatched hstarted ledger hinitEq hledgerEq hdata
                                hclock hpending hassignment selected) := hcutCoord
                    have hcutSelection :
                        (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
                          (.cutoffChosen dispatched hstarted ledger hinitEq hledgerEq hdata
                            hclock hpending hassignment selected)).selection = some selectedCut := by
                      calc
                        (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
                          (.cutoffChosen dispatched hstarted ledger hinitEq hledgerEq hdata
                            hclock hpending hassignment selected)).selection =
                            (ReferenceActivePhysicalStep.prepare cut.input).coordinator.selection :=
                          (congrArg (fun coordinator : ReferenceActivePhysicalStep.DispatchCut cut.input =>
                            coordinator.selection) hcoord').symm
                        _ = some selectedCut := hselection'
                    let weights :=
                      (ReferenceActivePhysicalStep.liveRegistersAt registers cut.input.time).complementWeights
                    have hnext : cut.output.next.coordinator =
                        (ReferenceActivePhysicalStep.collectionPostChoice
                          (x := cut.input) (ReferenceActivePhysicalStep.prepare cut.input)
                          registers.payload (ReferenceActivePhysicalStep.sharedLedger ledger)
                          dispatched.startResult weights).configuration := by
                      calc
                        cut.output.next.coordinator =
                            (ReferenceActivePhysicalStep.step cut.input).next.coordinator :=
                          congrArg (fun out : ReferenceActivePhysicalStep.RoundOutput cut.input =>
                            out.next.coordinator) cut.output_eq
                        _ = (ReferenceActivePhysicalStep.prepare cut.input).observeCoordinator.configuration := rfl
                        _ = (ReferenceActivePhysicalStep.collectionPostChoice
                            (x := cut.input) (ReferenceActivePhysicalStep.prepare cut.input)
                            registers.payload (ReferenceActivePhysicalStep.sharedLedger ledger)
                            dispatched.startResult weights).configuration := by
                          simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
                            hcoord', hcutSelection, weights]
                    have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
                      (ReferenceActivePhysicalStep.prepare cut.input) registers.payload
                      (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult weights
                    have hframe := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
                      (ReferenceActivePhysicalStep.prepare cut.input) registers.payload
                      (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult weights
                    have hnextPhase : cut.output.next.coordinator = .dagger ∨
                        ∃ nextLedger nextSaved,
                          cut.output.next.coordinator = .collection payload nextLedger nextSaved := by
                      rcases hphase with hdagger |
                        ⟨nextPayload, nextLedger, nextSaved, hconfiguration⟩
                      · exact Or.inl (hnext.trans hdagger)
                      · rcases hframe with hnone | hpayloadFrame
                        · simp [ReferenceAssignmentPayloadPersistence.storedPayload,
                            hconfiguration] at hnone
                        · have hpayloadNext : nextPayload = registers.payload := by
                            have hsome : some nextPayload = some registers.payload := by
                              simpa [ReferenceAssignmentPayloadPersistence.storedPayload,
                                hconfiguration] using hpayloadFrame
                            exact Option.some.inj hsome
                          have hpayloadNext' : nextPayload = payload :=
                            hpayloadNext.trans hpayload
                          exact Or.inr ⟨nextLedger, nextSaved,
                            hnext.trans (hconfiguration.trans (by rw [hpayloadNext']))⟩
                    exact hnextPhase
                  let c := v + 1 + tail.length
                  let W := (R.drop (c + 1)).takeWhile
                    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
                  have hcutOption : R[c]? = some cut := by
                    simpa [c] using hcutGet
                  obtain ⟨hcutlt, hcutval⟩ := List.getElem?_eq_some_iff.mp hcutOption
                  have hcutrecord : R.get ⟨c, hcutlt⟩ = cut := by
                    simpa only [List.get_eq_getElem] using hcutval
                  have hseq : ∀ j (hj : j < W.length),
                      Exists (fun (hc : (W.get ⟨j, hj⟩).input.state.coordinator = .dagger ∨
                          ∃ oldLedger oldSaved,
                            (W.get ⟨j, hj⟩).input.state.coordinator =
                              .collection payload oldLedger oldSaved) =>
                        Exists (fun (hn : ReferenceCollectionPhaseHistory.laterChosen
                            (W.get ⟨j, hj⟩).input = false) =>
                          True)) := by
                    intro j
                    induction j with
                    | zero =>
                        intro hj
                        let r := W.get ⟨0, hj⟩
                        have hget := ReferenceFirstReplacementCollectionFollowerPrefix.collectionWindow_get
                          R c 0 (by simpa [W] using hj)
                        obtain ⟨hrlt, hrval⟩ := List.getElem?_eq_some_iff.mp hget
                        have hrecord : R.get ⟨c + 1, hrlt⟩ = r := by
                          simpa only [c, W, r, List.get_eq_getElem] using hrval
                        have hadj := ReferenceFirstReplacementCollectionFollowerPrefix.completeSuffix_adjacent
                          source rewards C_star C_h c (by omega)
                        have hc : r.input.state.coordinator = .dagger ∨
                            ∃ oldLedger oldSaved,
                              r.input.state.coordinator = .collection payload oldLedger oldSaved := by
                          have hstate := hadj.1
                          rw [hrecord] at hstate
                          rw [hcutrecord] at hstate
                          rw [hstate]
                          exact hcutPhase
                        have hmem : r ∈ W := by
                          exact List.get_mem W ⟨0, hj⟩
                        have hnot : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
                          have hpred := List.mem_takeWhile_imp hmem
                          cases hvalue : ReferenceCollectionPhaseHistory.laterChosen r.input <;>
                            simp [hvalue] at hpred ⊢
                        exact ⟨hc, hnot, trivial⟩
                    | succ j ih =>
                        intro hj
                        have hj' : j < W.length := by
                          omega
                        obtain ⟨hcPrev, hnPrev, _⟩ := ih hj'
                        let prev := W.get ⟨j, hj'⟩
                        let r := W.get ⟨j + 1, hj⟩
                        have hstepPrev := actual_collection_dispatch_step prev payload hcPrev hnPrev
                        have hgetPrev := ReferenceFirstReplacementCollectionFollowerPrefix.collectionWindow_get
                          R c j (by simpa [W] using hj')
                        have hget := ReferenceFirstReplacementCollectionFollowerPrefix.collectionWindow_get
                          R c (j + 1) (by simpa [W] using hj)
                        obtain ⟨hprevlt, hprevval⟩ := List.getElem?_eq_some_iff.mp hgetPrev
                        obtain ⟨hrlt, hrval⟩ := List.getElem?_eq_some_iff.mp hget
                        have hprevrecord : R.get ⟨c + 1 + j, hprevlt⟩ = prev := by
                          simpa only [c, W, prev, List.get_eq_getElem] using hprevval
                        have hrecord : R.get ⟨c + 1 + (j + 1), hrlt⟩ = r := by
                          simpa only [c, W, r, List.get_eq_getElem] using hrval
                        have hadj := ReferenceFirstReplacementCollectionFollowerPrefix.completeSuffix_adjacent
                          source rewards C_star C_h (c + 1 + j) (by omega)
                        have hc : r.input.state.coordinator = .dagger ∨
                            ∃ oldLedger oldSaved,
                              r.input.state.coordinator = .collection payload oldLedger oldSaved := by
                          have hstate := hadj.1
                          have hstate' : r.input.state = prev.output.next := by
                            calc
                              r.input.state = (R.get ⟨c + 1 + (j + 1), hrlt⟩).input.state := by
                                rw [← hrecord]
                              _ = (R.get ⟨c + 1 + j, hprevlt⟩).output.next := by
                                convert hstate using 1
                              _ = prev.output.next := by rw [hprevrecord]
                          rw [hstate']
                          exact hstepPrev.1
                        have hmem : r ∈ W := by
                          exact List.get_mem W ⟨j + 1, hj⟩
                        have hnot : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
                          have hpred := List.mem_takeWhile_imp hmem
                          cases hvalue : ReferenceCollectionPhaseHistory.laterChosen r.input <;>
                            simp [hvalue] at hpred ⊢
                        exact ⟨hc, hnot, trivial⟩
                  let K := ReferenceCollectionPhaseHistory.collectionWindow R c
                  let E (j : ℕ) := ReferenceCollectionSegmentExtraction.endpointState
                    cut.output.next (W.take j)
                  refine And.intro hcutPhase ?_
                  intro j
                  obtain ⟨hc, hn, _⟩ := hseq j.val j.isLt
                  refine ⟨hc, ?_⟩
                  exact actual_collection_dispatch_step (W.get j) payload hc hn

end Bandits.Support.ReferenceFirstReplacementCollectionDispatchOrigin

end
