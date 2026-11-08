/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionPureUpAcceptanceRoot

import Lean.Elab.Tactic.Omega

/-!
# Selected UP receiver and awaited-offer fields in the first replacement collection

This is a deterministic per-round query for every selected UP receiver in the
continuing first replacement collection, including rounds with zero receiver
observations. It asserts no decoder event or probability bound.
-/

@[expose] public section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstReplacementCollectionSelectedUpAwaitedFields

private theorem selected_up_fields
    {p : ConstructorDimensions.Parameters}
    (slice : ContinuousLearningRows.Slice p)
    (i : Fin (p.m - 1))
    (h : ReferenceSelectedAffinePairLaw.selectedChannel p slice =
      some (1, Fin.cast (show p.m - 1 = ContinuousLearningRows.d p by rfl) i)) :
    PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.upSlot ∧
      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K slice).val = i.val := by
  classical
  unfold ReferenceSelectedAffinePairLaw.selectedChannel
    ReferenceSelectedAffinePairLaw.channelFromDraws at h
  split_ifs at h with hd hu
  · have hdirection := congrArg Prod.fst (Option.some.inj h)
    exact (zero_ne_one hdirection).elim
  · refine ⟨hu, ?_⟩
    have hdraw := (Prod.mk.inj (Option.some.inj h)).2
    calc
      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K slice).val =
          (Fin.cast (show p.m - 1 = ContinuousLearningRows.d p by rfl) i).val :=
        congrArg Fin.val hdraw
      _ = i.val := rfl

/-- Actual selected UP rounds in the first replacement collection expose
their checked offer and the corresponding local receiver and acceptance
fields. The statement includes zero observations and makes no success claim. -/
theorem complete_first_replacement_collection_selected_up_awaited_fields
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
              let prior := (ReferenceCollectionPhaseHistory.acceptedLabels
                (K.take (j.val + 1))).toFinset
              match r.output.next.coordinator with
              | .dagger => True
              | _ =>
                ∀ i : Fin (p.m - 1),
                  ReferenceSelectedAffinePairLaw.selectedChannel p
                    (r.input.row.2 r.input.time).1 =
                      some (1, Fin.cast
                        (show p.m - 1 = ContinuousLearningRows.d p by rfl) i) →
                  ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
                    (memory : ActiveFollowerLifecycle.LocalMemory p)
                    (U : OrdinaryMessageCodec.UpRecord
                      (ReferencePrelaunchFollower.codecParams p rate.eta))
                    (L : ReferenceActivePhysicalStep.Ledger rate)
                    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                    (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                      .ordinary state memory ∧ state.status = .unoccupied ∧
                    U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                    ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
                      (r.input.state.activations i) r.input.time state = .offer U ∧
                    ReferenceActiveAffinePositiveTest.upSent r.input =
                      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                    ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
                    CoordinatorUpReception.receptionInputCheck
                      (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true ∧
                    r.output.coordinator.up = some d ∧
                    d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
                    d.input.selectedFollower = i ∧
                    d.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                    L.sigma = payload.sigma.val + 1 ∧ L.cutoff = u ∧
                    L.cursor = r.input.time.val + 1 ∧ L.cutoff ≤ L.cursor ∧
                    L.pending = Finset.univ \ prior ∧
                    ((CoordinatorUpReception.roundInput d.input).selected = true ↔
                      i ∉ prior) ∧
                    (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
                    ((ReferencePrelaunchFollower.acceptedStart state <
                        (payload.downRecord i).val.sigma ∧
                      U.val.sigma < (payload.downRecord i).val.sigma ∧
                      CoordinatorCollectionLedger.acceptUpCheck L i U = false) ∨
                     (state.lastDown = some (payload.downRecord i) ∧
                      U.val.sigma = (payload.downRecord i).val.sigma ∧
                      (CoordinatorCollectionLedger.acceptUpCheck L i U = true ↔
                        i ∉ prior)))
          | _ => True
      | _ => True := by
  classical
  have hB :=
    ReferenceFirstReplacementCollectionUpStartedFields.complete_first_replacement_collection_up_started_fields
      rate source rewards C_star C_h
  have hR :=
    ReferenceFirstReplacementCollectionUpReceiverProvenance.complete_first_replacement_collection_up_receiver_provenance
      rate source rewards C_star C_h
  dsimp only at hB hR
  simp (config := { zeta := true }) only [] at ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hB hR ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hB hR ⊢
      cases outcome <;> try trivial
      rename_i core consistent birthStarted hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hB hR
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      rcases hR with ⟨_, _, hR⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [hc] at hB hR ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hB hR ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hB hR
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          rcases hR with ⟨_, hrecords, _⟩
          intro j
          let r := W.get j
          let prior := (ReferenceCollectionPhaseHistory.acceptedLabels
            (K.take (j.val + 1))).toFinset
          let k : Fin K.length := ⟨j.val + 1, by
            have hjW : j.val < W.length := j.isLt
            change j.val + 1 < W.length + 1
            omega⟩
          have hkval : k.val = j.val + 1 := rfl
          have hget : K.get k = r := by simp [K, k, r]
          have hBrecord := hB j
          have hRrecord := hrecords k
          rw [hget] at hRrecord
          cases hnext :
              (((R.drop (c + 1)).takeWhile
                (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).get j).output.next.coordinator <;>
            try trivial
          all_goals simp only [hnext] at hBrecord ⊢
          all_goals
            intro i hchannel
            rcases hBrecord with ⟨localLedger, saved, t, recording, started, d,
              hstate, htail, hrecording, hstart, hsite, hcheck, hdiagnostic,
              hinput, hexpectedActual, htailReception, hnotInvalid, hstartedSigma,
              hcutoff, hcursor, hcutCursor, hstartedPending, hmembership, _⟩
            have htailW :
                ReferenceCollectionPhaseHistory.executedTail (W.get j).input = some t := by
              simpa only [r] using htail
            dsimp only [K, k] at hRrecord
            rw [htailW] at hRrecord
            cases hrec : t.reception with
            | none =>
                rw [hrec] at htailReception
                cases htailReception
            | some pair =>
              rcases pair with ⟨startedR, receivedR⟩
              have hpair : (startedR, receivedR) =
                  (started, ReferenceActivePhysicalStep.receiveUp
                    (ReferenceActivePhysicalStep.prepare r.input) started) :=
                Option.some.inj (hrec.symm.trans htailReception)
              rcases Prod.mk.inj hpair with ⟨hstartedEq, hreceivedEq⟩
              subst startedR
              subst receivedR
              simp only [hrec] at hRrecord
              rcases hRrecord with
                ⟨hsigmaR, hcutoffR, hcursorR, hpendingR, hgateR, hofferR, hdiagR⟩
              cases hdiag : (ReferenceActivePhysicalStep.receiveUp
                  (ReferenceActivePhysicalStep.prepare r.input) started).diagnostic with
              | none =>
                  simp only [hdiag] at hdiagR
                  rcases hdiagR with ⟨_, _, houtputNone⟩
                  rw [houtputNone] at hdiagnostic
                  cases hdiagnostic
              | some diagnostic =>
                simp only [hdiag] at hdiagR
                rcases hdiagR with ⟨hinputR, _, _, _, houtputR⟩
                have hdiagEq : diagnostic = d :=
                  Option.some.inj (houtputR.symm.trans hdiagnostic)
                subst diagnostic
                have hselectedRound := selected_up_fields
                  (r.input.row.2 r.input.time).1 i hchannel
                have hslot : PublicDiscreteDraws.slotDraw
                    ((r.input.row.2 r.input.time).1) = PublicDiscreteDraws.upSlot :=
                  hselectedRound.1
                have hsender : ReferenceActivePhysicalStep.upSenderIndex r.input = i := by
                  rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]
                  apply Fin.ext
                  exact hselectedRound.2
                rw [hsender] at hofferR
                rcases hofferR hslot with
                  ⟨state, memory, U, hconfiguration, hchecked, hfields,
                    hexpectedOffer, horigin⟩
                have hconfigurationActual :
                    (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                      .ordinary state memory := by
                  simpa [ReferenceFollowerFixedReply.actualChoice] using hconfiguration
                have hgate : CoordinatorUpReception.receptionGate d.input ↔
                    i ∉ prior := by
                  rw [hinputR, hgateR]
                  rw [hslot, hsender]
                  simp only [prior, K, W, true_and]
                have hselected : (CoordinatorUpReception.roundInput d.input).selected = true ↔
                    i ∉ prior := by
                  rw [CoordinatorUpReception.roundInput_selected_iff_gate, hgate]
                have hselectedInput : d.input.selectedFollower = i := by
                  have htmp : d.input.selectedFollower =
                      ReferenceActivePhysicalStep.upSenderIndex r.input := by
                    simpa only [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
                      ReferenceActivePhysicalStep.upInputs,
                      ReferenceUpReception.receptionInputAtRow_selectedFollower,
                      ReferenceActivePhysicalStep.RoundInput.row,
                      CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw,
                      ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw] using
                      congrArg CoordinatorUpReception.ReceptionInput.selectedFollower hinput
                  exact htmp.trans hsender
                have hfieldsStarted : started.pending = Finset.univ \ prior := by
                  simpa only [hkval, prior] using hpendingR
                have horigin' := horigin
                rw [hfieldsStarted] at horigin'
                have hstatus : state.status = .unoccupied := by
                  unfold ActiveFollowerQueueOperation.checkedUpOffer at hchecked
                  split_ifs at hchecked with hdomain hselectedOffer hadmissible
                  · exact hselectedOffer.2
                refine ⟨state, memory, U, started, d, ?_⟩
                refine ⟨hconfigurationActual, hstatus, hfields, hchecked, ?_, hsite, hcheck,
                  hdiagnostic, hinput, hselectedInput, ?_, hstartedSigma, hcutoff, hcursor,
                  hcutCursor, hfieldsStarted, hselected, rfl, ?_⟩
                · simpa only [ReferenceActiveAffinePositiveTest.upSent] using hexpectedOffer
                · rw [hexpectedActual]
                  exact hexpectedOffer
                · rcases horigin' with hold | ⟨hcurrent, hcurrentSigma, haccept⟩
                  · exact Or.inl hold
                  · right
                    refine ⟨hcurrent, hcurrentSigma, ?_⟩
                    simpa [Finset.mem_sdiff, Finset.mem_univ, prior, K] using haccept

end Bandits.Support.ReferenceFirstReplacementCollectionSelectedUpAwaitedFields

end
