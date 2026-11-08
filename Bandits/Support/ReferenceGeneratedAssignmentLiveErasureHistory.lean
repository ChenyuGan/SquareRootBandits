/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInstallationFollowerSeed

import Lean.Elab.Tactic.Omega

/-!
# Generated live assignment birth initialization

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109`,
`sources/zip4/manuscript/05_binary_transport.tex:60-88,100-124`,
`sources/zip4/manuscript/06_interruptions.tex:41-70,246-295,303-348`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

This module starts the generated same-assignment live-history construction
from the real installation record selected by the actual run. It recovers the
birth date and the ordinary focal CHOICE configuration from the whole
generated execution, then consumes the accepted generated-installation
initializer to retain its real incoming fields. It does not assert that the
assignment continues without a cutoff or produce pending-erasure history.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceGeneratedDownBatchCalendar
open ReferenceGeneratedInheritedDownWrongCompletionWitness
open ReferenceAssignmentPayloadPersistence
open ReferenceCollectionPhaseHistory

namespace Bandits.Support.ReferenceGeneratedAssignmentLiveErasureHistory

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private abbrev Record :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

private theorem generated_seed_initial_facts
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs) :
    let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
      rate rewards C_star C_h s hs x
    ReferenceActivePhysicalHorizon.allActiveAtStart seed s ∧
      seed.coordinator = .first ∧
      ReferenceFirstLiveConfirmationHistory.InitialFollowers seed := by
  classical
  dsimp only
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs x
  have hseed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
    rate rewards C_star C_h s hs x
  obtain ⟨active, hactive, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate x.val rewards C_star C_h x.property.1
  have hseedActive : seed = active :=
    Option.some.inj (hseed.1.symm.trans hactive.1)
  obtain ⟨activeFields, hfieldsLaunch, hfields⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
      rate x.val rewards C_star C_h x.property.1
  have hseedFields : seed = activeFields :=
    Option.some.inj (hseed.1.symm.trans hfieldsLaunch)
  have hfirst : seed.coordinator = .first := by
    rw [hseedActive]
    exact hactive.2.1
  have hfollowers :
      ReferenceFirstLiveConfirmationHistory.InitialFollowers seed := by
    intro i state memory hconfiguration
    rcases hfields i with ⟨hconfiguration', hlastDown, _, _, _, _, hunoccupied, _⟩
    have hconfiguration'' :
        seed.followers i = .ordinary
          (ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate))
            (ActualReferenceInitializationBlock.refFollower i))
          (ActiveFollowerLifecycle.initialMemory p) := by
      rw [hseedFields]
      exact hconfiguration'
    rw [hconfiguration''] at hconfiguration
    cases hconfiguration
    exact ⟨hunoccupied, hlastDown⟩
  exact ⟨hseed.2.1, hfirst, hfollowers⟩

private theorem generated_record_input_eq_nextInput
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
      (generated_seed_initial_facts rate rewards C_star C_h s hs x).1 := by
  classical
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs x
  have hseed := generated_seed_initial_facts rate rewards C_star C_h s hs x
  let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := hseed.1
  let rows := x.val.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p x.val
  let total := ReferenceActivePhysicalHorizon.run seed rows selected rewards s
    (p.T - s) (by omega) hmode
  let prefixRun := ReferenceActivePhysicalHorizon.run seed rows selected rewards s n.val
    (by omega) hmode
  let through := ReferenceActivePhysicalHorizon.run seed rows selected rewards s (n.val + 1)
    (by omega) hmode
  have hgenerated : ReferenceGeneratedDownBatchCalendar.generatedSourceRun
      rate rewards C_star C_h s hs x = total := rfl
  have htotalCount : total.records.length = p.T - s :=
    ReferenceActivePhysicalHorizon.run_record_count seed rows selected rewards s
      (p.T - s) (by omega) hmode
  have hrecord (j : Fin (p.T - s)) :
      total.records[j.val]'(by omega) =
        ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x j := by
    have hget := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
      rate rewards C_star C_h s hs x j
    rw [hgenerated,
      List.getElem?_eq_getElem (by rw [htotalCount]; exact j.isLt)] at hget
    exact Option.some.inj hget
  obtain ⟨suffix, hrecords⟩ :=
    ReferenceCollectionPhaseHistory.run_records_prefix seed rows selected rewards s
      (n.val + 1) (p.T - s - (n.val + 1)) (by omega) hmode
  have hrecordsTotal : total.records = through.records ++ suffix := by
    simpa [total, through, hgenerated] using hrecords
  have hthroughSuccessor : through.records = prefixRun.records ++
      [ReferenceAssignmentPayloadChronology.actualRunRecordAt seed rows selected rewards s n.val
        (by omega) hmode] := by
    simpa only [through, prefixRun] using
      ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt seed rows selected
        rewards s n.val (by omega) hmode
  have hprefixCount : prefixRun.records.length = n.val :=
    ReferenceActivePhysicalHorizon.run_record_count seed rows selected rewards s n.val
      (by omega) hmode
  have hthroughCount : through.records.length = n.val + 1 :=
    ReferenceActivePhysicalHorizon.run_record_count seed rows selected rewards s (n.val + 1)
      (by omega) hmode
  have hcalendarRecord? : total.records[n.val]? =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt seed rows selected rewards s n.val
        (by omega) hmode) := by
    rw [hrecordsTotal]
    rw [List.getElem?_append_left (by rw [hthroughCount]; omega)]
    rw [hthroughSuccessor]
    rw [List.getElem?_append_right (by omega)]
    simp [hprefixCount]
  have hgeneratedRecord? : total.records[n.val]? = some
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n) := by
    rw [List.getElem?_eq_getElem (by rw [htotalCount]; exact n.isLt)]
    rw [hrecord n]
  have hrecordIdentity := Option.some.inj (hcalendarRecord?.symm.trans hgeneratedRecord?)
  have hinput :
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n).input =
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt seed rows selected rewards s n.val
        (by omega) hmode).input :=
    congrArg (fun record : Record => record.input) hrecordIdentity.symm
  calc
    _ = (ReferenceAssignmentPayloadChronology.actualRunRecordAt seed rows selected rewards s n.val
        (by omega) hmode).input := hinput
    _ = ReferenceCollectionPhaseHistory.nextInput seed rows selected rewards s n.val
        (by omega) hmode := rfl

private theorem prepared_live_input_state
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput x registers owned base))
    (hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live registers owned base outcome) :
    x.state.coordinator = .live registers owned base := by
  have hdispatch : ReferenceActivePhysicalStep.dispatch x = .live registers owned base outcome := by
    calc
      ReferenceActivePhysicalStep.dispatch x = (ReferenceActivePhysicalStep.prepare x).coordinator :=
        (ReferenceActivePhysicalStep.prepare x).coordinator_eq.symm
      _ = .live registers owned base outcome := hprepared
  cases hstate : x.state.coordinator with
  | first =>
      rw [ReferenceActivePhysicalStep.dispatch_first x hstate] at hdispatch
      cases hdispatch
  | live old oldOwned oldBase =>
      have hcut : ReferenceActivePhysicalStep.dispatch x =
          .live old oldOwned oldBase
            (CoordinatorRoundDispatch.dispatchLive
              (ReferenceActivePhysicalStep.liveInput x old oldOwned oldBase)) := by
        simp only [ReferenceActivePhysicalStep.dispatch, hstate,
          CoordinatorRoundDispatch.dispatch]
        rfl
      rw [hcut] at hdispatch
      cases hdispatch
      rfl
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
        cases hrun : CoordinatorRoundDispatch.dispatch (.collection source) with
        | collection actual =>
            have hcut : ReferenceActivePhysicalStep.dispatch x =
                .collection payload ledger clock cutoff actual := by
              simp only [ReferenceActivePhysicalStep.dispatch, hstate, dite_eq_left hvalid,
                cutoff, clock]
              rw [hrun]
              rfl
            rw [hcut] at hdispatch
            cases hdispatch
      · have hcut : ReferenceActivePhysicalStep.dispatch x = .invalidCollectionCutoff := by
          simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid]
        rw [hcut] at hdispatch
        cases hdispatch
  | dagger =>
      rw [ReferenceActivePhysicalStep.dispatch_dagger x hstate] at hdispatch
      cases hdispatch

/-- The actual selected payload in a continuing generated LIVE branch has a
real earlier installation birth on the same generated execution. The
ordinary focal CHOICE at the endpoint is traced back through the actual
connected run to an ordinary CHOICE at that birth, where the admitted seed
initializer proves unoccupied status and frames all real incoming follower
fields. The output retains the original rows, selected private row `J`, and
whole reward table through the original launch source.
-/
theorem generated_live_actual_payload_birth_initializer
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (n : Fin (p.T - s)) (i : Fin (p.m - 1)) :
    let Rn := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x n
    match Rn.output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen _ _ _ _) =>
        ∀ (selected : ReferenceActivePhysicalStep.Selection Rn.input),
          Rn.output.preparation.coordinator.selection = some selected →
        ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFollowerFixedReply.actualChoice Rn i).configuration = .ordinary state memory →
        ∃ (b : Fin (p.T - s)), b.val < n.val ∧
          let Rb := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
            rate rewards C_star C_h s hs x b
          ReferenceAssignmentPayloadPersistence.InstallationBirth Rb selected.view.payload ∧
          selected.view.payload.sigma.val = s + b.val ∧
          ∃ birthState birthMemory,
            (ReferenceFollowerFixedReply.actualChoice Rb i).configuration =
              .ordinary birthState birthMemory ∧
            birthState.status = .unoccupied ∧
            ∃ before beforeMemory,
              Rb.input.state.followers i = .ordinary before beforeMemory ∧
              before.status = .unoccupied ∧
              ReferenceFollowerReplyChronology.reply birthState =
                ReferenceFollowerReplyChronology.reply before ∧
              birthState.downBatch = before.downBatch ∧
              birthState.buffer = before.buffer ∧
              birthState.initializationFailure = before.initializationFailure ∧
              birthMemory = beforeMemory
    | _ => True := by
  classical
  dsimp only
  let Rn := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
    rate rewards C_star C_h s hs x n
  cases hcoord : Rn.output.preparation.coordinator with
  | first outcome => trivial
  | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation arm =>
          intro selected hselected state memory hchoice
          have hselectionAt :
              ReferenceActivePhysicalStep.selectionAt Rn.input registers.payload
                dispatched.startResult Rn.input.time
                (ReferenceActivePhysicalStep.liveRegistersAt registers Rn.input.time).complementWeights
                arm = some selected := by
            simpa only [hcoord, ReferenceActivePhysicalStep.DispatchCut.selection] using hselected
          have hpayload : selected.view.payload = registers.payload := by
            simp only [ReferenceActivePhysicalStep.selectionAt] at hselectionAt
            split at hselectionAt
            · exact (congrArg (fun value : ReferenceActivePhysicalStep.Selection Rn.input =>
                value.view.payload) (Option.some.inj hselectionAt)).symm
            · cases hselectionAt
          have hinputLive := prepared_live_input_state Rn.input registers owned base
            (.continuingChosen dispatched hstart continuation arm) (by
              change (ReferenceActivePhysicalStep.step Rn.input).preparation.coordinator = _
              rw [← Rn.output_eq]
              exact hcoord)
          have hstored :
              ReferenceAssignmentPayloadPersistence.storedPayload Rn.input.state.coordinator =
                some selected.view.payload := by
            simp [ReferenceAssignmentPayloadPersistence.storedPayload, hinputLive, hpayload]

          let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
            rate rewards C_star C_h s hs x
          let rows := x.val.1.2
          let J := ActualInitializationPhysicalStep.selectedRowIndex p x.val
          have hseed := generated_seed_initial_facts rate rewards C_star C_h s hs x
          let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := hseed.1
          have hfirst : seed.coordinator = .first := hseed.2.1
          let prefixRun := ReferenceActivePhysicalHorizon.run seed rows J rewards s n.val
            (by omega) hmode
          let total := ReferenceActivePhysicalHorizon.run seed rows J rewards s (p.T - s)
            (by omega) hmode
          have hinput : Rn.input = ReferenceCollectionPhaseHistory.nextInput seed rows J rewards s
              n.val (by omega) hmode := by
            simpa only [seed, rows, J] using
              generated_record_input_eq_nextInput rate rewards C_star C_h s hs x n
          have hstoredPrefix :
              ReferenceAssignmentPayloadPersistence.storedPayload prefixRun.finalState.coordinator =
                some selected.view.payload := by
            have hstate : Rn.input.state = prefixRun.finalState := by
              rw [hinput]
              rfl
            rw [hstate] at hstored
            exact hstored
          obtain ⟨birth, hbirthMem, hbirth, hbirthTime, _, _⟩ :=
            ReferenceAssignmentPayloadChronology.run_prefix_storedPayload_has_birth
              seed rows J rewards s (p.T - s) (by omega) hmode hfirst n.val
              (Nat.le_of_lt n.isLt) selected.view.payload hstoredPrefix
          obtain ⟨bval, hbval, hbirthPrefix⟩ := List.mem_iff_getElem.mp hbirthMem
          have htotalCount : total.records.length = p.T - s :=
            ReferenceActivePhysicalHorizon.run_record_count seed rows J rewards s (p.T - s)
              (by omega) hmode
          have hprefixCount : prefixRun.records.length = n.val :=
            ReferenceActivePhysicalHorizon.run_record_count seed rows J rewards s n.val
              (by omega) hmode
          have hbval_lt_n : bval < n.val := by
            rw [hprefixCount] at hbval
            exact hbval
          let b : Fin (p.T - s) := ⟨bval, by omega⟩
          obtain ⟨suffix, hsuffix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
              seed rows J rewards s n.val (p.T - s - n.val) (by omega) hmode
          have hcount : n.val + (p.T - s - n.val) = p.T - s := by omega
          have hrunEq : total.records = prefixRun.records ++ suffix := by
            simpa only [total, prefixRun, hcount] using hsuffix
          have htakePrefix : total.records.take n.val = prefixRun.records := by
            calc
              total.records.take n.val = (prefixRun.records ++ suffix).take n.val := by rw [hrunEq]
              _ = prefixRun.records.take n.val :=
                List.take_append_of_le_length (by rw [hprefixCount])
              _ = prefixRun.records := by rw [← hprefixCount, List.take_length]
          have hprefixGet? : prefixRun.records[bval]? = some birth := by
            rw [List.getElem?_eq_getElem (by rw [hprefixCount]; exact hbval_lt_n)]
            exact congrArg some hbirthPrefix
          have htotalGet? : total.records[bval]? = some birth := by
            calc
              total.records[bval]? = prefixRun.records[bval]? := by
                rw [hrunEq, List.getElem?_append_left (by rw [hprefixCount]; exact hbval_lt_n)]
              _ = some birth := hprefixGet?
          have hgeneratedRun : ReferenceGeneratedDownBatchCalendar.generatedSourceRun
              rate rewards C_star C_h s hs x = total := rfl
          have hsourceBirthGet? :=
            ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
              rate rewards C_star C_h s hs x b
          rw [hgeneratedRun] at hsourceBirthGet?
          have hbirthRecord : birth =
              ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
                rate rewards C_star C_h s hs x b :=
            (Option.some.inj (hsourceBirthGet?.symm.trans htotalGet?)).symm
          have hbirthRb :
              ReferenceAssignmentPayloadPersistence.InstallationBirth
                (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
                  rate rewards C_star C_h s hs x b) selected.view.payload := by
            rw [← hbirthRecord]
            exact hbirth
          have hbRecord :=
            ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
              rate rewards C_star C_h s hs x b
          have hRnGet :=
            ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
              rate rewards C_star C_h s hs x n
          have hcurrentInputFrame :=
            ReferenceFollowerReplyChronology.record_input_to_choice Rn i state memory hchoice
          obtain ⟨currentInputState, currentInputMemory, hcurrentInputOrdinary, _, _⟩ :=
            hcurrentInputFrame
          have hcurrentRecordGet? : total.records[n.val]? = some Rn := by
            simpa only [hgeneratedRun] using hRnGet
          have hcurrentRecord : total.records[n.val]'(by rw [htotalCount]; exact n.isLt) = Rn :=
            Option.some.inj
              ((List.getElem?_eq_getElem (by rw [htotalCount]; exact n.isLt)).symm.trans
                hcurrentRecordGet?)
          have hnTotal : n.val < total.records.length := by
            rw [htotalCount]
            exact n.isLt
          let currentRecord : Record := total.records[n.val]'hnTotal
          have hcurrentRecordEq : currentRecord = Rn := hcurrentRecord
          have hcurrentInputEq :
              currentRecord.input.state = Rn.input.state :=
            congrArg (fun record : Record => record.input.state) hcurrentRecordEq
          have hcurrentInputOrdinary' :
              currentRecord.input.state.followers i =
                .ordinary currentInputState currentInputMemory := by
            rw [hcurrentInputEq]
            exact hcurrentInputOrdinary
          have hbInPrefix : b.val < (total.records.take n.val).length := by
            rw [htakePrefix, hprefixCount]
            exact hbval_lt_n
          have hbirthInPrefix :
              (total.records.take n.val)[b.val]? =
                some (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
                  rate rewards C_star C_h s hs x b) := by
            rw [htakePrefix, List.getElem?_eq_getElem (by rw [hprefixCount]; exact hbval_lt_n)]
            rw [hbirthPrefix]
            exact congrArg some hbirthRecord
          have hbActual :
              (total.records.take n.val)[b.val]'hbInPrefix =
                ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
                  rate rewards C_star C_h s hs x b :=
            Option.some.inj ((List.getElem?_eq_getElem hbInPrefix).symm.trans hbirthInPrefix)
          have hprefixChain :=
            ReferenceFollowerReplyChronology.connected_take_to_input total.connected n.val
              (by rw [htotalCount]; exact n.isLt)
          have hbirthChain :=
            ReferenceFollowerReplyChronology.connected_drop_from_output hprefixChain b.val
              hbInPrefix
          have hbirthChain' :
              ReferenceActivePhysicalHorizon.Connected
                (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
                  rate rewards C_star C_h s hs x b).output.next
                ((total.records.take n.val).drop (b.val + 1))
                currentRecord.input.state := by
            rw [← hbActual, hcurrentRecordEq, ← hcurrentRecord]
            exact hbirthChain
          have hbirthOutputOrdinary :=
            ReferenceFollowerReplyChronology.connected_ordinary_chronology hbirthChain' i
              currentInputState currentInputMemory
              hcurrentInputOrdinary'
          obtain ⟨birthOutputState, birthOutputMemory, hbirthOutputOrdinary, _, _, _⟩ :=
            hbirthOutputOrdinary
          have hbirthChoice :=
            ReferenceFollowerReplyChronology.record_choice_chronology
              (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
                rate rewards C_star C_h s hs x b) i
              birthOutputState birthOutputMemory hbirthOutputOrdinary
          obtain ⟨birthState, birthMemory, hbirthActualChoice, _, _, _⟩ := hbirthChoice
          have hunoccupied :=
            ReferenceGeneratedInstallationFollowerSeed.generated_installation_choice_unoccupied
              rate rewards C_star C_h s hs x i b selected.view.payload hbirthRb
              birthState birthMemory hbirthActualChoice
          have htime : selected.view.payload.sigma.val = s + b.val := by
            have hbirthTime' := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
              (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
                rate rewards C_star C_h s hs x b) selected.view.payload hbirthRb
            have hrecordTime :
                (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
                  rate rewards C_star C_h s hs x b).input.time.val = s + b.val := by
              rw [generated_record_input_eq_nextInput rate rewards C_star C_h s hs x b]
              rfl
            exact hbirthTime'.trans hrecordTime
          refine ⟨b, hbval_lt_n, hbirthRb, htime,
            birthState, birthMemory, hbirthActualChoice, hunoccupied.1, ?_⟩
          rcases hunoccupied.2 with ⟨before, beforeMemory, hbefore, hbeforeStatus,
            hreply, hbank, hbuffer, hfailure, hmemory, _, _, _⟩
          exact ⟨before, beforeMemory, hbefore, hbeforeStatus, hreply, hbank,
            hbuffer, hfailure, hmemory⟩
      | cutoffChosen _ _ _ _ _ _ _ _ _ _ => trivial
      | clockFailure _ _ => trivial
      | initializerFailure _ _ _ _ => trivial
      | localFailure _ _ _ => trivial
  | collection payload ledger clock cutoff outcome => trivial
  | invalidCollectionCutoff => trivial
  | dagger => trivial

end Bandits.Support.ReferenceGeneratedAssignmentLiveErasureHistory

end
