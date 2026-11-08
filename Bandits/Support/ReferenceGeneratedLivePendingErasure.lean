/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedAssignmentLiveSegment

import Lean.Elab.Tactic.Omega

/-!
# Actual generated live pending erasure

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:100-106`,
`sources/zip4/manuscript/05_binary_transport.tex:60-88,94-124`,
`sources/zip4/manuscript/06_interruptions.tex:41-70,270-295,327-348`,
`sources/zip4/manuscript/07_public_setup.tex:129-162`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This internal branch result consumes the admitted generated LIVE segment. It
locates an actual earlier positive DOWN confirmation that first removes the
focal follower from this same assignment's pending set. It does not establish
occupancy, accepted-DOWN chronology, stale-word exclusion, or manuscript
closure.
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

namespace Bandits.Support.ReferenceGeneratedLivePendingErasure

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private abbrev Record := RoundRecord (p := p) (rate := rate)

private theorem selectionAt_fields
    (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (selected : Selection x)
    (hselected : selectionAt x payload started time weights arm = some selected) :
    selected.view.payload = payload ∧
      selected.view.pendingAtChoice = started.pending ∧
      selected.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u ∧
      selected.started = started := by
  unfold selectionAt at hselected
  split at hselected
  · cases hselected
    exact ⟨rfl, rfl, rfl, rfl⟩
  · cases hselected

private theorem dispatchLive_continuing_pending
    (input : CoordinatorRoundDispatch.LiveInput p)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      input.registers input.ownedRegisters input.followerBaseScore)
    (hstart : CoordinatorPhaseClock.startRound p input.eta.val input.registers.time
      input.registers.priorClock input.registers.clockPending = .ok dispatched.startResult)
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation input.registers input.row)
    (selection : CoordinatorRoundDispatch.ArmSelection input.registers.payload
      dispatched.startResult input.registers.time input.registers.complementWeights input.row)
    (heq : CoordinatorRoundDispatch.dispatchLive input =
      .continuingChosen dispatched hstart continuation selection) :
    dispatched.startResult.pending = input.registers.pendingAtChoice := by
  unfold CoordinatorRoundDispatch.dispatchLive at heq
  dsimp only at heq
  split at heq
  · cases heq
  · rename_i actual hactual
    split at heq
    · cases heq
    · cases heq
    · by_cases hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          input.registers actual.startResult
      · rw [dite_eq_left hframe] at heq
        have hp := hframe.2.1.trans
          (CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq input.registers)
        repeat' split at heq
        all_goals first
          | (cases heq; exact hp)
          | cases heq
          | (rename_i hchoice hboundary henvelope hselected
             exact ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
               input.registers.payload actual.startResult.pending
               (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
               input.registers.time input.registers.complementWeights input.row hchoice) hselected).elim)
      · rw [dite_eq_right hframe] at heq
        cases heq
    · repeat' split at heq
      all_goals first
        | cases heq
        | (rename_i hchoice hboundary henvelope hselected
           exact ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
             input.registers.payload actual.startResult.pending
             (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
             input.registers.time input.registers.complementWeights input.row hchoice) hselected).elim)

private theorem livePostChoice_live_success
    (x : RoundInput p rate) (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (baseNext : Fin (p.m - 1) → ℕ)
    (h : (livePostChoice prepared r q base started).configuration = .live next owned baseNext) :
    ∃ recording serviced pending finished,
      CoordinatorRecorderComplementBridge.run (liveRecordingInput prepared r started) =
        some recording ∧
      CoordinatorLiveServiceFinish.servicePass r q recording = .ok serviced ∧
      CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        x.time x.row prepared.coordinatorObservation = some pending ∧
      CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock pending x.row =
        .ok finished ∧
      next.payload = r.payload ∧ next.pendingAtChoice = finished.pending := by
  unfold livePostChoice at h
  split at h
  · cases h
  · rename_i recording hrecord
    split at h
    · cases h
    · rename_i serviced hservice
      split at h
      · cases h
      · rename_i pending hpending
        split at h
        · cases h
        · rename_i finished hfinish
          cases h
          exact ⟨recording, serviced, pending, finished,
            hrecord, hservice, hpending, hfinish, rfl, rfl⟩

private theorem confirmation_erases_absent
    (x : RoundInput p rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (payload : Payload rate) (observation : Fin (D p + 1))
    (pendingAfter : Finset (Fin (p.m - 1))) (finished : CoordinatorPhaseClock.FinishRoundResult p)
    (hupdate : CoordinatorLocalArmChoice.confirmationUpdate payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time x.row observation = some pendingAfter)
    (hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
      pendingAfter x.row = .ok finished)
    (i : Fin (p.m - 1)) (hmem : i ∈ started.pending)
    (habsent : i ∉ finished.pending) :
    CoordinatorLocalArmChoice.downConfirmationEvent payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time (x.row.2 x.time) observation ∧
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (x.row.2 x.time).1 = i ∧
    pendingAfter = started.pending.erase
      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1) := by
  have hcore : CoordinatorLocalArmChoice.confirmationUpdateCore payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time (x.row.2 x.time) observation = some pendingAfter := hupdate
  have hvalid : CoordinatorLocalArmChoice.ConfirmationInputsValid payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time := by
    by_contra hnot
    simp [CoordinatorLocalArmChoice.confirmationUpdateCore, hnot] at hcore
  have hfinishPending := CoordinatorPhaseClock.finishRound_pending_frame p rate.eta.val
    x.time started.clock pendingAfter x.row finished hfinish
  have hnotAfter : i ∉ pendingAfter := by
    simpa only [hfinishPending] using habsent
  by_cases hevent : CoordinatorLocalArmChoice.downConfirmationEvent payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time (x.row.2 x.time) observation
  · have hremove := CoordinatorLocalArmChoice.confirmationUpdateCore_removes payload
      started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time (x.row.2 x.time) observation hvalid hevent
    have hout : pendingAfter = started.pending.erase
        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1) := by
      exact Option.some.inj (hcore.symm.trans hremove)
    have hdraw := Finset.eq_of_mem_of_notMem_erase hmem (by simpa only [hout] using hnotAfter)
    exact ⟨hevent, hdraw.symm, hout⟩
  · have hpreserve := CoordinatorLocalArmChoice.confirmationUpdateCore_preserves payload
      started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time (x.row.2 x.time) observation hvalid hevent
    have hout : pendingAfter = started.pending :=
      Option.some.inj (hcore.symm.trans hpreserve)
    have : i ∈ pendingAfter := by simpa only [hout] using hmem
    exact (hnotAfter this).elim

private theorem output_next_coordinator_eq
    (record : Record (p := p) (rate := rate)) :
    record.output.next.coordinator = record.output.coordinator.configuration := by
  rw [record.output_eq]
  rfl

private theorem record_prepared_eq
    (record : Record (p := p) (rate := rate)) :
    record.output.preparation = prepare record.input := by
  rw [record.output_eq]
  rfl

/- A selected installation or continuing LIVE record uses its original
post-choice operation. These are exactly the two forms used by the segment's
birth and continuing interval.
-/
private theorem record_live_tail_origin
    (record : Record (p := p) (rate := rate)) (selected : Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (hbranch : InstallationBirth record selected.view.payload ∨
      ∃ registers owned base dispatched hstart continuation arm,
        record.output.preparation.coordinator = .live registers owned base
          (.continuingChosen dispatched hstart continuation arm)) :
    ∃ registers registersOwned liveBase started,
      record.output.preparation.observeCoordinator =
        livePostChoice record.output.preparation registers registersOwned liveBase started ∧
      selected.view.payload = registers.payload ∧
      selected.view.pendingAtChoice = started.pending ∧
      selected.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u ∧
      selected.started = started := by
  classical
  rcases hbranch with hbirth | hcontinue
  · cases hcoord : record.output.preparation.coordinator with
    | first outcome =>
        cases outcome with
        | chosen installed arm =>
            have hselAt : selectionAt record.input installed.registers.payload
                installed.startRoundResult installed.registers.time installed.registers.complementWeights
                arm = some selected := by
              simpa only [hcoord, DispatchCut.selection] using hselected
            have hfields := selectionAt_fields record.input installed.registers.payload
              installed.startRoundResult installed.registers.time installed.registers.complementWeights
              arm selected hselAt
            have heq := observeCoordinator_first_equation record.output.preparation
              (.chosen installed arm) hcoord
            have hsel : (DispatchCut.first (.chosen installed arm)).selection = some selected := by
              simpa only [hcoord] using hselected
            have hnon : (DispatchCut.first (.chosen installed arm)).selection ≠ none := by
              rw [hsel]
              exact Option.some_ne_none _
            have hobs : record.output.preparation.observeCoordinator =
                livePostChoice record.output.preparation installed.registers installed.ownedRegisters
                  installed.followerBaseScore installed.startRoundResult := by
              rw [heq, ite_eq_right hnon]
            exact ⟨installed.registers, installed.ownedRegisters, installed.followerBaseScore,
              installed.startRoundResult, hobs, hfields.1, hfields.2.1, hfields.2.2.1,
              hfields.2.2.2⟩
        | choiceDomainFailure _ => simp only [InstallationBirth, hcoord] at hbirth
        | recorderBoundaryFailure _ => simp only [InstallationBirth, hcoord] at hbirth
        | choiceRejected _ => simp only [InstallationBirth, hcoord] at hbirth
    | collection payload ledger clock cutoff outcome =>
        cases outcome with
        | laterChosen core consistent started hstart instruction hinstruction output
            hlocal clockData installed arm =>
              have hselAt : selectionAt record.input installed.registers.payload
                  started instruction.time installed.registers.complementWeights arm =
                    some selected := by
                simpa only [hcoord, DispatchCut.selection] using hselected
              have hfields := selectionAt_fields record.input installed.registers.payload
                started instruction.time installed.registers.complementWeights arm selected hselAt
              have heq := observeCoordinator_collection_equation record.output.preparation
                payload ledger clock cutoff (.laterChosen core consistent started hstart
                  instruction hinstruction output hlocal clockData installed arm) hcoord
              have hsel : (DispatchCut.collection payload ledger clock cutoff
                  (.laterChosen core consistent started hstart instruction hinstruction
                    output hlocal clockData installed arm)).selection = some selected := by
                simpa only [hcoord] using hselected
              have hnon : (DispatchCut.collection payload ledger clock cutoff
                  (.laterChosen core consistent started hstart instruction hinstruction
                    output hlocal clockData installed arm)).selection ≠ none := by
                rw [hsel]
                exact Option.some_ne_none _
              have hobs : record.output.preparation.observeCoordinator =
                  livePostChoice record.output.preparation installed.registers
                    installed.ownedRegisters installed.retainedBaseScore started := by
                rw [heq, ite_eq_right hnon]
              exact ⟨installed.registers, installed.ownedRegisters,
                installed.retainedBaseScore, started, hobs, hfields.1, hfields.2.1,
                hfields.2.2.1, hfields.2.2.2⟩
        | continuing _ _ _ _ => simp only [InstallationBirth, hcoord] at hbirth
        | clockFailure _ _ => simp only [InstallationBirth, hcoord] at hbirth
        | localFailure _ _ _ _ => simp only [InstallationBirth, hcoord] at hbirth
        | coreFailure _ _ _ _ => simp only [InstallationBirth, hcoord] at hbirth
        | laterReconstructionFailure _ _ _ _ _ _ _ _ =>
            simp only [InstallationBirth, hcoord] at hbirth
        | laterPrefixFailure _ _ _ _ _ _ _ _ _ =>
            simp only [InstallationBirth, hcoord] at hbirth
        | laterOrientationFailure _ _ _ _ _ _ _ _ =>
            simp only [InstallationBirth, hcoord] at hbirth
        | laterChoiceFailure _ _ _ _ _ _ _ _ _ _ _ =>
            simp only [InstallationBirth, hcoord] at hbirth
    | live _ _ _ _ => simp only [InstallationBirth, hcoord] at hbirth
    | invalidCollectionCutoff => simp only [InstallationBirth, hcoord] at hbirth
    | dagger => simp only [InstallationBirth, hcoord] at hbirth
  · rcases hcontinue with ⟨registers, registersOwned, liveBase, dispatched, hstart,
      continuation, arm, hcoord⟩
    have hselAt : selectionAt record.input registers.payload dispatched.startResult
        record.input.time (liveRegistersAt registers record.input.time).complementWeights
        arm = some selected := by
      simpa only [hcoord, DispatchCut.selection] using hselected
    have hfields := selectionAt_fields record.input registers.payload dispatched.startResult
      record.input.time (liveRegistersAt registers record.input.time).complementWeights arm
      selected hselAt
    have heq := observeCoordinator_live_equation record.output.preparation registers
      registersOwned liveBase (.continuingChosen dispatched hstart continuation arm) hcoord
    have hsel : (DispatchCut.live registers registersOwned liveBase
        (.continuingChosen dispatched hstart continuation arm)).selection = some selected := by
      simpa only [hcoord] using hselected
    have hnon : (DispatchCut.live registers registersOwned liveBase
        (.continuingChosen dispatched hstart continuation arm)).selection ≠ none := by
      rw [hsel]
      exact Option.some_ne_none _
    have hobs : record.output.preparation.observeCoordinator =
        livePostChoice record.output.preparation (liveRegistersAt registers record.input.time)
          (liveOwnedAt registers registersOwned record.input.time) liveBase dispatched.startResult := by
      rw [heq, ite_eq_right hnon]
    refine ⟨liveRegistersAt registers record.input.time,
      liveOwnedAt registers registersOwned record.input.time, liveBase,
      dispatched.startResult, hobs, ?_, hfields.2.1, hfields.2.2.1, hfields.2.2.2⟩
    exact hfields.1

/-- The first index whose actual selected CHOICE omits `i` has an immediately
preceding original index whose successful LIVE post-choice tail erased `i`.
-/
theorem generated_live_missing_pending_confirmation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (n : Fin (p.T - s)) (i : Fin (p.m - 1)) :
    let R := generatedSourceRecordAt rate rewards C_star C_h s hs x
    match (R n).output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen _ _ _ _) =>
        ∀ v : Selection (R n).input,
          (R n).output.preparation.coordinator.selection = some v →
        ∀ state memory,
          (ReferenceFollowerFixedReply.actualChoice (R n) i).configuration =
            .ordinary state memory →
        i ∉ v.view.pendingAtChoice →
        ∃ b : Fin (p.T - s),
          b.val < n.val ∧
          InstallationBirth (R b) v.view.payload ∧
          ∃ k : Fin (p.T - s),
            b.val ≤ k.val ∧ k.val < n.val ∧
            s + b.val ≤ s + k.val ∧ s + k.val < s + n.val ∧ s + n.val < p.T ∧
            (R k).input.time.val = s + k.val ∧
            ∃ w : Selection (R k).input,
              (R k).output.preparation.coordinator.selection = some w ∧
              ∃ stateK memoryK,
                (ReferenceFollowerFixedReply.actualChoice (R k) i).configuration =
                  .ordinary stateK memoryK ∧
                w.view.payload = v.view.payload ∧
                PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  ((R k).input.row.2 (R k).input.time).1 = i ∧
                CoordinatorLocalArmChoice.downConfirmationEvent w.view.payload
                  w.view.pendingAtChoice w.view.cutoff (R k).input.time
                  ((R k).input.row.2 (R k).input.time)
                  (R k).output.preparation.coordinatorObservation ∧
                ∃ next owned base,
                  (R k).output.next.coordinator = .live next owned base ∧
                  next.pendingAtChoice = w.view.pendingAtChoice.erase i ∧
                  next.payload = v.view.payload
    | _ => True := by
  classical
  dsimp only
  let R := generatedSourceRecordAt rate rewards C_star C_h s hs x
  cases hcoord : (R n).output.preparation.coordinator with
  | first _ => trivial
  | live endpoint endpointOwned endpointBase outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation arm =>
          intro v hv state memory hchoice hmissing
          have hsegment := ReferenceGeneratedAssignmentLiveSegment.generated_live_actual_payload_segment
            rate rewards C_star C_h s hs x n i
          dsimp only at hsegment
          rw [hcoord] at hsegment
          obtain ⟨b, hbn, hbirth, hdate, hdownDate, hinitializer, hbirthSelection,
            hbirthLive, hconnected, hinterval, hsuccess, htimeChoice⟩ :=
            hsegment v hv state memory hchoice
          rcases hbirthSelection with ⟨birthSelected, hbirthSelected, hbirthPayload,
            hbirthPending, hbirthStartedPending⟩
          have hselectExists : ∀ (j : Fin (p.T - s)) (hj : b.val < j.val)
              (hjn : j.val ≤ n.val),
              ∃ w : Selection (R j).input,
                (R j).output.preparation.coordinator.selection = some w ∧
                w.view.payload = v.view.payload := by
            intro j hj hjn
            rcases hinterval j hj hjn with
              ⟨r, q, base, outcome, _, _, _, hpayload, hselected, _, _⟩
            rcases hselected with ⟨w, hw, hwp⟩
            exact ⟨w, hw, hwp⟩
          let selectedPending : Fin (p.T - s) → Option (Finset (ActiveRoundActions.Follower p.m)) :=
            fun j => ((R j).output.preparation.coordinator.selection).map
              fun selected => selected.view.pendingAtChoice
          have hvActual : (R n).output.preparation.coordinator.selection = some v := by
            rw [hcoord]
            exact hv
          have hmapN : selectedPending n = some v.view.pendingAtChoice := by
            dsimp [selectedPending]
            rw [hvActual]
            rfl
          have hnIndex : (⟨n.val, by omega⟩ : Fin (p.T - s)) = n := Fin.ext rfl
          let bad : ℕ → Prop := fun j =>
            ∃ hjb : b.val ≤ j, ∃ hjn : j ≤ n.val,
              ∃ pending : Finset (ActiveRoundActions.Follower p.m),
                selectedPending (⟨j, by omega⟩ : Fin (p.T - s)) = some pending ∧ i ∉ pending
          have hbad : ∃ j, bad j := by
            refine ⟨n.val, ?_, Nat.le_refl _, v.view.pendingAtChoice, ?_, hmissing⟩
            · omega
            simpa only [selectedPending, hnIndex] using hmapN
          let j := Nat.find hbad
          have hjbad := Nat.find_spec hbad
          have hjb : b.val < j := by
            rcases hjbad with ⟨hjb, hjn, pendingJ, hmapJ, hiJ⟩
            by_contra hnot
            have heq : j = b.val := by omega
            have hjBound : j < p.T - s := by omega
            have heqIndex : (⟨j, hjBound⟩ : Fin (p.T - s)) = b := Fin.ext heq
            have hfindIndex : (⟨Nat.find hbad, hjBound⟩ : Fin (p.T - s)) =
                (⟨j, hjBound⟩ : Fin (p.T - s)) := by
              apply Fin.ext
              rfl
            have hmapAtJ : selectedPending (⟨j, hjBound⟩ : Fin (p.T - s)) = some pendingJ := by
              simpa only [hfindIndex] using hmapJ
            have hmapAtB : selectedPending b = some pendingJ := by
              simpa only [heqIndex] using hmapAtJ
            have hbirthMap : selectedPending b = some birthSelected.view.pendingAtChoice := by
              dsimp [selectedPending]
              rw [hbirthSelected]
              rfl
            have hpendingEq : pendingJ = Finset.univ := by
              exact (Option.some.inj (hmapAtB.symm.trans hbirthMap)).trans hbirthPending
            have hiMem : i ∈ pendingJ := by
              rw [hpendingEq]
              exact Finset.mem_univ i
            exact hiJ hiMem
          rcases hjbad with ⟨hjb', hjn', pendingJ, hmapJ, hnotJ⟩
          have hjle : j ≤ n.val := hjn'
          have hjIndex : j < p.T - s := by omega
          let jFin : Fin (p.T - s) := ⟨j, hjIndex⟩
          have hfindToJ : (⟨Nat.find hbad, by omega⟩ : Fin (p.T - s)) = jFin := by
            apply Fin.ext
            rfl
          have hmapJFin : selectedPending jFin = some pendingJ := by
            simpa only [hfindToJ] using hmapJ
          obtain ⟨wJ, hwJ, hwpayloadJ⟩ := hselectExists jFin (by simpa [jFin] using hjb)
            (by simpa only [jFin] using hjle)
          have hmapSelectedJ : selectedPending jFin = some wJ.view.pendingAtChoice := by
            dsimp [selectedPending]
            rw [hwJ]
            rfl
          have hpendingJ : wJ.view.pendingAtChoice = pendingJ :=
            Option.some.inj (hmapSelectedJ.symm.trans hmapJFin)
          have hnotJ' : i ∉ wJ.view.pendingAtChoice := by
            simpa only [hpendingJ] using hnotJ
          have hprevMinimal : ¬ bad (j - 1) := by
            exact Nat.find_min hbad (by omega)
          have hklo : b.val ≤ j - 1 := by omega
          have hkhi : j - 1 ≤ n.val := by omega
          have hklt : j - 1 < n.val := by omega
          let k : Fin (p.T - s) := ⟨j - 1, by omega⟩
          have hKIndex : (⟨j - 1, by omega⟩ : Fin (p.T - s)) = k := by
            apply Fin.ext
            rfl
          have hkIndex : k.val + 1 = j := by dsimp [k]; omega
          have hselectedK : ∃ w : Selection (R k).input,
              (R k).output.preparation.coordinator.selection = some w ∧
              w.view.payload = v.view.payload := by
            by_cases hkb : k.val = b.val
            · have hkEq : k = b := Fin.ext hkb
              rw [hkEq]
              exact ⟨birthSelected, hbirthSelected, hbirthPayload⟩
            · have hgt : b.val < k.val := by omega
              exact hselectExists k hgt (Nat.le_of_lt hklt)
          rcases hselectedK with ⟨w, hw, hwpayload⟩
          have hmemK : i ∈ w.view.pendingAtChoice := by
            by_contra hnot
            apply hprevMinimal
            refine ⟨hklo, hkhi, w.view.pendingAtChoice, ?_, hnot⟩
            have hmapW : selectedPending k = some w.view.pendingAtChoice := by
              dsimp [selectedPending]
              rw [hw]
              rfl
            simpa only [selectedPending, hKIndex] using hmapW
          have hordinaryK : ∃ stateK memoryK,
              (ReferenceFollowerFixedReply.actualChoice (R k) i).configuration =
                .ordinary stateK memoryK := by
            rcases htimeChoice k hklo hkhi with ⟨_, _, hchoices⟩
            rcases hchoices with ⟨stateK, memoryK, hchoiceK⟩
            exact ⟨stateK, memoryK, hchoiceK⟩
          obtain ⟨stateK, memoryK, hchoiceK⟩ := hordinaryK
          have hinputTime : (R k).input.time.val = s + k.val :=
            (htimeChoice k hklo hkhi).1
          rcases hsuccess k (by omega) hklt with
            ⟨next, nextOwned, nextBase, hnext, hnextPayload⟩
          have hnextInput : (R jFin).input.state = (R k).output.next := by
            let total := generatedSourceRun rate rewards C_star C_h s hs x
            have hcount : total.records.length = p.T - s := by
              exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
            have htotalK : k.val < total.records.length := by rw [hcount]; exact k.isLt
            have htotalJ : jFin.val < total.records.length := by rw [hcount]; exact jFin.isLt
            have hchain := ReferenceFollowerReplyChronology.connected_drop_from_output
              total.connected k.val htotalK
            rw [hkIndex, List.drop_eq_getElem_cons htotalJ] at hchain
            change _ ∧ _ at hchain
            have hstate := hchain.1
            have hgetK : total.records[k.val] = R k := by
              have hget := generatedSourceRecordAt_getElem? rate rewards C_star C_h s hs x k
              rw [List.getElem?_eq_getElem htotalK] at hget
              exact Option.some.inj hget
            have hgetJ : total.records[jFin.val] = R jFin := by
              have hget := generatedSourceRecordAt_getElem? rate rewards C_star C_h s hs x jFin
              rw [List.getElem?_eq_getElem htotalJ] at hget
              exact Option.some.inj hget
            rw [hgetK, hgetJ] at hstate
            exact hstate
          have hphaseJ : ∃ r q base, ∃ outcome : CoordinatorRoundDispatch.LiveOutcome
              (liveInput (R jFin).input r q base),
              (R jFin).input.state.coordinator = .live r q base ∧
              (R jFin).output.preparation.coordinator = .live r q base outcome ∧
              (∃ dispatched hstart continuation arm,
                outcome = .continuingChosen dispatched hstart continuation arm) ∧
              r.payload = v.view.payload ∧
              ∃ current : Selection (R jFin).input,
                (R jFin).output.preparation.coordinator.selection = some current ∧
                current.view.payload = v.view.payload := by
            have hjgt : b.val < jFin.val := by simpa [jFin] using hjb
            rcases hinterval jFin hjgt (by simpa only [jFin] using hjle) with
              ⟨r, q, base, outcome, hinput, hcut, hcontinue, hpayload, hselected, _, _⟩
            exact ⟨r, q, base, outcome, hinput, hcut, hcontinue, hpayload, hselected⟩
          rcases hphaseJ with ⟨rJ, qJ, baseJ, outcomeJ, hinputJ, hcutJ, hcontinueJ,
            hpayloadJ, currentJ, hcurrentJ, hcurrentPayloadJ⟩
          have hcurrentEq : currentJ = wJ := Option.some.inj (hcurrentJ.symm.trans hwJ)
          have hnotCurrent : i ∉ currentJ.view.pendingAtChoice := by
            simpa only [hcurrentEq] using hnotJ'
          have hsameState : (R jFin).input.state.coordinator =
              (R k).output.next.coordinator := by
            have hcoordinator := congrArg
              (fun st : ReferenceActivePhysicalStep.State p rate => st.coordinator) hnextInput
            exact hcoordinator
          have hliveEq : CoordinatorConfiguration.live rJ qJ baseJ =
              CoordinatorConfiguration.live next nextOwned nextBase := by
            calc
              CoordinatorConfiguration.live rJ qJ baseJ = (R jFin).input.state.coordinator := hinputJ.symm
              _ = (R k).output.next.coordinator := hsameState
              _ = CoordinatorConfiguration.live next nextOwned nextBase := hnext
          have hnextReg : next = rJ := by
            cases hliveEq
            rfl
          have hstartPending : currentJ.view.pendingAtChoice = rJ.pendingAtChoice := by
            rcases hcontinueJ with ⟨dispatchedJ, hstartJ, continuationJ, armJ, houtcomeJ⟩
            have hcoordJ : (R jFin).output.preparation.coordinator =
                .live rJ qJ baseJ (.continuingChosen dispatchedJ hstartJ continuationJ armJ) := by
              rw [hcutJ, houtcomeJ]
            have hfieldsJ := selectionAt_fields (R jFin).input rJ.payload
              dispatchedJ.startResult (R jFin).input.time
              (liveRegistersAt rJ (R jFin).input.time).complementWeights armJ currentJ
              (by simpa only [hcoordJ, DispatchCut.selection] using hcurrentJ)
            have hdispatchJ : CoordinatorRoundDispatch.dispatchLive
                (liveInput (R jFin).input rJ qJ baseJ) =
                .continuingChosen dispatchedJ hstartJ continuationJ armJ := by
              have hprep := record_prepared_eq (R jFin)
              have hprepCoord : (prepare (R jFin).input).coordinator =
                  .live rJ qJ baseJ (.continuingChosen dispatchedJ hstartJ continuationJ armJ) := by
                calc
                  (prepare (R jFin).input).coordinator =
                      (R jFin).output.preparation.coordinator := congrArg PreparedRound.coordinator hprep |>.symm
                  _ = .live rJ qJ baseJ (.continuingChosen dispatchedJ hstartJ continuationJ armJ) := hcoordJ
              have hdispatchEq : dispatch (R jFin).input =
                  .live rJ qJ baseJ (.continuingChosen dispatchedJ hstartJ continuationJ armJ) :=
                (prepare (R jFin).input).coordinator_eq.symm.trans hprepCoord
              have hdispatchBase : dispatch (R jFin).input =
                  .live rJ qJ baseJ
                    (CoordinatorRoundDispatch.dispatchLive (liveInput (R jFin).input rJ qJ baseJ)) := by
                simp only [dispatch, hinputJ, CoordinatorRoundDispatch.dispatch]
                rfl
              rw [hdispatchBase] at hdispatchEq
              injection hdispatchEq with _ _ _ hOutcome
            have hpendingJ := dispatchLive_continuing_pending
              (liveInput (R jFin).input rJ qJ baseJ) dispatchedJ hstartJ continuationJ armJ
              hdispatchJ
            have hpendingJ' : dispatchedJ.startResult.pending = rJ.pendingAtChoice := by
              simpa [liveInput, liveRegistersAt] using hpendingJ
            exact hfieldsJ.2.1.trans hpendingJ'
          have hnextAbsent : i ∉ rJ.pendingAtChoice := by
            simpa only [hstartPending] using hnotCurrent
          have hbranchK : InstallationBirth (R k) w.view.payload ∨
              ∃ r q base dispatched hstart continuation arm,
                (R k).output.preparation.coordinator = .live r q base
                  (.continuingChosen dispatched hstart continuation arm) := by
            by_cases hkb : k.val = b.val
            · have hkEq : k = b := Fin.ext hkb
              have hbirthW : InstallationBirth (R b) w.view.payload := by
                rw [hwpayload]
                exact hbirth
              exact Or.inl (by simpa only [hkEq] using hbirthW)
            · have hgt : b.val < k.val := by omega
              obtain ⟨r, q, base, outcome, _, hcut, hcontinue, _, _, _, _⟩ :=
                hinterval k hgt (Nat.le_of_lt hklt)
              rcases hcontinue with ⟨dispatched, hstart, continuation, arm, houtcome⟩
              have hcut' := hcut
              rw [houtcome] at hcut'
              exact Or.inr ⟨r, q, base, dispatched, hstart, continuation, arm, hcut'⟩
          rcases record_live_tail_origin (R k) w hw hbranchK with
            ⟨registers, registersOwned, liveBase, started, hobs, hwpayload', hwpending,
              hwcutoff, hwstarted⟩
          have hconfigurationEq : CoordinatorConfiguration.live rJ qJ baseJ =
              CoordinatorConfiguration.live next nextOwned nextBase := by
            calc
              CoordinatorConfiguration.live rJ qJ baseJ = (R jFin).input.state.coordinator := hinputJ.symm
              _ = (R k).output.next.coordinator := hsameState
              _ = CoordinatorConfiguration.live next nextOwned nextBase := hnext
          have htail : (livePostChoice (R k).output.preparation registers registersOwned
              liveBase started).configuration = .live rJ qJ baseJ := by
            have hnextObs : (R k).output.next.coordinator =
                (livePostChoice (R k).output.preparation registers registersOwned
                  liveBase started).configuration := by
              calc
                (R k).output.next.coordinator = (R k).output.coordinator.configuration :=
                  output_next_coordinator_eq (R k)
                _ = (livePostChoice (R k).output.preparation registers registersOwned
                    liveBase started).configuration :=
                  congrArg (fun o : CoordinatorObservation p rate => o.configuration) hobs
            calc
              (livePostChoice (R k).output.preparation registers registersOwned
                  liveBase started).configuration = (R k).output.next.coordinator := hnextObs.symm
              _ = .live next nextOwned nextBase := hnext
              _ = .live rJ qJ baseJ := hconfigurationEq.symm
          have hliveEqual : CoordinatorConfiguration.live rJ qJ baseJ =
              CoordinatorConfiguration.live next nextOwned nextBase := by
            exact hconfigurationEq
          have htailK : (livePostChoice (R k).output.preparation registers registersOwned
              liveBase started).configuration = .live next nextOwned nextBase :=
            htail.trans hliveEqual
          have hnextReg : next = rJ := by
            have hliveEq : CoordinatorConfiguration.live rJ qJ baseJ =
                CoordinatorConfiguration.live next nextOwned nextBase := by
              calc
                CoordinatorConfiguration.live rJ qJ baseJ = (R jFin).input.state.coordinator := hinputJ.symm
                _ = (R k).output.next.coordinator := hsameState
                _ = CoordinatorConfiguration.live next nextOwned nextBase := hnext
            cases hliveEq
            rfl
          obtain ⟨recording, serviced, pendingAfter, finished,
            hrecording, hservice, hupdate, hfinish, hpayloadNext, hfinishedPending⟩ :=
            livePostChoice_live_success (R k).input (R k).output.preparation
              registers registersOwned liveBase started next nextOwned nextBase htailK
          have hfinishedAbsent : i ∉ finished.pending := by
            have hnextAbsent' : i ∉ next.pendingAtChoice := by
              simpa only [hnextReg] using hnextAbsent
            rw [← hfinishedPending]
            exact hnextAbsent'
          have hmemStarted : i ∈ started.pending := by
            rw [← hwpending]
            exact hmemK
          have herased := confirmation_erases_absent (R k).input started registers.payload
            ((R k).output.preparation.coordinatorObservation) pendingAfter finished
            hupdate hfinish i hmemStarted hfinishedAbsent
          rcases herased with ⟨hevent, hdraw, hpendingAfter⟩
          have heventView : CoordinatorLocalArmChoice.downConfirmationEvent w.view.payload
              w.view.pendingAtChoice w.view.cutoff (R k).input.time
              ((R k).input.row.2 (R k).input.time)
              (R k).output.preparation.coordinatorObservation := by
            rw [hwpayload', hwpending, hwcutoff]
            exact hevent
          have hfinishFrame : finished.pending = pendingAfter :=
            CoordinatorPhaseClock.finishRound_pending_frame p rate.eta.val
              (R k).input.time started.clock pendingAfter (R k).input.row finished hfinish
          have hpendingAfterNext : next.pendingAtChoice = pendingAfter :=
            hfinishedPending.trans hfinishFrame
          have heraseEq : pendingAfter = w.view.pendingAtChoice.erase i := by
            rw [hpendingAfter, ← hwpending, hdraw]
            rfl
          have hpendingErase : next.pendingAtChoice = w.view.pendingAtChoice.erase i :=
            hpendingAfterNext.trans heraseEq
          have hpayloadFinal : next.payload = v.view.payload :=
            hpayloadNext.trans hwpayload'.symm |>.trans hwpayload
          refine ⟨b, hbn, hbirth, k, ?_, hklt, ?_, ?_, ?_, ?_, w, hw, stateK, memoryK,
            hchoiceK, hwpayload, hdraw, heventView, next, nextOwned, nextBase,
            hnext, hpendingErase, hpayloadFinal⟩
          · exact hklo
          · omega
          · omega
          · omega
          · exact hinputTime
      | cutoffChosen _ _ _ _ _ _ _ _ _ _ => trivial
      | clockFailure _ _ => trivial
      | initializerFailure _ _ _ _ => trivial
      | localFailure _ _ _ => trivial
  | collection _ _ _ _ _ => trivial
  | invalidCollectionCutoff => trivial
  | dagger => trivial

end Bandits.Support.ReferenceGeneratedLivePendingErasure

end
