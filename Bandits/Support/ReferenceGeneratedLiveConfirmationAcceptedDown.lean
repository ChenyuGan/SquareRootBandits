/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedLivePendingErasure

import Lean.Elab.Tactic.Omega

/-!
# Actual live confirmation has a prior accepted DOWN record

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109`,
`sources/zip4/manuscript/05_binary_transport.tex:60-88,94-124`, and
`sources/zip4/manuscript/06_interruptions.tex:270-295,327-348`.

The result consumes the accepted actual-run pending-erasure producer. It
propagates only the focal follower's occupied DOWN field from that producer's
actual installation birth to its actual confirmation record, then invokes the
public original-run accepted-record origin theorem. The theorem retains the
actual selected confirmation record and its physical event. This is an internal
branch result, not a manuscript closure claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceGeneratedDownBatchCalendar
open ReferenceGeneratedInheritedDownWrongCompletionWitness

namespace Bandits.Support.ReferenceGeneratedLiveConfirmationAcceptedDown

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem focal_step_occupied_fields
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected)
    (i : Fin (p.m - 1))
    (hfields : ReferenceActiveDataOwnership.occupiedFields selected.view.payload i
      (x.state.followers i)) :
    ReferenceActiveDataOwnership.occupiedFields selected.view.payload i
      ((ReferenceActivePhysicalStep.step x).next.followers i) := by
  have hview : (ReferenceActivePhysicalStep.prepare x).coordinator.downView =
      some selected.view := by
    simp only [ReferenceActivePhysicalStep.DispatchCut.downView, hselected, Option.map_some]
  have halignment := (ReferenceActivePhysicalStep.prepare x).follower_alignment i
  have hprepared : ReferenceActiveDataOwnership.occupiedFields selected.view.payload
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).follower
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration := by
    rw [halignment.2.1]
    exact ReferenceActiveDataOwnership.choice_occupied_fields_preserved selected.view.payload i
      x.row (x.state.activations i) x.time (x.active i) (x.state.followers i) hfields
  have hfinished := ReferenceActiveDataOwnership.finishFollower_occupied_fields selected.view
    ((ReferenceActivePhysicalStep.prepare x).followers.followers i)
    ((ReferenceActivePhysicalStep.prepare x).feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) hprepared
  rw [halignment.2.1] at hfinished
  rw [(ReferenceActivePhysicalStep.step_next_fields x).2.2.2 i]
  unfold ReferenceActivePhysicalStep.PreparedRound.observeFollower
  rw [hview]
  exact hfinished

private theorem generated_record_next_input
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (k j : Fin (p.T - s)) (hkj : j.val = k.val + 1) :
    (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x j).input.state =
    (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x k).output.next := by
  let total := ReferenceGeneratedDownBatchCalendar.generatedSourceRun
    rate rewards C_star C_h s hs x
  have hcount : total.records.length = p.T - s := by
    exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have htotalK : k.val < total.records.length := by
    rw [hcount]
    exact k.isLt
  have htotalJ : j.val < total.records.length := by
    rw [hcount]
    exact j.isLt
  have hchain := ReferenceFollowerReplyChronology.connected_drop_from_output
    total.connected k.val htotalK
  rw [hkj.symm, List.drop_eq_getElem_cons htotalJ] at hchain
  change _ ∧ _ at hchain
  have hstate := hchain.1
  have hgetK : total.records[k.val] =
      ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x k := by
    have hget := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
      rate rewards C_star C_h s hs x k
    rw [List.getElem?_eq_getElem htotalK] at hget
    exact Option.some.inj hget
  have hgetJ : total.records[j.val] =
      ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x j := by
    have hget := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
      rate rewards C_star C_h s hs x j
    rw [List.getElem?_eq_getElem htotalJ] at hget
    exact Option.some.inj hget
  rw [hgetK, hgetJ] at hstate
  exact hstate

private theorem generated_interval_input_occupied_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (P : ReferenceActivePhysicalStep.Payload rate)
    (b n : Fin (p.T - s)) (hbn : b.val < n.val)
    (hbirth : ReferenceActiveDataOwnership.occupiedFields P i
      ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x b).output.next.followers i))
    (hselected : ∀ j : Fin (p.T - s), b.val < j.val → j.val < n.val →
      ∃ selected : ReferenceActivePhysicalStep.Selection
          (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
            rate rewards C_star C_h s hs x j).input,
        (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x j).output.preparation.coordinator.selection =
            some selected ∧ selected.view.payload = P) :
    ReferenceActiveDataOwnership.occupiedFields P i
      ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n).input.state.followers i) := by
  let R := fun j : Fin (p.T - s) =>
    ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x j
  have hfieldsAt : ∀ t : ℕ, b.val < t → t ≤ n.val →
      ∃ j : Fin (p.T - s), j.val = t ∧
        ReferenceActiveDataOwnership.occupiedFields P i ((R j).input.state.followers i) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro hbt htn
        let current : Fin (p.T - s) := ⟨t, by omega⟩
        by_cases hfirst : t = b.val + 1
        · have hnext := generated_record_next_input rate rewards C_star C_h s hs x b current
            (by
              simp only [current]
              omega)
          refine ⟨current, rfl, ?_⟩
          rw [hnext]
          exact hbirth
        · let prev : Fin (p.T - s) := ⟨t - 1, by omega⟩
          have hprevBounds : b.val < t - 1 ∧ t - 1 ≤ n.val := by omega
          obtain ⟨prev', hprevVal, hprevFields⟩ :=
            ih (t - 1) (by omega) hprevBounds.1 hprevBounds.2
          have hprevEq : prev' = prev := Fin.ext (by omega)
          subst prev'
          obtain ⟨selected, hsel, hpayload⟩ := hselected prev (by omega) (by omega)
          have hprevSelectedFields : ReferenceActiveDataOwnership.occupiedFields
              selected.view.payload i ((R prev).input.state.followers i) := by
            simpa only [hpayload] using hprevFields
          have hstep := focal_step_occupied_fields (R prev).input selected hsel i
            hprevSelectedFields
          have hstepOutput : ReferenceActiveDataOwnership.occupiedFields P i
              ((R prev).output.next.followers i) := by
            rw [(R prev).output_eq]
            simpa only [hpayload] using hstep
          have hnext := generated_record_next_input rate rewards C_star C_h s hs x prev current
            (by
              simp only [current, prev]
              omega)
          refine ⟨current, rfl, ?_⟩
          rw [hnext]
          exact hstepOutput
  obtain ⟨last, hlast, hfields⟩ := hfieldsAt n.val hbn (Nat.le_refl _)
  have hlastEq : last = n := Fin.ext hlast
  subst last
  exact hfields

private theorem generated_seed_initial_followers
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs) :
    ReferenceFirstLiveConfirmationHistory.InitialFollowers
      (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
        rate rewards C_star C_h s hs x) := by
  have hseed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
    rate rewards C_star C_h s hs x
  obtain ⟨active, hlaunch, hfields⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
      rate x.1 rewards C_star C_h x.2.1
  have hseedEq : ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
      rate rewards C_star C_h s hs x = active :=
    Option.some.inj (hseed.1.symm.trans hlaunch)
  intro i state memory hconfiguration
  have hconfiguration' : active.followers i = .ordinary state memory := by
    rw [← hseedEq]
    exact hconfiguration
  rcases hfields i with ⟨hactive, hlastDown, _, _, _, _, hunoccupied, _⟩
  rw [hactive] at hconfiguration'
  cases hconfiguration'
  exact ⟨hunoccupied, hlastDown⟩

/-- On the selected live CHOICE branch, an absent pending follower's actual
same-payload DOWN confirmation is later than an exact accepted DOWN diagnostic
for that payload. The confirmation selection, focal ordinary CHOICE, draw, and
event are retained on their original actual record.
-/
theorem generated_live_missing_pending_prior_accepted_down
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (n : Fin (p.T - s)) (i : Fin (p.m - 1)) :
    let R := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x
    match (R n).output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen _ _ _ _) =>
        ∀ v : ReferenceActivePhysicalStep.Selection (R n).input,
          (R n).output.preparation.coordinator.selection = some v →
        ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFollowerFixedReply.actualChoice (R n) i).configuration =
            .ordinary state memory →
        i ∉ v.view.pendingAtChoice →
        ∃ a : Fin (p.T - s),
          a.val < n.val ∧
          ReferenceFirstLiveConfirmationHistory.AcceptedDown (R a) i
            (v.view.payload.downRecord i) ∧
          ∃ k : Fin (p.T - s),
            a.val < k.val ∧ k.val < n.val ∧
            ∃ w : ReferenceActivePhysicalStep.Selection (R k).input,
              (R k).output.preparation.coordinator.selection = some w ∧
              w.view.payload = v.view.payload ∧
              PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                ((R k).input.row.2 (R k).input.time).1 = i ∧
              ∃ stateK memoryK,
                (ReferenceFollowerFixedReply.actualChoice (R k) i).configuration =
                  .ordinary stateK memoryK ∧
                CoordinatorLocalArmChoice.downConfirmationEvent w.view.payload
                  w.view.pendingAtChoice w.view.cutoff (R k).input.time
                  ((R k).input.row.2 (R k).input.time)
                  (R k).output.preparation.coordinatorObservation
    | _ => True := by
  classical
  dsimp only
  let R := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
    rate rewards C_star C_h s hs x
  cases hcoordinator : (R n).output.preparation.coordinator with
  | first _ => trivial
  | live endpoint endpointOwned endpointBase outcome =>
      cases outcome with
      | continuingChosen _ _ _ _ =>
          intro v hv state memory hchoice hmissing
          have hroot := ReferenceGeneratedLivePendingErasure.generated_live_missing_pending_confirmation
            rate rewards C_star C_h s hs x n i
          dsimp only at hroot
          rw [hcoordinator] at hroot
          obtain ⟨bRoot, _, hbirthRoot, k, hbk, hkn, _, _, _, _,
            w, hw, stateK, memoryK, hchoiceK, hwpayload, hdraw, hevent, _, _, _⟩ :=
            hroot v hv state memory hchoice hmissing
          have hsegment := ReferenceGeneratedAssignmentLiveSegment.generated_live_actual_payload_segment
            rate rewards C_star C_h s hs x n i
          dsimp only at hsegment
          rw [hcoordinator] at hsegment
          obtain ⟨b, _, _, hdate, _, hinitializer, hbirthSelection,
            _, _, hinterval, _, _⟩ := hsegment v hv state memory hchoice
          have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
            (R bRoot) v.view.payload hbirthRoot
          have hrecordTime : (R bRoot).input.time.val = s + bRoot.val := rfl
          have hrootDate : v.view.payload.sigma.val = s + bRoot.val :=
            hbirthTime.trans hrecordTime
          have hrootBirthEq : bRoot = b := Fin.ext (by omega)
          subst bRoot
          obtain ⟨birthState, birthMemory, hbirthChoice, hbirthStatus,
            before, beforeMemory, hbefore, hbeforeStatus, _, _, _, _, _⟩ := hinitializer
          obtain ⟨birthSelected, hbirthSelected, hbirthPayload, _, _⟩ := hbirthSelection
          have hbkStrict : b.val < k.val := by
            by_contra hnot
            have hsame : k = b := Fin.ext (by omega)
            subst k
            have hsameSelected : w = birthSelected := Option.some.inj (hw.symm.trans hbirthSelected)
            subst w
            have hbirthConfiguration :
                ((R b).output.preparation.followers.followers
                  (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                    ((R b).input.row.2 (R b).input.time).1)).configuration =
                  .ordinary birthState birthMemory := by
              change (ReferenceFollowerFixedReply.actualChoice (R b)
                (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  ((R b).input.row.2 (R b).input.time).1)).configuration = _
              rw [hdraw]
              exact hbirthChoice
            have hoccupied := ReferenceActiveConfirmationRelease.downConfirmationEvent_implies_occupied
              (R b).output.preparation birthSelected hbirthSelected birthState birthMemory
              hbirthConfiguration hevent
            have hnotUnoccupied : birthState.status ≠ .unoccupied := by
              intro hu
              rcases hoccupied with hpending | hreleased
              · rw [hu] at hpending
                cases hpending
              · rw [hu] at hreleased
                cases hreleased
            exact hnotUnoccupied hbirthStatus
          have hbInputFields : ReferenceActiveDataOwnership.occupiedFields v.view.payload i
              ((R b).input.state.followers i) := by
            rw [hbefore]
            simp [ReferenceActiveDataOwnership.occupiedFields, hbeforeStatus]
          have hbSelectedInputFields : ReferenceActiveDataOwnership.occupiedFields
              birthSelected.view.payload i ((R b).input.state.followers i) := by
            simpa only [hbirthPayload] using hbInputFields
          have hbStepFields := focal_step_occupied_fields (R b).input birthSelected
            hbirthSelected i hbSelectedInputFields
          have hbOutputFields : ReferenceActiveDataOwnership.occupiedFields v.view.payload i
              ((R b).output.next.followers i) := by
            rw [(R b).output_eq]
            simpa only [hbirthPayload] using hbStepFields
          have hselections : ∀ j : Fin (p.T - s), b.val < j.val → j.val < k.val →
              ∃ selected : ReferenceActivePhysicalStep.Selection (R j).input,
                (R j).output.preparation.coordinator.selection = some selected ∧
                  selected.view.payload = v.view.payload := by
            intro j hjb hjk
            obtain ⟨_, _, _, _, _, _, _, _, hselected, _, _⟩ :=
              hinterval j hjb (by omega)
            rcases hselected with ⟨selected, hselected, hpayload⟩
            exact ⟨selected, hselected, hpayload⟩
          have hinputFields := generated_interval_input_occupied_fields
            rate rewards C_star C_h s hs x i v.view.payload b k hbkStrict
            hbOutputFields hselections
          have hpreparedConfiguration :
              ((R k).output.preparation.followers.followers
                (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  ((R k).input.row.2 (R k).input.time).1)).configuration =
                .ordinary stateK memoryK := by
            change (ReferenceFollowerFixedReply.actualChoice (R k)
              (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                ((R k).input.row.2 (R k).input.time).1)).configuration = _
            rw [hdraw]
            exact hchoiceK
          have hoccupied := ReferenceActiveConfirmationRelease.downConfirmationEvent_implies_occupied
            (R k).output.preparation w hw stateK memoryK hpreparedConfiguration hevent
          have hstateOccupied : stateK.status ≠ .unoccupied := by
            intro hu
            rcases hoccupied with hpending | hreleased
            · rw [hu] at hpending
              cases hpending
            · rw [hu] at hreleased
              cases hreleased
          have hchoiceFields := ReferenceActiveDataOwnership.choice_occupied_fields_preserved
            v.view.payload i (R k).input.row ((R k).input.state.activations i)
            (R k).input.time ((R k).input.active i) ((R k).input.state.followers i) hinputFields
          have hactualChoice :
              ReferenceActiveDataOwnership.occupiedFields v.view.payload i
                (.ordinary stateK memoryK) := by
            have hprepare : ReferenceFollowerFixedReply.actualChoice (R k) i =
                DeclaredFollowerLocalRound.prepare rate i (R k).input.row
                  ((R k).input.state.activations i) (R k).input.time ((R k).input.active i)
                  ((R k).input.state.followers i) :=
              (R k).output.preparation.followers.followers_eq i
            rw [← hprepare, hchoiceK] at hchoiceFields
            exact hchoiceFields
          have hlastDown : stateK.lastDown = some (v.view.payload.downRecord i) :=
            hactualChoice hstateOccupied
          let initial := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
            rate rewards C_star C_h s hs x
          have hseedSpec := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
            rate rewards C_star C_h s hs x
          have hseedInitial : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial :=
            generated_seed_initial_followers rate rewards C_star C_h s hs x
          have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := hseedSpec.2.1
          let originalRun := ReferenceActivePhysicalHorizon.run initial x.1.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p x.1) rewards s (p.T - s)
            (by omega) hmode
          have hrunEq : originalRun =
              ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                rate rewards C_star C_h s hs x := by
            rfl
          have hrunCount : originalRun.records.length = p.T - s := by
            exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
          have hrecordsEq : originalRun.records =
              (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                rate rewards C_star C_h s hs x).records := by
            exact congrArg (fun run => run.records) hrunEq
          have hgetRunK :
              (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                rate rewards C_star C_h s hs x).records[k.val]? = some (R k) := by
            have hget := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
              rate rewards C_star C_h s hs x k
            exact hget
          have hgetKOption : originalRun.records[k.val]? = some (R k) := by
            calc
              originalRun.records[k.val]? =
                  (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                    rate rewards C_star C_h s hs x).records[k.val]? :=
                congrArg (fun records => records[k.val]?) hrecordsEq
              _ = some (R k) := hgetRunK
          have hboundK : k.val < originalRun.records.length := by
            rw [hrunCount]
            exact k.isLt
          have hgetK : originalRun.records[k.val] = R k := by
            rw [List.getElem?_eq_getElem hboundK] at hgetKOption
            exact Option.some.inj hgetKOption
          have hchoiceOriginal :
              (ReferenceFollowerFixedReply.actualChoice originalRun.records[k.val] i).configuration =
                .ordinary stateK memoryK := by
            rw [hgetK]
            exact hchoiceK
          have hprior := ReferenceFirstLiveConfirmationHistory.run_choice_prior_down
            initial x.1.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.1)
            rewards s (p.T - s) (by omega) hmode hseedInitial
          have hpriorAccepted := hprior
            (⟨k.val, by rw [hrunCount]; exact k.isLt⟩ : Fin originalRun.records.length)
            i stateK memoryK hchoiceOriginal (v.view.payload.downRecord i) hlastDown
          obtain ⟨j, hjkPrior, hacceptedOriginal⟩ := hpriorAccepted
          have hjk : j < k.val := by simpa using hjkPrior
          have hja : j < p.T - s := hjk.trans k.isLt
          let a : Fin (p.T - s) := ⟨j, hja⟩
          have hgetRunA :
              (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                rate rewards C_star C_h s hs x).records[a.val]? = some (R a) := by
            have hget := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
              rate rewards C_star C_h s hs x a
            exact hget
          have hgetAOption : originalRun.records[j]? = some (R a) := by
            calc
              originalRun.records[j]? = originalRun.records[a.val]? := by
                rfl
              _ = (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                    rate rewards C_star C_h s hs x).records[a.val]? :=
                congrArg (fun records => records[a.val]?) hrecordsEq
              _ = some (R a) := hgetRunA
          have hboundA : j < originalRun.records.length := by
            rw [hrunCount]
            exact hja
          have hgetA : originalRun.records[j] = R a := by
            rw [List.getElem?_eq_getElem hboundA] at hgetAOption
            exact Option.some.inj hgetAOption
          have haccepted : ReferenceFirstLiveConfirmationHistory.AcceptedDown
              (R a) i (v.view.payload.downRecord i) := by
            rw [hgetA] at hacceptedOriginal
            exact hacceptedOriginal
          refine ⟨a, ?_, haccepted, k, ?_, hkn, w, hw, hwpayload, hdraw,
            stateK, memoryK, hchoiceK, hevent⟩
          · change j < n.val
            exact hjk.trans hkn
          · change j < k.val
            exact hjk
      | cutoffChosen _ _ _ _ _ _ _ _ _ _ => trivial
      | clockFailure _ _ => trivial
      | initializerFailure _ _ _ _ => trivial
      | localFailure _ _ _ => trivial
  | collection _ _ _ _ _ => trivial
  | invalidCollectionCutoff => trivial
  | dagger => trivial

end Bandits.Support.ReferenceGeneratedLiveConfirmationAcceptedDown

end
