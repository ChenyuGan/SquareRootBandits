/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionPredictableStages
public import Bandits.Support.ReferenceFirstReplacementCollectionFreshPositiveService

import Bandits.Support.ReferenceFirstReplacementCollectionFreshFollowerGeometry
import Bandits.Support.ReferenceFirstReplacementCollectionPendingFoundation
import Bandits.Support.ReferenceFirstReplacementCollectionStoppedCompositeQuota
import Bandits.Support.ReferenceFirstReplacementCutoffPreparedBoundary
import Bandits.Support.ReferenceFirstReplacementCollectionUpReceiverProvenance
import Bandits.Support.ReferenceFirstReplacementCollectionPureUpWindowCut
import Bandits.Support.ReferenceFirstReplacementCollectionOldDownSenderReadiness

open _root_.Bandits.Support.ReferenceFirstReplacementCollectionFreshPositiveService

/-!
# Ordinary stages and pointwise service in the first replacement collection

Sources: `sources/zip4/manuscript/06_interruptions.tex:289-349,459-487` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-85,141-157`.

This module consumes the actual cutoff-inclusive K list supplied by the
collection geometry and the existing literal pending/stage observers. It
assembles pointwise service identities only at those actual masked K
coordinates; it proves no calendar converse or waiting law.
-/

noncomputable section

open Bandits.Support ConstructorDimensions
open ReferenceActivePhysicalStep
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionOrdinaryStages

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

open ReferenceFirstReplacementCollectionPendingFoundation

private abbrev follower_control_geometry_root
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :=
  ReferenceFirstReplacementCollectionFreshFollowerGeometry.complete_first_replacement_collection_follower_control_geometry
    rate z rewards C_star C_h

private abbrev pending_coordinates_root
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :=
  ReferenceFirstReplacementCollectionPendingFoundation.complete_first_replacement_pending_coordinates
    rate rewards C_star C_h control0 z

private abbrev composite_quota_root
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :=
  ReferenceFirstReplacementCollectionStoppedCompositeQuota.complete_first_replacement_collection_stopped_composite_quota
    rate z rewards C_star C_h control0

private abbrev cutoff_boundary_root
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :=
  ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
    rate z rewards C_star C_h

private abbrev up_receiver_root
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :=
  ReferenceFirstReplacementCollectionUpReceiverProvenance.complete_first_replacement_collection_up_receiver_provenance
    rate z rewards C_star C_h

private abbrev pure_up_window_root
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :=
  ReferenceFirstReplacementCollectionPureUpWindowCut.complete_first_replacement_collection_pure_up_window_cut
    rate z rewards C_star C_h

private abbrev collection_selection_pending_root
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hc : r.input.state.coordinator = .collection payload ledger saved)
    (hn : ReferenceCollectionPhaseHistory.laterChosen r.input = false)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected) :=
  ReferenceFirstReplacementCollectionOldDownSenderReadiness.collection_selection_pending
    r payload ledger saved hc hn selected hs

@[expose] public section

/-- Every actual record of the cutoff-inclusive collection has an ordinary
unoccupied follower choice. On a pending K coordinate that choice is exactly
the literal OLD or FORMED task stage. -/
theorem complete_first_replacement_collection_ordinary_stages
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let P := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let K := cut :: (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            ∀ a : Fin K.length, ∀ i : Fin (p.m - 1),
              (ReferenceFirstReplacementCollectionPredictableStages.choiceStage
                (K.get a) P i = .old ∨
               ReferenceFirstReplacementCollectionPredictableStages.choiceStage
                (K.get a) P i = .formed) ∧
              (i ∈ P_repl rate rewards C_star C_h control0 (u - 1 + a.val) z →
                (ReferenceFirstReplacementCollectionPredictableStages.OLD
                    rate rewards C_star C_h control0 (u - 1 + a.val) i z ∨
                 ReferenceFirstReplacementCollectionPredictableStages.FORMED
                    rate rewards C_star C_h control0 (u - 1 + a.val) i z) ∧
                ReferenceFirstReplacementCollectionPredictableStages.taskStage
                    rate rewards C_star C_h control0 (u - 1 + a.val) i z =
                  some (ReferenceFirstReplacementCollectionPredictableStages.choiceStage
                    (K.get a) P i))
          | _ => True
      | _ => True := by
  have hG := follower_control_geometry_root rate z rewards C_star C_h
  have hS := ReferenceFirstReplacementCollectionPredictableStages.complete_first_replacement_predictable_stages
    rate rewards C_star C_h control0 z
  dsimp only at hG hS ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hG hS ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hG hS ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hG hS ⊢
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [tail, c, hc] at hG hS ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hG hS ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hG hS ⊢
          intro a i
          let K := cut :: (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let P := installed.registers.payload
          obtain ⟨choice, memory, U, hactual, hstatus, hdomain, hzero, horigin, hU, hall⟩ :=
            hG a i
          have hordinary :=
            (ReferenceFirstReplacementCollectionPredictableStages.choiceStage_old_or_formed
              (r := K.get a) (payload := P) i).2
              ⟨choice, memory, hactual, hstatus⟩
          obtain ⟨hcoordinates, htask⟩ := hS a i
          refine ⟨hordinary, ?_⟩
          intro hmem
          have hstageEq := htask
          rw [ite_eq_left hmem] at hstageEq
          have hchoiceIdentity := hstageEq
          rcases hordinary with hold | hformed
          ·
            rw [hold] at hstageEq
            exact ⟨Or.inl hstageEq, hchoiceIdentity⟩
          ·
            rw [hformed] at hstageEq
            exact ⟨Or.inr hstageEq, hchoiceIdentity⟩

/-- At each actual masked-pending K coordinate, the literal OLD/FORMED stage
selects the corresponding whole-control fresh service identity. The returned
readouts retain B's actual record, input, payload, pending set, cutoff, and
full source-control invariances. -/
theorem complete_first_replacement_collection_ordinary_stage_service
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let P := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let M := fun i => P.downRecord i
            ∀ a : Fin K.length,
              let r := K.get a
              let t := r.input.time
              let n := u - 1 + a.val
              ∃ v0 : ReferenceActivePhysicalStep.Selection r.input,
                r.output.preparation.coordinator.selection = some v0 ∧
                v0.view.payload = P ∧
                v0.view.cutoff = some
                  (CoordinatorCollectionUpRoundStep.localCutoff cut.input.time) ∧
                ∀ i : Fin (p.m - 1), i ∈ P_repl rate rewards C_star C_h control0 n z →
                  (ReferenceFirstReplacementCollectionPredictableStages.OLD
                      rate rewards C_star C_h control0 n i z ∧
                    ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt r i (M i) ∧
                    ∀ h : ContinuousLearningRows.TimeControl p,
                      let zh := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h
                      let xh := ReferenceLaterOptionalControlResampling.withControl r.input h
                      let wD := CoordinatorLocalArmChoice.storedDownFlatWord P i
                      ∃ rh : ReferenceCompletePhysicalHistory.RoundRecord p rate,
                        ∃ vh : ReferenceActivePhysicalStep.Selection xh,
                          ReferenceSourcePrefixHistoryFiltration.actualRecord
                            rate rewards C_star C_h t zh = some rh ∧ rh.input = xh ∧
                          (prepare xh).coordinator.selection = some vh ∧
                          vh.view.payload = P ∧
                          vh.view.pendingAtChoice = v0.view.pendingAtChoice ∧
                          vh.view.cutoff = v0.view.cutoff ∧
                          ReferenceFirstReplacementCollectionCommonStopObservation.L
                            rate rewards C_star C_h control0 s u i t.val zh = false ∧
                          ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt rh i (M i) ∧
                          ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
                            (rate := rate) rewards C_star C_h i t zh =
                          (ReferenceFirstCollectionDownConditionalService.downServiceFormulaSet
                            rewards t i wD).indicator (fun _ => (1 : ℝ)) h) ∨
                  (ReferenceFirstReplacementCollectionPredictableStages.FORMED
                      rate rewards C_star C_h control0 n i z ∧
                    ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt r i (M i) ∧
                    ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
                      ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
                      ∃ U : OrdinaryMessageCodec.UpRecord
                          (ReferencePrelaunchFollower.codecParams p rate.eta),
                        (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                          .ordinary choice memory ∧
                        choice.status = .unoccupied ∧ choice.lastDown = some (M i) ∧
                        U.val = ActiveFollowerQueueOperation.upOfferFields choice ∧
                        U.val.sigma = (M i).val.sigma ∧ 0 < U.val.sigma ∧
                        ∀ h : ContinuousLearningRows.TimeControl p,
                          let zh := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h
                          let xh := ReferenceLaterOptionalControlResampling.withControl r.input h
                          ∃ rh : ReferenceCompletePhysicalHistory.RoundRecord p rate,
                            ∃ vh : ReferenceActivePhysicalStep.Selection xh,
                              ReferenceSourcePrefixHistoryFiltration.actualRecord
                                rate rewards C_star C_h t zh = some rh ∧ rh.input = xh ∧
                              (prepare xh).coordinator.selection = some vh ∧
                              vh.view.payload = P ∧
                              vh.view.pendingAtChoice = v0.view.pendingAtChoice ∧
                              vh.view.cutoff = v0.view.cutoff ∧
                              ReferenceFirstReplacementCollectionCommonStopObservation.L
                                rate rewards C_star C_h control0 s u i t.val zh = false ∧
                              ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt
                                rh i (M i) ∧
                              ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
                                (rate := rate) rewards C_star C_h i t zh =
                              (ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet
                                (rate := rate) rewards t i U).indicator (fun _ => (1 : ℝ)) h)
          | _ => True
      | _ => True := by
  classical
  have hStages := complete_first_replacement_collection_ordinary_stages
    rate z rewards C_star C_h control0
  have hServices := complete_first_replacement_collection_fresh_positive_tests
    rate z rewards C_star C_h control0
  have hPending := pending_coordinates_root rate z rewards C_star C_h control0
  have hQuota := composite_quota_root rate z rewards C_star C_h control0
  have hBoundary := cutoff_boundary_root rate z rewards C_star C_h
  have hReceiver := up_receiver_root rate z rewards C_star C_h
  have hPure := pure_up_window_root rate z rewards C_star C_h
  dsimp only at hStages hServices hPending hQuota hBoundary hReceiver hPure ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hStages hServices hPending hQuota hBoundary hReceiver hPure ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hStages hServices hPending hQuota hBoundary hReceiver hPure ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput]
        at hStages hServices hPending hQuota hBoundary hReceiver hPure ⊢
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [tail, c, hc] at hStages hServices hPending hQuota hBoundary hReceiver hPure ⊢
        rcases hBoundary with ⟨_, hBoundary⟩
        rcases hReceiver with ⟨_, _, hReceiver⟩
        rcases hPure with ⟨_, _, hPure⟩
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hStages hServices hPending hQuota hBoundary hReceiver hPure ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hStages hServices hPending hQuota hBoundary hReceiver hPure ⊢
          rcases hBoundary with
            ⟨_, _, _, _, _, _, _, _, _, _, _, selectedB, hselectedB, _, hpendingB, _, _⟩
          rcases hQuota with ⟨_, hcalendar, _, _⟩
          rcases hPure with ⟨_, ⟨hZ0, hZLinks, hZRecords⟩, _⟩
          rcases hReceiver with ⟨hEndpoints, _, _⟩
          let P := installed.registers.payload
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.output.next (W.take j)
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := fun i => P.downRecord i
          intro a
          let r := K.get a
          let t := r.input.time
          let n := u - 1 + a.val
          obtain ⟨v0, hv0, hvpay, hvcut, hbranches⟩ := hServices a
          refine ⟨v0, hv0, hvpay, hvcut, ?_⟩
          intro i hmem
          obtain ⟨hOnset, hActualRecord, hRaw, hPendingCoordinates⟩ := hPending a
          have htime : t.val = n := by
            have hc := hcalendar a
            change (K.get a).input.time.val + 1 =
              cut.input.time.val + 1 + a.val at hc
            have hc' : (K.get a).input.time.val = cut.input.time.val + a.val := by
              omega
            simpa [r, t, n, u] using hc'
          have hLfalse :
              ReferenceFirstReplacementCollectionCommonStopObservation.L
                rate rewards C_star C_h control0 s u i t.val z = false := by
            have hfilter := hmem
            change i ∈ (Praw rate rewards C_star C_h n z).filter
              (fun j => match payloadOnset rate rewards C_star C_h n z with
                | none => false
                | some (_, u') =>
                    !ReferenceFirstReplacementCollectionCommonStopObservation.L
                      rate rewards C_star C_h control0 s u' j n z) at hfilter
            rcases Finset.mem_filter.mp hfilter with ⟨_, hkeep⟩
            rw [hOnset] at hkeep
            have hL_n :
                ReferenceFirstReplacementCollectionCommonStopObservation.L
                  rate rewards C_star C_h control0 s u i n z = false := by
              simp only at hkeep
              change (!ReferenceFirstReplacementCollectionCommonStopObservation.L
                rate rewards C_star C_h control0 s u i n z) = true at hkeep
              cases hvalue :
                  ReferenceFirstReplacementCollectionCommonStopObservation.L
                    rate rewards C_star C_h control0 s u i n z <;>
                simp [hvalue] at hkeep ⊢
            rw [htime]
            exact hL_n
          have hViewPending : i ∈ v0.view.pendingAtChoice := by
            cases a using Fin.cases with
            | zero =>
              have hr : r = cut := by simp [r, K]
              have hvCut :
                  cut.output.preparation.coordinator.selection = some v0 := by
                simpa only [r, K, List.get_cons_zero] using hv0
              have hselectedCut :
                  cut.output.preparation.coordinator.selection = some selectedB := by
                simpa [hcut] using hselectedB
              have hvEq : v0 = selectedB := Option.some.inj (hvCut.symm.trans hselectedCut)
              have hview : v0.view.pendingAtChoice = Finset.univ := by
                simpa [hvEq] using hpendingB
              rw [hview]
              exact Finset.mem_univ i
            | succ j =>
              have hjW : j.val < W.length := by
                exact j.isLt
              have hr : r = W.get ⟨j.val, hjW⟩ := by
                dsimp only [r, K, List.get_cons_succ']
              let q : Fin K.length := ⟨j.val + 1, by dsimp [K]; omega⟩
              have hrecordState : (K.get q).input.state = E j := by
                have hstate := (hZRecords q).1
                have hendpoint := hZLinks j.val (Nat.le_of_lt hjW)
                change (K.get q).input.state = Z (j.val + 1) at hstate
                change Z (j.val + 1) = E j.val at hendpoint
                exact hstate.trans hendpoint
              have hselection : r.output.preparation.coordinator.selection = some v0 := by
                simpa only [r, K, List.get_cons_succ'] using hv0
              have hnotDagger : r.input.state.coordinator ≠ .dagger := by
                intro hd
                have hprep : (prepare r.input).coordinator = .dagger := by
                  change dispatch r.input = .dagger
                  exact ReferenceActivePhysicalStep.dispatch_dagger r.input hd
                have hnone : r.output.preparation.coordinator.selection = none := by
                  rw [r.output_eq]
                  change (prepare r.input).coordinator.selection = none
                  rw [hprep]
                  rfl
                cases hnone.symm.trans hselection
              rcases hEndpoints j.val (Nat.le_of_lt hjW) with hdagger | ⟨taskLedger, saved, hcoord, _, _, _⟩
              · have hbad : r.input.state.coordinator = .dagger := by
                  exact (congrArg (fun st : ReferenceActivePhysicalStep.State p rate => st.coordinator)
                    hrecordState).trans hdagger
                exact (hnotDagger hbad).elim
              · have hcoordInput :
                    r.input.state.coordinator = .collection P taskLedger saved := by
                  exact (congrArg (fun st : ReferenceActivePhysicalStep.State p rate => st.coordinator)
                    hrecordState).trans hcoord
                have hn : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
                  have hmemW : r ∈ W := by
                    have hr : r = W.get ⟨j, hjW⟩ := by
                      simp [r, K]
                    exact hr ▸ List.get_mem W ⟨j, hjW⟩
                  have hall := List.all_eq_true.mp (List.all_takeWhile
                    (l := R.drop (c + 1))
                    (p := fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input))
                    r hmemW
                  cases htag : ReferenceCollectionPhaseHistory.laterChosen r.input <;>
                    simp_all only [Bool.not_true, Bool.false_eq_true]
                have hQ : i ∈ ReferenceFirstCollectionPendingObservation.Q
                    rate rewards C_star C_h P.sigma.val t z :=
                  (hPendingCoordinates i).mp hmem |>.1
                have hactual :
                    ReferenceSourcePrefixHistoryFiltration.actualRecord
                      rate rewards C_star C_h t z = some r := by
                  simpa only [t, r, K, List.get_cons_succ'] using hActualRecord
                have hQledger : i ∈ taskLedger.pending := by
                  simpa [ReferenceFirstCollectionPendingObservation.Q, hactual,
                    hcoordInput] using hQ
                have hfields := collection_selection_pending_root r P taskLedger saved
                  hcoordInput hn v0 hselection
                rw [hfields.2]
                exact hQledger
          have hconditions := hbranches i hViewPending hLfalse
          obtain ⟨_, hmaskedStage⟩ := hStages a i
          obtain ⟨hstageDisj, hstageEq⟩ := hmaskedStage hmem
          rcases hstageDisj with hOld | hFormed
          · have hactualOld :=
              (ReferenceFirstReplacementCollectionPredictableStages.choiceStage_old_iff
                (r := r) (payload := P) i).mp
                (Option.some.inj (hstageEq.symm.trans hOld))
            left
            refine ⟨hOld, hactualOld, ?_⟩
            exact hconditions.1 hactualOld
          · have hreplyFormed :=
              (ReferenceFirstReplacementCollectionPredictableStages.choiceStage_formed_iff
                (r := r) (payload := P) i).mp
                (Option.some.inj (hstageEq.symm.trans hFormed))
            right
            refine ⟨hFormed, hreplyFormed, ?_⟩
            exact hconditions.2 hreplyFormed

end

end Bandits.Support.ReferenceFirstReplacementCollectionOrdinaryStages

end
