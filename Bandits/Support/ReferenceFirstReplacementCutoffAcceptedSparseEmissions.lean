/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementContinuingNumericalReplay
public import Bandits.Support.ReferenceFirstReplacementCutoffDownRecovery

import Lean.Elab.Tactic.Omega

/-!
# Accepted sparse emissions at the first replacement cutoff

Sources: `sources/zip4/manuscript/06_interruptions.tex:193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This internal result follows the actual original follower buffer from the
first replacement launch through its first accepted cutoff DOWN. It records
the actual acceptance, excludes a prior reset on the replacement slice, and
identifies every dated emission in the checked interval. It asserts no
numerical replay, global initial queue, score, or UP law.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower ActiveFollowerLifecycle ActiveFollowerDownAcceptance
open ReferenceDownReception SparseCalendarReplay PublicDiscreteDraws
open ReferenceFollowerBufferProvenance ReferenceFollowerReplyChronology
open ReferenceFollowerSparseEmissionRecovery

namespace Bandits.Support.ReferenceFirstReplacementCutoffAcceptedSparseEmissions

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem sparseBufferContribution_flatMap_sum
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (i : Fin (p.m - 1)) (date : ℕ)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate))) :
    SparseCalendarReplay.sparseBufferContribution (p.m - 1) (ConstructorDimensions.D p : ℝ)
      rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) date
      (records.flatMap (ReferenceFollowerBufferProvenance.logEmission i)) =
    (records.map fun record =>
      SparseCalendarReplay.sparseBufferContribution (p.m - 1) (ConstructorDimensions.D p : ℝ)
        rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) date
        (ReferenceFollowerBufferProvenance.logEmission i record)).sum := by
  classical
  induction records with
  | nil => simp [SparseCalendarReplay.sparseBufferContribution]
  | cons record rest ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
      rw [SparseCalendarReplay.sparseBufferContribution_append, ih]

private theorem run_records_take
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n ≤ total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan hmode).records.take n =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n (by omega) hmode).records := by
  obtain ⟨suffix, hsuffix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start n (total - n) (by omega) hmode
  have harith : n + (total - n) = total := by omega
  have hsplit :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan hmode).records =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n (by omega) hmode).records ++ suffix := by
    simpa only [harith] using hsuffix
  have hlen := ReferenceActivePhysicalHorizon.run_record_count
    initial rows selected rewards start n (by omega) hmode
  rw [hsplit]
  rw [List.take_append_of_le_length (by simp [hlen])]
  simp [hlen]

private theorem connected_successor_state
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (j : ℕ) (hj : j + 1 < records.length) :
    records[j + 1].input.state = records[j].output.next := by
  induction records generalizing initial j with
  | nil =>
      simp only [List.length_nil] at hj
      omega
  | cons record rest ih =>
      simp only [List.length_cons] at hj
      cases j with
      | zero =>
          cases rest with
          | nil =>
              simp only [List.length_nil] at hj
              omega
          | cons next rest =>
              change record.input.state = initial ∧
                ReferenceActivePhysicalHorizon.Connected record.output.next (next :: rest) final at chain
              have hrest := chain.2
              change next.input.state = record.output.next ∧ _ at hrest
              simpa only [List.getElem_cons_succ, List.getElem_cons_zero] using hrest.1
      | succ j =>
          change record.input.state = initial ∧
            ReferenceActivePhysicalHorizon.Connected record.output.next rest final at chain
          have hrest := chain.2
          exact ih hrest j (by omega)

private theorem outputFollower_matches_next
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) :
    record.output.next.followers i = (record.output.followers i).configuration := by
  rw [record.output_eq]
  rfl

private theorem getElem_drop_take_eq {α : Type} (xs : List α)
    (offset count index : ℕ) (hindex : index < count)
    (hbound : offset + index < xs.length) :
    ((xs.drop offset).take count)[index]'(by
      simp only [List.length_take, List.length_drop]
      omega) = xs[offset + index]'hbound := by
  simp only [List.getElem_take, List.getElem_drop]

/-- At an actual accepted first-replacement cutoff, the checked DOWN scan and
the complete original sparse log agree on every date from the transmitted
start through its exclusive endpoint. -/
theorem complete_first_replacement_cutoff_accepted_sparse_emissions
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
        let X := (R.drop v).take (1 + tail.length)
        let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
        let L := X.length
        let cIndex := v + 1 + tail.length
        match R[cIndex]? with
        | none => True
        | some cut =>
          ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen cut = false ∧
          match cut.output.preparation.coordinator with
          | .live _registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            C.length = L ∧ X = birth :: tail ∧
            ∀ i : Fin (p.m - 1),
              match (cut.output.followers i).down with
              | none => True
              | some diagnostic => match diagnostic.outcome with
                | .accepted before _after _raw M scan _registers _lastService =>
                  M = payload.downRecord i ∧
                  (cut.output.followers i).downInput = some before ∧
                  scan.endpoint = u ∧
                  u = M.val.sigma + L ∧
                  (∀ j : Fin X.length,
                    ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i (X.get j)) ∧
                  (∀ j : Fin X.length, ∀ state memory,
                    ((X.get j).output.preparation.followers.followers i).configuration =
                      .ordinary state memory →
                    state.status = ActiveRoundActions.FollowerStatus.unoccupied) ∧
                  (∀ j : Fin X.length,
                    (X.get j).input.time.val + 1 = M.val.sigma + j.val ∧
                    ActiveFollowerDownAcceptance.bufferArrivalAt p rate M before
                      (M.val.sigma + j.val) =
                      ReferenceFollowerSparseEmissionRecovery.emissionContribution M i (X.get j))
                | _ => True
          | _ => True
      | _ => True := by
  classical
  have hnumerical :=
    ReferenceFirstReplacementContinuingNumericalReplay.complete_first_replacement_continuing_follower_numerical_replay
      rate source rewards C_star C_h
  have hdown :=
    ReferenceFirstReplacementCutoffDownRecovery.complete_first_replacement_cutoff_down_recovery_and_finish
      rate source rewards C_star C_h
  have hboundary :=
    ReferenceFirstReplacementFollowerBoundary.complete_first_replacement_follower_boundary
      rate source rewards C_star C_h
  have hbirth :=
    ReferenceFirstReplacementDownRecovery.complete_first_replacement_down_recovery_and_finish
      rate source rewards C_star C_h
  have hsource :=
    ReferenceFirstReplacementNumericalSourceRecovery.complete_first_replacement_numerical_source_stream
      rate source rewards C_star C_h
  dsimp only at hnumerical hdown hboundary hbirth hsource ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hnumerical hdown hboundary hbirth hsource ⊢
    cases hc : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection old ledger clock cutoff outcome =>
      rw [hc] at hnumerical hdown hboundary hbirth hsource
      cases outcome <;> try trivial
      rename_i core consistent started hs instruction hinstruction output hcons clockData installed arm
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hnumerical hboundary hbirth hsource ⊢
      let payload := installed.registers.payload
      let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
      let X := (R.drop v).take (1 + tail.length)
      let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
      let L := X.length
      let cIndex := v + 1 + tail.length
      cases hcGet : R[v + 1 +
          (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length]? with
      | none => trivial
      | some cut =>
        dsimp only [tail, cIndex] at hdown ⊢
        simp only [hcGet] at hdown ⊢
        rcases hdown with ⟨hnotContinuing, hcutBranch⟩
        refine ⟨hnotContinuing, ?_⟩
        cases hcutCoord : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
            rw [hcutCoord] at hcutBranch
            cases outcome <;> try trivial
            dsimp only [ReferenceActivePhysicalStep.liveInput] at hcutBranch ⊢
            rcases hcutBranch with ⟨hpayload, htimeBirth, htimeSource, hrows, hselectedRow,
              hrewards, hsigmaPayload, hsourceStart, hfirstCutoff, hgridBound, hcause,
              hselectedBlock⟩
            rcases hselectedBlock with ⟨selected, hselection, hselectedPayload, hpendingChoice,
              hcutoffChoice, hfollower⟩
            have hcurrentIndex : cIndex < R.length :=
              (List.getElem?_eq_some_iff.mp hcGet).1
            have hcurrentGet : R.get ⟨cIndex, hcurrentIndex⟩ = cut := by
              exact (List.getElem?_eq_some_iff.mp hcGet).2
            have hcurrentGetElem : R[cIndex]'hcurrentIndex = cut := by
              simpa only [List.get_eq_getElem] using hcurrentGet
            have hv : v < R.length := (List.getElem?_eq_some_iff.mp hb).1
            have hbirthGet : R.get ⟨v, hv⟩ = birth := by
              exact (List.getElem?_eq_some_iff.mp hb).2
            have hRlen : R.length = p.T - s := by
              simpa [R, s] using
                ReferenceCompletePhysicalHistory.completeSuffixRecords_length
                  rate source rewards C_star C_h
            have hspanTotal : s + (p.T - s) ≤ p.T := by omega
            have hcurrentTotal : cIndex < p.T - s := by
              rw [← hRlen]
              exact hcurrentIndex
            have hcutIndexBound : v + 1 + tail.length < R.length := by
              simpa only [cIndex] using hcurrentIndex
            have hspanCurrent : s + cIndex ≤ p.T := by omega
            have hspanCurrentNext : s + (cIndex + 1) ≤ p.T := by omega
            have hspanV : s + v ≤ p.T := by omega
            have htimeAt : ∀ j : Fin R.length, (R.get j).input.time.val = s + j.val := by
              intro j
              obtain ⟨_, _, hactual⟩ :=
                ReferenceLaterLiveNumericalReadout.source_record_prefix
                  rate rewards C_star C_h source j
              have htime := congrArg
                (fun x : ReferenceActivePhysicalHorizon.RoundRecord
                    (p := p) (rate := rate) => x.input.time.val) hactual
              simpa [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
                ReferenceActivePhysicalHorizon.roundInputAt] using htime
            have hbirthTime : birth.input.time.val = s + v := by
              rw [← hbirthGet]
              exact htimeAt ⟨v, hv⟩
            have hmsgSigma : ∀ i : Fin (p.m - 1),
                (payload.downRecord i).val.sigma = s + v + 1 := by
              intro i
              rw [payload.downRecord_fields i, hsigmaPayload, hbirthTime]
            have hcurrentCutoffTime : cut.input.time.val = s + v + 1 + tail.length := by
              simpa [tail] using htimeSource
            have hXeq : X = birth :: tail := hnumerical.2.1
            have hCeq : C.length = X.length := hnumerical.1
            have hL : L = X.length := rfl
            have hLlen : L = 1 + tail.length := by
              calc
                L = X.length := hL
                _ = (birth :: tail).length := by rw [hXeq]
                _ = 1 + tail.length := by
                  simp only [List.length_cons]
                  omega
            have hXlen : X.length = 1 + tail.length := hL.symm.trans hLlen
            have hstatusBirth : ∀ i : Fin (p.m - 1),
                ∃ st mem, (birth.output.preparation.followers.followers i).configuration =
                  .ordinary st mem ∧ st.status = ActiveRoundActions.FollowerStatus.unoccupied := by
              intro i
              obtain ⟨_, followers⟩ := hbirth
              obtain ⟨st, mem, _, _, hstatus, hprepared, _⟩ := followers i
              exact ⟨st, mem, hprepared, hstatus⟩
            refine ⟨hCeq.trans hL.symm, hXeq, ?_⟩
            intro i
            cases hdiagnostic : (cut.output.followers i).down with
            | none => trivial
            | some diagnostic =>
                cases houtcome : diagnostic.outcome with
                | skipped before reason => simp only [houtcome] at ⊢
                | inputFailure before reason => simp only [houtcome] at ⊢
                | decodeOrParseRejected before after raw => simp only [houtcome] at ⊢
                | parsedButUnaccepted before after raw M => simp only [houtcome] at ⊢
                | outputFailure before reason => simp only [houtcome] at ⊢
                | accepted before after raw M scan registers' lastService =>
                    simp only [houtcome] at ⊢
                    rcases hfollower i with ⟨old, memory, hinput, hdomainOld, hmassOld,
                      hzeroOld, hstrictOld, hbusyOld, hdecision, hstartRound, hprepared,
                      hdomainChoice, hmassChoice, hpair, hdates, hup, hstarted, hcredit,
                      logged, post, hlogging, hbuffer, hoperation, hlast, hS, hdelta,
                      hbacklog, hflagChoice, hloggedUnoccupied, hloggedPair, hloggedDates,
                      hnoAppend, hconsume, hpostUnoccupied, hpostDomain, hpostMass,
                      hpostDelta, hpostFlag, hbranches, hrecordResult, hloggedInput,
                      hloggedCut, hrelease, hfinishRound, hreleaseFinish, hfollowersActual⟩
                    have hcutDiag : (cut.output.followers i).down = some diagnostic := hdiagnostic
                    have hfollowersActualLive := hfollowersActual
                    have hcutInput : (cut.output.followers i).downInput = some logged := by
                      rw [hfollowersActualLive]
                    have hcutDiagnosticOutput : (cut.output.followers i).down =
                        some (ReferenceDownReception.referenceDownCut p
                          (cut.output.preparation.coordinator.downView) i cut.input.row
                          cut.input.time
                          (cut.output.preparation.feedback.observations
                            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged) := by
                      rw [hcutCoord]
                      rw [hfollowersActualLive]
                      rfl
                    have hdiagEq : diagnostic =
                        ReferenceDownReception.referenceDownCut p
                          (cut.output.preparation.coordinator.downView) i cut.input.row
                          cut.input.time
                          (cut.output.preparation.feedback.observations
                            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged := by
                      apply Option.some.inj
                      exact hcutDiag.symm.trans hcutDiagnosticOutput
                    have hdiagnosticOutcome :
                        (ReferenceDownReception.referenceDownCut p
                          (cut.output.preparation.coordinator.downView) i cut.input.row
                          cut.input.time
                          (cut.output.preparation.feedback.observations
                            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).outcome =
                          .accepted before after raw M scan registers' lastService := by
                      rw [hcutCoord] at hdiagEq
                      rw [hcutCoord]
                      rw [← hdiagEq]
                      exact houtcome
                    rw [hcutCoord] at hdiagnosticOutcome
                    rcases hbranches with hskipped | hrejected | hparsed | haccepted
                    · have himpossible := hdiagnosticOutcome.symm.trans hskipped.2.1
                      cases himpossible
                    · have hrejectedOutcome :=
                        hrejected.2.2.2.2.2.2.2.2.1
                      have himpossible := hdiagnosticOutcome.symm.trans hrejectedOutcome
                      cases himpossible
                    · have hparsedOutcome := hparsed.2.2.2.2.2.2.2.1
                      have himpossible := hdiagnosticOutcome.symm.trans hparsedOutcome
                      cases himpossible
                    · rcases haccepted with ⟨hselectedDown, hdecodedWord, hraw, hfiltered,
                        hrawComparison, hordinaryParse, hordinaryAcceptance, hcheckedData⟩
                      rcases hcheckedData with ⟨accepted, hcheckedData⟩
                      rcases hcheckedData with ⟨recovered, hchecked, hscanEndpoint,
                        hrounds, hqueueRecords, hallTrue, hregisters, hprefixReplay,
                        hlastService, hcutOutcome, hpostEq⟩
                      have hacceptedOutcome := hdiagnosticOutcome.symm.trans hcutOutcome
                      injection hacceptedOutcome with hbefore hafter hrawEq hMEq
                        hscanEq hregistersEq hserviceEq
                      subst before
                      subst M
                      subst scan
                      have hstartStrict :
                          ReferencePrelaunchFollower.acceptedStart logged <
                            (payload.downRecord i).val.sigma := by
                        exact accepted.1
                      have hloggedLast : logged.lastDown = old.lastDown := by
                        calc
                          logged.lastDown = { old with status := .unoccupied }.lastDown := hlast
                          _ = old.lastDown := rfl
                      have holdUnoccupied :
                          old.status = ActiveRoundActions.FollowerStatus.unoccupied := by
                        by_contra hnotUnoccupied
                        have hlastDown : old.lastDown = some (payload.downRecord i) :=
                          (hbusyOld hnotUnoccupied).1
                        have hstartLogged :
                            ReferencePrelaunchFollower.acceptedStart logged =
                              (payload.downRecord i).val.sigma := by
                          simp [ReferencePrelaunchFollower.acceptedStart,
                            hloggedLast, hlastDown]
                        rw [hstartLogged] at hstartStrict
                        omega
                      have hcurrentInput : cut.input.state.followers i = .ordinary old memory := hinput
                      have hstrictOldCurrent :
                          ReferencePrelaunchFollower.acceptedStart old <
                            (payload.downRecord i).val.sigma := by
                        have hstartFrame :
                            ReferencePrelaunchFollower.acceptedStart old =
                              ReferencePrelaunchFollower.acceptedStart logged := by
                          unfold ReferencePrelaunchFollower.acceptedStart
                          rw [← hloggedLast]
                        rw [hstartFrame]
                        exact hstartStrict
                      have hmsgSigma : (payload.downRecord i).val.sigma = s + v + 1 := by
                        rw [payload.downRecord_fields i, hsigmaPayload, hbirthTime]
                      have hendpointL : cut.input.time.val + 1 =
                          (payload.downRecord i).val.sigma + L := by
                        rw [hcurrentCutoffTime, hmsgSigma]
                        omega
                      obtain ⟨hcSource, _, _⟩ :=
                        ReferenceLaterLiveNumericalReadout.source_record_prefix
                          rate rewards C_star C_h source ⟨v, hv⟩
                      have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
                        rate source rewards C_star C_h hcSource
                      let active := ReferenceFirstLaunchNumericalCell.launchState
                        rate source rewards C_star C_h hcSource
                      have hconnected :=
                        ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
                          rate source rewards C_star C_h active hlaunch
                      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
                        rate source rewards C_star C_h hcSource
                      have hactiveMode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
                        rate source rewards C_star C_h active hlaunch
                      have hcompleteRecords :=
                        ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
                          rate source rewards C_star C_h active hlaunch
                      have hprefixCurrent :
                          (ReferenceActivePhysicalHorizon.run active source.1.2
                            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                            cIndex hspanCurrent seed.activeAtStart).records = R.take cIndex := by
                        calc
                          (ReferenceActivePhysicalHorizon.run active source.1.2
                            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                            cIndex hspanCurrent seed.activeAtStart).records =
                              (ReferenceActivePhysicalHorizon.run active source.1.2
                                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                                (p.T - s) hspanTotal hactiveMode).records.take cIndex := by
                                  symm
                                  exact run_records_take active source.1.2
                                    (ActualInitializationPhysicalStep.selectedRowIndex p source)
                                    rewards s (p.T - s) hspanTotal hactiveMode cIndex
                                    (by rw [← hRlen]; omega)
                          _ = R.take cIndex := by rw [← hcompleteRecords]
                      have hprefixV :
                          (ReferenceActivePhysicalHorizon.run active source.1.2
                            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                            v hspanV seed.activeAtStart).records = R.take v := by
                        calc
                          (ReferenceActivePhysicalHorizon.run active source.1.2
                            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                            v hspanV seed.activeAtStart).records =
                              (ReferenceActivePhysicalHorizon.run active source.1.2
                                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                                (p.T - s) hspanTotal hactiveMode).records.take v := by
                                  symm
                                  exact run_records_take active source.1.2
                                    (ActualInitializationPhysicalStep.selectedRowIndex p source)
                                    rewards s (p.T - s) hspanTotal hactiveMode v
                                    (by rw [← hRlen]; omega)
                          _ = R.take v := by rw [← hcompleteRecords]
                      have hcanonicalRecord :
                          ReferenceAssignmentPayloadChronology.actualRunRecordAt active
                            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                            rewards s cIndex hspanCurrentNext seed.activeAtStart = cut := by
                        have hindexed : R.get ⟨cIndex, hcurrentIndex⟩ =
                            ReferenceAssignmentPayloadChronology.actualRunRecordAt active
                              source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                              rewards s cIndex hspanCurrentNext seed.activeAtStart := by
                          simpa [active, seed] using
                            (ReferenceLaterLiveNumericalReadout.source_record_prefix
                              rate rewards C_star C_h source ⟨cIndex, hcurrentIndex⟩).2.2
                        exact hindexed.symm.trans hcurrentGet
                      let choiceState : ReferencePrelaunchFollower.State p rate.eta :=
                        { old with status := ActiveRoundActions.FollowerStatus.unoccupied }
                      have hcanonicalPrepared :
                          ((ReferenceAssignmentPayloadChronology.actualRunRecordAt active
                            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                            rewards s cIndex hspanCurrentNext seed.activeAtStart).output.preparation.followers.followers i).configuration =
                          .ordinary choiceState memory := by
                        rw [hcanonicalRecord]
                        simpa only [ReferenceActivePhysicalStep.liveInput, choiceState] using hprepared
                      have hseedConfig : active.followers i =
                          .ordinary (seed.followers i) (seed.memory i) := by
                        change (ReferenceFirstLaunchNumericalCell.launchState
                          rate source rewards C_star C_h hcSource).followers i = _
                        exact seed.configuration i
                      have hseedValid :
                          ActiveFollowerLifecycle.localBufferValid (seed.followers i) :=
                        seed.bufferValid i
                      have hseedPair : (seed.followers i).buffer.Pairwise
                          (fun a b => a.calendarRound < b.calendarRound) :=
                        seed.chronologicalBuffer i
                      have hseedStamps : ∀ saved ∈ (seed.followers i).buffer,
                          saved.calendarRound ≤ s := by
                        simpa only [s, ReferenceCompletePhysicalHistory.physicalStart,
                          ReferenceCompletePhysicalHistory.generatedBoundary,
                          ReferenceCompletePhysicalHistory.generatedInput] using seed.bufferStamps i
                      have hrunLogging := ReferenceFollowerBufferProvenance.run_logging_ne_error
                        i active source.1.2
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
                        s cIndex hspanCurrentNext seed.activeAtStart (seed.followers i)
                        (seed.memory i) hseedConfig hseedValid hseedPair hseedStamps
                        choiceState memory hcanonicalPrepared (by rfl)
                      rcases hrunLogging.1 with ⟨loggedRun, hrunInput, hrunBuffer, _⟩
                      have hrunInput' : (cut.output.followers i).downInput = some loggedRun := by
                        rw [← hcanonicalRecord]
                        exact hrunInput
                      have hloggedRunEq : loggedRun = logged :=
                        Option.some.inj (hrunInput'.symm.trans hcutInput)
                      have hloggedBuffer : logged.buffer =
                          ReferenceFollowerBufferProvenance.bufferFold i (seed.followers i).buffer
                            (R.take cIndex) ++
                            ReferenceFollowerBufferProvenance.logEmission i cut := by
                        change loggedRun.buffer =
                          ReferenceFollowerBufferProvenance.bufferFold i (seed.followers i).buffer
                            (ReferenceActivePhysicalHorizon.run active source.1.2
                              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
                              s cIndex hspanCurrent seed.activeAtStart).records ++
                            ReferenceFollowerBufferProvenance.logEmission i
                              (ReferenceAssignmentPayloadChronology.actualRunRecordAt active
                                source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                                rewards s cIndex hspanCurrentNext seed.activeAtStart) at hrunBuffer
                        rw [hloggedRunEq, hcanonicalRecord, hprefixCurrent] at hrunBuffer
                        exact hrunBuffer
                      have hsourceSelection : ∀ z : Fin X.length,
                          ∃ selectedAt : ReferenceActivePhysicalStep.Selection (X.get z).input,
                            (X.get z).output.preparation.coordinator.selection = some selectedAt ∧
                            selectedAt.view.payload = payload := by
                        intro z
                        rcases hsource.2.1 z with
                          ⟨cell, _, _, hselectedPayloadAt, _, _, _, _, _⟩
                        exact ⟨cell.selected, cell.selection_actual, hselectedPayloadAt⟩
                      have hnoAt : ∀ j : Fin R.length, v ≤ j.val → j.val < cIndex →
                          ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i (R.get j) := by
                        intro j hjlow hjhigh hreset
                        have hz : j.val - v < X.length := by
                          rw [hXeq]
                          simp only [List.length_cons]
                          dsimp [cIndex] at hjhigh
                          omega
                        let z : Fin X.length := ⟨j.val - v, hz⟩
                        obtain ⟨selectedAt, hselectedAt, hselectedPayloadAt⟩ :=
                          hsourceSelection z
                        have hdropBound : z.val < (R.drop v).length := by
                          rw [List.length_drop]
                          dsimp [z]
                          omega
                        have hrecordElem : X[z.val]'z.isLt = R[j.val]'j.isLt := by
                          change ((R.drop v).take (1 + tail.length))[z.val]'_ = R[j.val]'_
                          have hindex : v + z.val = j.val := by
                            dsimp only [z]
                            omega
                          simpa only [hindex] using
                            (getElem_drop_take_eq R v (1 + tail.length) z.val
                              (by dsimp only [z]; omega) (by omega))
                        have hrecordEq : X.get z = R.get j := by
                          simpa only [List.get_eq_getElem] using hrecordElem
                        have hsourceDownView :
                            (X.get z).output.preparation.coordinator.downView =
                              some selectedAt.view := by
                          change ((X.get z).output.preparation.coordinator.selection).map
                            ReferenceActivePhysicalStep.Selection.view = some selectedAt.view
                          rw [hselectedAt]
                          rfl
                        have hdownView :
                            (R.get j).output.preparation.coordinator.downView =
                              some selectedAt.view := by
                          have hdownEq := congrArg
                            (fun record : ReferenceActivePhysicalHorizon.RoundRecord
                              (p := p) (rate := rate) =>
                                record.output.preparation.coordinator.downView) hrecordEq
                          rw [← hdownEq]
                          exact hsourceDownView
                        obtain ⟨resetCut, hresetDown, resetBefore, resetAfter, resetRaw,
                          resetMsg, resetScan, resetRegisters, resetLastService,
                          hresetAccepted⟩ := hreset
                        obtain ⟨resetChoice, resetMemory, resetLogged, hresetPrepared,
                          hresetStatus, hresetLogging, hresetInput, hresetCut⟩ :=
                          ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice
                            (R.get j) i resetCut hresetDown
                        have hresetRef :
                            (ReferenceDownReception.referenceDownCut p
                              (R.get j).output.preparation.coordinator.downView
                              ((R.get j).output.preparation.followers.followers i).follower
                              ((R.get j).output.preparation.followers.followers i).row
                              ((R.get j).output.preparation.followers.followers i).time
                              ((R.get j).output.preparation.feedback.observations
                                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate resetLogged).outcome =
                              .accepted resetBefore resetAfter resetRaw resetMsg resetScan
                                resetRegisters resetLastService := by
                          rw [← hresetCut]
                          exact hresetAccepted
                        have hbeforeEq := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_before_eq
                          (R.get j).output.preparation.coordinator.downView
                          ((R.get j).output.preparation.followers.followers i).follower
                          ((R.get j).output.preparation.followers.followers i).row
                          ((R.get j).output.preparation.followers.followers i).time
                          ((R.get j).output.preparation.feedback.observations
                            (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                          resetLogged resetBefore resetAfter resetRaw resetMsg resetScan
                          resetRegisters resetLastService hresetRef
                        subst resetBefore
                        have hresetIndex := (R.get j).output.preparation.follower_alignment i |>.2.1
                        have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields
                          selectedAt.view ((R.get j).output.preparation.followers.followers i).follower
                          ((R.get j).output.preparation.followers.followers i).row
                          ((R.get j).output.preparation.followers.followers i).time
                          ((R.get j).output.preparation.feedback.observations
                            (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                          resetLogged resetLogged resetAfter resetRaw resetMsg resetScan
                          resetRegisters resetLastService (by
                            rw [← hdownView]
                            exact hresetRef)
                        have hresetMsgSigma : resetMsg.val.sigma =
                            selectedAt.view.payload.sigma.val + 1 := by
                          rw [hfields.1, hresetIndex, selectedAt.view.payload.downRecord_fields i]
                        have hresetPayloadSigma : selectedAt.view.payload.sigma.val =
                            payload.sigma.val := by
                          exact congrArg (fun q => q.sigma.val) hselectedPayloadAt
                        have hresetSigma : resetMsg.val.sigma =
                            (payload.downRecord i).val.sigma := by
                          rw [hresetMsgSigma, hresetPayloadSigma, payload.downRecord_fields i]
                        have hinputAtN : (R[cIndex]'hcurrentIndex).input.state.followers i =
                            .ordinary old memory := by
                          have hcurrentGetElem : R[cIndex]'hcurrentIndex = cut := by
                            simpa only [List.get_eq_getElem] using hcurrentGet
                          rw [hcurrentGetElem]
                          exact hinput
                        have hprefixConnected :=
                          ReferenceFollowerReplyChronology.connected_take_to_input
                            hconnected cIndex hcurrentIndex
                        have hjTake : j.val < (R.take cIndex).length := by
                          rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hcurrentIndex)]
                          exact hjhigh
                        obtain ⟨next, nextMemory, hnext, hnextBound⟩ :=
                          ReferenceFollowerReplyChronology.connected_output_chronology
                            hprefixConnected i old memory hinputAtN j.val hjTake
                        have hnextRecord : (R.get j).output.next.followers i =
                            .ordinary next nextMemory := by
                          have htake := List.getElem_take' j.isLt hjhigh
                          rw [← htake] at hnext
                          simpa only [List.get_eq_getElem] using hnext
                        have happlied : ReferenceFollowerReplyChronology.appliedDown
                            (R.get j) i resetMsg.val.sigma :=
                          ⟨resetLogged, resetCut, resetAfter, resetRaw, resetMsg, resetScan,
                            resetRegisters, resetLastService, hresetInput, hresetDown,
                            hresetAccepted, rfl⟩
                        obtain ⟨_, _, _, hresetStrict, hresetStart⟩ :=
                          ReferenceFollowerReplyChronology.record_appliedDown_strict
                            (R.get j) i resetMsg.val.sigma happlied next nextMemory hnextRecord
                        have hresetStartCurrent : resetMsg.val.sigma ≤
                            ReferencePrelaunchFollower.acceptedStart old := by
                          rw [← hresetStart]
                          exact hnextBound
                        omega
                      have hbusyToOldAux : ∀ d n (hn : n < tail.length),
                          tail.length - n = d →
                          ∀ state currentMemory,
                            ((tail.get ⟨n, hn⟩).output.preparation.followers.followers i).configuration =
                              .ordinary state currentMemory →
                            state.status ≠ ActiveRoundActions.FollowerStatus.unoccupied →
                            old.status ≠ ActiveRoundActions.FollowerStatus.unoccupied := by
                        intro d
                        induction d using Nat.strong_induction_on with
                        | h d ih =>
                            intro n hn hdist state currentMemory hconfiguration hbusy
                            let k : Fin tail.length := ⟨n, hn⟩
                            let r := tail.get k
                            rcases hboundary k with
                              ⟨hindex, _, _, _, selectedAt, hselectedAt, hpayloadAt,
                                _, _, _, hfollowersBoundary⟩
                            rcases hfollowersBoundary i with
                              ⟨stateAt, memoryAt, nextAt, nextMemoryAt, hinputAt,
                                _, _, _, _, _, _, _, _, _, _, _, hpreparedAt, houtputAt,
                                _, _, _, _, _, _, _, _, hpreserveAt⟩
                            have hstateEq : state = stateAt := by
                              have heq := hconfiguration.symm.trans hpreparedAt
                              simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq] at heq
                              exact heq.1
                            have hbusyAt : stateAt.status ≠
                                ActiveRoundActions.FollowerStatus.unoccupied := by
                              rw [← hstateEq]
                              exact hbusy
                            have hnextBusy : nextAt.status ≠
                                ActiveRoundActions.FollowerStatus.unoccupied := hpreserveAt hbusyAt
                            have htailOption :=
                              ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R v k
                            have hrBound : v + 1 + n < R.length :=
                              (List.getElem?_eq_some_iff.mp htailOption).1
                            have hrEq : R.get ⟨v + 1 + n, hrBound⟩ = r :=
                              (List.getElem?_eq_some_iff.mp htailOption).2
                            have hnNext : n + 1 ≤ tail.length := by omega
                            have hsuccessorIndex : v + 2 + n < R.length := by omega
                            have hconnBound : v + 1 + n + 1 < R.length := by omega
                            have hadj := connected_successor_state hconnected (v + 1 + n) hconnBound
                            have hrElem : R[v + 1 + n]'hrBound = r := by
                              simpa only [List.get_eq_getElem] using hrEq
                            have hnextRecord :
                                (R.get ⟨v + 2 + n, hsuccessorIndex⟩).input.state = r.output.next := by
                              have hnextElem :
                                  (R[v + 1 + n + 1]'hconnBound).input.state = r.output.next := by
                                change (R[v + 1 + n + 1]'hconnBound).input.state =
                                  (R[v + 1 + n]'hrBound).output.next at hadj
                                rw [hrElem] at hadj
                                exact hadj
                              have hindexEq : v + 2 + n = v + 1 + n + 1 := by omega
                              have hfinNext : (⟨v + 2 + n, hsuccessorIndex⟩ : Fin R.length) =
                                  ⟨v + 1 + n + 1, hconnBound⟩ := by
                                exact Fin.ext hindexEq
                              simpa only [List.get_eq_getElem, hfinNext] using hnextElem
                            have hcurrentStatus :
                                (R.get ⟨v + 2 + n, hsuccessorIndex⟩).input.state.followers i =
                                  .ordinary nextAt nextMemoryAt := by
                              calc
                                _ = r.output.next.followers i :=
                                  congrArg (fun state => state.followers i) hnextRecord
                                _ = (r.output.followers i).configuration :=
                                  outputFollower_matches_next r i
                                _ = .ordinary nextAt nextMemoryAt := houtputAt
                            by_cases hlast : n + 1 = tail.length
                            · have hindexCut : v + 2 + n = cIndex := by
                                simp only [cIndex]
                                omega
                              have hfinCut : (⟨v + 2 + n, hsuccessorIndex⟩ : Fin R.length) =
                                  ⟨cIndex, hcurrentIndex⟩ := Fin.ext hindexCut
                              have hcutStatus : cut.input.state.followers i =
                                  .ordinary nextAt nextMemoryAt := by
                                rw [hfinCut, hcurrentGet] at hcurrentStatus
                                exact hcurrentStatus
                              have hcurrentEq : old = nextAt := by
                                have hstate := hinput.symm.trans hcutStatus
                                simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq] at hstate
                                exact hstate.1
                              rw [hcurrentEq]
                              exact hnextBusy
                            · have hnNext : n + 1 < tail.length := by omega
                              have hdistNext : tail.length - (n + 1) < d := by omega
                              let kNext : Fin tail.length := ⟨n + 1, hnNext⟩
                              let rNext := tail.get kNext
                              have htailNext :=
                                ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R v kNext
                              have hindexEq : v + 1 + kNext.val = v + 2 + n := by
                                dsimp only [kNext]
                                omega
                              have htailNext' := htailNext
                              rw [hindexEq] at htailNext'
                              have hrNextBound : v + 2 + n < R.length :=
                                (List.getElem?_eq_some_iff.mp htailNext').1
                              have hrNextEq : R.get ⟨v + 2 + n, hrNextBound⟩ = rNext := by
                                exact (List.getElem?_eq_some_iff.mp htailNext').2
                              have hinputNext : rNext.input.state.followers i =
                                  .ordinary nextAt nextMemoryAt := by
                                calc
                                  rNext.input.state.followers i =
                                      (R.get ⟨v + 2 + n, hrNextBound⟩).input.state.followers i := by
                                        rw [hrNextEq]
                                  _ = .ordinary nextAt nextMemoryAt := hcurrentStatus
                              rcases hboundary kNext with
                                ⟨_, _, _, _, _, _, _, _, _, _, hfollowersNext⟩
                              rcases hfollowersNext i with
                                ⟨stateNext, memoryNext, _, _, hinputNextBoundary,
                                  _, _, _, _, _, _, _, _, _, _, _, hpreparedNext, _, _,
                                  _, _, _, _, _, _, _, _⟩
                              have hstateNext : stateNext = nextAt := by
                                have heq := hinputNextBoundary.symm.trans hinputNext
                                simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq] at heq
                                exact heq.1
                              have hconfigurationNext :
                                  (rNext.output.preparation.followers.followers i).configuration =
                                    .ordinary stateNext memoryNext := hpreparedNext
                              apply ih (tail.length - (n + 1)) hdistNext (n + 1) hnNext
                                (by omega) stateNext memoryNext hconfigurationNext
                              rw [hstateNext]
                              exact hnextBusy
                      have hstatusX : ∀ j : Fin X.length, ∀ state memory,
                          ((X.get j).output.preparation.followers.followers i).configuration =
                            .ordinary state memory →
                          state.status = ActiveRoundActions.FollowerStatus.unoccupied := by
                        intro j state memory hconfiguration
                        rcases j with ⟨jval, hjval⟩
                        let jFin : Fin X.length := ⟨jval, hjval⟩
                        change ((X.get jFin).output.preparation.followers.followers i).configuration =
                          .ordinary state memory at hconfiguration
                        by_cases hjZero : jval = 0
                        · have hfirst : X.get jFin = birth := by
                            have hfirstOption : X[jval]? = some birth := by
                              rw [hXeq]
                              simp [hjZero]
                            have hfirstElem := (List.getElem?_eq_some_iff.mp hfirstOption).2
                            simpa only [List.get_eq_getElem] using hfirstElem
                          obtain ⟨stateBirth, memoryBirth, hprepBirth, hstatusBirth⟩ :=
                            hstatusBirth i
                          have hconfigurationBirth :
                              (birth.output.preparation.followers.followers i).configuration =
                                .ordinary state memory := by
                            rw [← hfirst]
                            exact hconfiguration
                          have heq := hconfigurationBirth.symm.trans hprepBirth
                          simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq] at heq
                          rw [heq.1]
                          exact hstatusBirth
                        · have hn : jval - 1 < tail.length := by
                            have hj : jval < 1 + tail.length := by
                              simpa only [hXlen] using hjval
                            omega
                          let k : Fin tail.length := ⟨jval - 1, hn⟩
                          have hXRecord : X.get jFin = tail.get k := by
                            have hindex : jval = k.val + 1 := by
                              dsimp only [k]
                              omega
                            have hoption : X[jval]? = some (tail.get k) := by
                              rw [hXeq, hindex]
                              simp only [List.getElem?_cons_succ]
                              rw [List.getElem?_eq_getElem k.isLt]
                              simp only [List.get_eq_getElem]
                            have hgetElem := (List.getElem?_eq_some_iff.mp hoption).2
                            simpa only [List.get_eq_getElem] using hgetElem
                          have hbusyToOld := hbusyToOldAux (tail.length - k.val) k.val k.isLt rfl
                          have hstatusState :
                              ((tail.get k).output.preparation.followers.followers i).configuration =
                                .ordinary state memory := by
                            rw [← hXRecord]
                            exact hconfiguration
                          by_contra hnot
                          have holdBusy := hbusyToOld state memory hstatusState hnot
                          exact (holdBusy holdUnoccupied).elim
                      have hnoX : ∀ j : Fin X.length,
                          ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i (X.get j) := by
                        intro j hreset
                        have hlt : j.val < 1 + tail.length := by
                          simpa only [hXlen] using j.isLt
                        have hjBound : v + j.val < R.length := by
                          omega
                        let jR : Fin R.length := ⟨v + j.val, hjBound⟩
                        have hXRecord : X.get j = R.get jR := by
                          have hElem : X[j.val]'j.isLt = R[v + j.val]'hjBound := by
                            change ((R.drop v).take (1 + tail.length))[j.val]'_ = _
                            exact getElem_drop_take_eq R v (1 + tail.length)
                              j.val (by exact hlt) hjBound
                          simpa only [List.get_eq_getElem] using hElem
                        rw [hXRecord] at hreset
                        have hjRlow : v ≤ jR.val := by simp [jR]
                        have hjRhigh : jR.val < cIndex := by
                          change v + j.val < cIndex
                          calc
                            v + j.val < v + (1 + tail.length) :=
                              Nat.add_lt_add_left hlt v
                            _ = cIndex := by simp only [cIndex, Nat.add_assoc]
                        exact hnoAt jR hjRlow hjRhigh hreset
                      have hslice : (R.drop v).take (cIndex - v) = X := by
                        have hdropLength : cIndex - v = 1 + tail.length := by
                          simp only [cIndex]
                          omega
                        simp only [X, hdropLength]
                      have hsplitTake :
                          R.take cIndex = R.take v ++ (R.drop v).take (cIndex - v) := by
                        have htakeIndex : cIndex = v + (cIndex - v) := by omega
                        rw [htakeIndex, List.take_add]
                        simp only [Nat.add_sub_cancel_left]
                      have htakeAll : R.take (cIndex + 1) = R.take cIndex ++ [cut] := by
                        rw [List.take_succ_eq_append_getElem hcurrentIndex]
                        rw [hcurrentGetElem]
                      have hintervalResetFree :
                          ∀ record ∈ (R.drop v).take (cIndex - v),
                            ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i record := by
                        intro record hrecord hreset
                        have hrecordX : record ∈ X := by
                          rw [← hslice]
                          exact hrecord
                        obtain ⟨q, hq, hrecordEq⟩ := List.mem_iff_getElem.mp hrecordX
                        let j : Fin X.length := ⟨q, hq⟩
                        have hgetEq : X.get j = record := by
                          simpa only [List.get_eq_getElem] using hrecordEq
                        rw [← hgetEq] at hreset
                        exact hnoX j hreset
                      let prefixFold := ReferenceFollowerBufferProvenance.bufferFold i
                        (seed.followers i).buffer (R.take v)
                      have hfoldSplit :
                          ReferenceFollowerBufferProvenance.bufferFold i
                            (seed.followers i).buffer (R.take cIndex) =
                            prefixFold ++
                              ((R.drop v).take (cIndex - v)).flatMap
                                (ReferenceFollowerBufferProvenance.logEmission i) := by
                        calc
                          ReferenceFollowerBufferProvenance.bufferFold i
                              (seed.followers i).buffer (R.take cIndex) =
                            ReferenceFollowerBufferProvenance.bufferFold i
                              (seed.followers i).buffer
                              (R.take v ++ (R.drop v).take (cIndex - v)) := by rw [hsplitTake]
                          _ = ReferenceFollowerBufferProvenance.bufferFold i
                                (ReferenceFollowerBufferProvenance.bufferFold i
                                  (seed.followers i).buffer (R.take v))
                                ((R.drop v).take (cIndex - v)) := by
                                  simp [ReferenceFollowerBufferProvenance.bufferFold,
                                    List.foldl_append]
                          _ = prefixFold ++
                                ((R.drop v).take (cIndex - v)).flatMap
                                  (ReferenceFollowerBufferProvenance.logEmission i) :=
                            ReferenceFollowerSparseEmissionRecovery.bufferFold_eq_seed_append_emissions_of_no_reset
                                i prefixFold ((R.drop v).take (cIndex - v)) hintervalResetFree
                      have hprefixFoldBound : ∀ saved ∈ prefixFold,
                          saved.calendarRound ≤ s + v := by
                        have hsafety := ReferenceFollowerBufferProvenance.run_bufferFold_safety i
                          (seed.followers i) active source.1.2
                          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
                          s v hspanV seed.activeAtStart hseedValid hseedPair hseedStamps
                        have hsafety' := hsafety.2.2
                        rw [hprefixV] at hsafety'
                        intro saved hsaved
                        exact hsafety' saved hsaved
                      have hprefixBufferZero (date : ℕ)
                          (hdate : (payload.downRecord i).val.sigma ≤ date) :
                          SparseCalendarReplay.sparseBufferContribution (p.m - 1)
                            (ConstructorDimensions.D p : ℝ) rate.eta.val
                            (payload.downRecord i).val.h
                            (PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i))
                            date prefixFold = 0 := by
                        apply ReferenceFollowerSparseEmissionRecovery.sparseBufferContribution_zero_of_no_matching_round
                        intro saved hsaved heq
                        have hstamp := hprefixFoldBound saved hsaved
                        rw [hmsgSigma] at hdate
                        omega
                      have hpreEmissionZero (date : ℕ)
                          (hdate : (payload.downRecord i).val.sigma ≤ date) :
                          SparseCalendarReplay.sparseBufferContribution (p.m - 1)
                            (ConstructorDimensions.D p : ℝ) rate.eta.val
                            (payload.downRecord i).val.h
                            (PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i))
                            date ((R.take v).flatMap
                              (ReferenceFollowerBufferProvenance.logEmission i)) = 0 := by
                        apply ReferenceFollowerSparseEmissionRecovery.emissionFlatMapContribution_zero_of_source_round_ne
                        intro record hrecord
                        obtain ⟨q, hq, hrecordEq⟩ := List.mem_iff_getElem.mp hrecord
                        have hqBound : q < v := by
                          simp only [List.length_take] at hq
                          omega
                        have hqR : q < R.length := by omega
                        have hrecordTime : record.input.time.val = s + q := by
                          have htake : (R.take v)[q]'hq = R[q]'hqR :=
                            (List.getElem_take' hqR hqBound).symm
                          rw [← hrecordEq, htake]
                          simpa only [List.get_eq_getElem] using htimeAt ⟨q, hqR⟩
                        rw [hmsgSigma] at hdate
                        omega
                      have hflatDecomposition :
                          (R.take (cIndex + 1)).flatMap
                              (ReferenceFollowerBufferProvenance.logEmission i) =
                            (R.take v).flatMap (ReferenceFollowerBufferProvenance.logEmission i) ++
                              ((R.drop v).take (cIndex - v)).flatMap
                                (ReferenceFollowerBufferProvenance.logEmission i) ++
                              ReferenceFollowerBufferProvenance.logEmission i cut := by
                        rw [htakeAll, hsplitTake, List.flatMap_append, List.flatMap_append]
                        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
                      have hbufferFlat (date : ℕ)
                          (hdate : (payload.downRecord i).val.sigma ≤ date) :
                          ActiveFollowerDownAcceptance.bufferArrivalAt p rate
                              (payload.downRecord i) logged date =
                            SparseCalendarReplay.sparseBufferContribution (p.m - 1)
                              (ConstructorDimensions.D p : ℝ) rate.eta.val
                              (payload.downRecord i).val.h
                              (PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i))
                              date ((R.take (cIndex + 1)).flatMap
                                (ReferenceFollowerBufferProvenance.logEmission i)) := by
                        change SparseCalendarReplay.sparseBufferContribution (p.m - 1)
                            (ConstructorDimensions.D p : ℝ) rate.eta.val
                            (payload.downRecord i).val.h
                            (PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i))
                            date logged.buffer = _
                        rw [hloggedBuffer, hfoldSplit]
                        calc
                          SparseCalendarReplay.sparseBufferContribution (p.m - 1)
                              (ConstructorDimensions.D p : ℝ) rate.eta.val
                              (payload.downRecord i).val.h
                              (PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i)) date
                              ((prefixFold ++ ((R.drop v).take (cIndex - v)).flatMap
                                (ReferenceFollowerBufferProvenance.logEmission i)) ++
                                ReferenceFollowerBufferProvenance.logEmission i cut) =
                            SparseCalendarReplay.sparseBufferContribution (p.m - 1)
                              (ConstructorDimensions.D p : ℝ) rate.eta.val
                              (payload.downRecord i).val.h
                              (PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i)) date
                              (((R.take v).flatMap (ReferenceFollowerBufferProvenance.logEmission i) ++
                                ((R.drop v).take (cIndex - v)).flatMap
                                  (ReferenceFollowerBufferProvenance.logEmission i)) ++
                                ReferenceFollowerBufferProvenance.logEmission i cut) := by
                                  rw [SparseCalendarReplay.sparseBufferContribution_append,
                                    SparseCalendarReplay.sparseBufferContribution_append,
                                    SparseCalendarReplay.sparseBufferContribution_append,
                                    SparseCalendarReplay.sparseBufferContribution_append,
                                    hprefixBufferZero date hdate,
                                    hpreEmissionZero date hdate]
                          _ = SparseCalendarReplay.sparseBufferContribution (p.m - 1)
                              (ConstructorDimensions.D p : ℝ) rate.eta.val
                              (payload.downRecord i).val.h
                              (PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i)) date
                              ((R.take (cIndex + 1)).flatMap
                                (ReferenceFollowerBufferProvenance.logEmission i)) := by
                                  rw [hflatDecomposition]
                      have hbufferSum (date : ℕ)
                          (hdate : (payload.downRecord i).val.sigma ≤ date) :
                          ActiveFollowerDownAcceptance.bufferArrivalAt p rate
                              (payload.downRecord i) logged date =
                            ((R.take (cIndex + 1)).map (fun x =>
                              SparseCalendarReplay.sparseBufferContribution (p.m - 1)
                                (ConstructorDimensions.D p : ℝ) rate.eta.val
                                (payload.downRecord i).val.h
                                (PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i))
                                date (ReferenceFollowerBufferProvenance.logEmission i x))).sum := by
                        calc
                          ActiveFollowerDownAcceptance.bufferArrivalAt p rate
                              (payload.downRecord i) logged date =
                            SparseCalendarReplay.sparseBufferContribution (p.m - 1)
                              (ConstructorDimensions.D p : ℝ) rate.eta.val
                              (payload.downRecord i).val.h
                              (PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i))
                              date ((R.take (cIndex + 1)).flatMap
                                (ReferenceFollowerBufferProvenance.logEmission i)) :=
                                  hbufferFlat date hdate
                          _ = ((R.take (cIndex + 1)).map (fun x =>
                              SparseCalendarReplay.sparseBufferContribution (p.m - 1)
                                (ConstructorDimensions.D p : ℝ) rate.eta.val
                                (payload.downRecord i).val.h
                                (PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i))
                                date (ReferenceFollowerBufferProvenance.logEmission i x))).sum :=
                                  sparseBufferContribution_flatMap_sum
                                    (payload.downRecord i) i date (R.take (cIndex + 1))
                      refine ⟨rfl, hcutInput, hscanEndpoint, ?_, hnoX, hstatusX, ?_⟩
                      · exact hendpointL
                      · intro j
                        let date := (payload.downRecord i).val.sigma + j.val
                        have hjX : j.val < 1 + tail.length := by
                          have hj : j.val < X.length := j.isLt
                          exact lt_of_lt_of_eq hj hXlen
                        have hrecordIndex : v + j.val < R.length := by
                          dsimp [cIndex] at hcurrentIndex ⊢
                          omega
                        let jR : Fin R.length := ⟨v + j.val, hrecordIndex⟩
                        have hrecordX : X.get j = R.get jR := by
                          have hElem : X[j.val]'j.isLt = R[v + j.val]'hrecordIndex := by
                            change ((R.drop v).take (1 + tail.length))[j.val]'_ = _
                            simp only [List.getElem_take, List.getElem_drop]
                          simpa only [List.get_eq_getElem] using hElem
                        have htimeDate : (X.get j).input.time.val + 1 = date := by
                          rw [hrecordX, htimeAt]
                          dsimp [date, jR]
                          rw [hmsgSigma]
                          omega
                        have hdateLower : (payload.downRecord i).val.sigma ≤ date := by
                          dsimp [date]
                          omega
                        have hdateUpper : date <
                            (payload.downRecord i).val.sigma + L := by
                          dsimp [date, L]
                          omega
                        have hendpoint : date < cut.input.time.val + 1 := by
                          rw [hendpointL]
                          exact hdateUpper
                        have hdateEq : s + (v + j.val) + 1 = date := by
                          dsimp [date]
                          rw [hmsgSigma]
                          omega
                        let d := date - s - 1
                        have hdEq : d = v + j.val := by
                          dsimp [d]
                          omega
                        have hdlt : d < (R.take (cIndex + 1)).length := by
                          simp only [List.length_take]
                          dsimp [d, cIndex]
                          omega
                        have htimesAll : ∀ q (hq : q < (R.take (cIndex + 1)).length),
                            ((R.take (cIndex + 1))[q]'hq).input.time.val = s + q := by
                          intro q hq
                          have hqTake : q < cIndex + 1 := by
                            simp only [List.length_take] at hq
                            omega
                          have hqR : q < R.length := by omega
                          rw [List.getElem_take]
                          exact htimeAt ⟨q, hqR⟩
                        have hcontribution :=
                          ReferenceFollowerSparseEmissionRecovery.emissionFlatMapContribution_getElem
                            (payload.downRecord i) i s (R.take (cIndex + 1)) d hdlt htimesAll
                        have hdateD : s + d + 1 = date := by
                          rw [hdEq]
                          exact hdateEq
                        rw [hdateD] at hcontribution
                        have hgetTake :
                            (R.take (cIndex + 1)).get ⟨d, hdlt⟩ = X.get j := by
                          have hdIndex : d = v + j.val := hdEq
                          have htakeR :
                              (R.take (cIndex + 1)).get ⟨d, hdlt⟩ = R.get jR := by
                            simp only [List.get_eq_getElem, List.getElem_take, hdIndex]
                            rfl
                          exact htakeR.trans hrecordX.symm
                        have hbufferEmission :
                            ActiveFollowerDownAcceptance.bufferArrivalAt p rate
                                (payload.downRecord i) logged date =
                              ReferenceFollowerSparseEmissionRecovery.emissionContribution
                                (payload.downRecord i) i (X.get j) := by
                          calc
                            ActiveFollowerDownAcceptance.bufferArrivalAt p rate
                                (payload.downRecord i) logged date =
                              SparseCalendarReplay.sparseBufferContribution (p.m - 1)
                                (ConstructorDimensions.D p : ℝ) rate.eta.val
                                (payload.downRecord i).val.h
                                (PrelaunchBufferRecovery.downArm rate.eta
                                  (payload.downRecord i)) date
                                ((R.take (cIndex + 1)).flatMap
                                  (ReferenceFollowerBufferProvenance.logEmission i)) :=
                                    hbufferFlat date hdateLower
                            _ = ReferenceFollowerSparseEmissionRecovery.emissionContribution
                                  (payload.downRecord i) i
                                  ((R.take (cIndex + 1)).get ⟨d, hdlt⟩) := hcontribution
                            _ = ReferenceFollowerSparseEmissionRecovery.emissionContribution
                                  (payload.downRecord i) i (X.get j) := by rw [hgetTake]
                        exact ⟨htimeDate, hbufferEmission⟩

end Bandits.Support.ReferenceFirstReplacementCutoffAcceptedSparseEmissions

end
