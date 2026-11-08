/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionEmissionGeometry

import Lean.Elab.Tactic.Omega

/-!
# Dated sparse emissions during first replacement collection

Sources: `sources/zip4/manuscript/06_interruptions.tex:193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

For each actual accepted DOWN in the post-cutoff collection window, this
retains the admitted actual geometry and identifies every dated sparse
arrival and the complete enabled queue-record list. The launch buffer and
all earlier resets remain in the carried prefix.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower ActiveFollowerLifecycle ActiveFollowerDownAcceptance
open ReferenceDownReception SparseCalendarReplay PublicDiscreteDraws
open ReferenceFollowerBufferProvenance ReferenceFollowerReplyChronology
open ReferenceFollowerSparseEmissionRecovery
open ReferenceFirstReplacementCollectionSeedEndpoint
open ReferenceFirstReplacementCollectionDispatchOrigin
open ReferenceFirstReplacementCollectionPrefix
open ReferenceFirstReplacementLiveFollowerPrefix
open ReferenceFirstReplacementFollowerBoundary
open ReferenceFirstReplacementCutoffPreparedBoundary
open ReferenceFirstReplacementDownRecovery
open ReferenceFirstReplacementNextFollowerStep

namespace Bandits.Support.ReferenceFirstReplacementCollectionDatedSparseEmissions

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

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
  rw [hsplit, List.take_append_of_le_length (by simp [hlen])]
  simp [hlen]

/-- The actual first replacement collection has dated sparse-arrival and
ordered queue-record recovery, while preserving all witnesses from the
actual emission-geometry result. -/
theorem complete_first_replacement_collection_dated_sparse_emissions
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
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
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            ∀ j : Fin W.length,
              let r := W.get j
              let N := c + 1 + j.val
              R[N]? = some r ∧
              r.input.time.val = s + N ∧
              r.input.time.val = u + j.val ∧
              r.input.rows = source.1.2 ∧
              r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
              r.input.rewards = rewards ∧
              ∀ i : Fin (p.m - 1),
              match (r.output.followers i).down with
              | none => True
              | some diag =>
                match diag.outcome with
                | .accepted before _after _raw msg scan _registers _lastService =>
                  msg = payload.downRecord i ∧
                  (r.output.followers i).downInput = some before ∧
                  diag = ReferenceDownReception.referenceDownCut p
                    r.output.preparation.coordinator.downView i r.input.row r.input.time
                    (r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate before ∧
                  scan.endpoint = u ∧
                  (∀ k : Fin R.length, v ≤ k.val → k.val < N →
                    ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i (R.get k)) ∧
                  (∀ k : Fin R.length, msg.val.sigma ≤ (R.get k).input.time.val + 1 →
                    (R.get k).input.time.val + 1 < u →
                    ∃ state : ReferencePrelaunchFollower.State p rate.eta,
                      ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
                        ((R.get k).output.preparation.followers.followers i).configuration =
                          .ordinary state memory ∧ state.status = .unoccupied) ∧
                  (∀ date : ℕ, msg.val.sigma ≤ date → date < u →
                    ∃ k : Fin R.length,
                      k.val = date - s - 1 ∧
                      (R.get k).input.time.val + 1 = date ∧
                      ActiveFollowerDownAcceptance.bufferArrivalAt p rate msg before date =
                        ReferenceFollowerSparseEmissionRecovery.emissionContribution msg i (R.get k)) ∧
                  ActiveFollowerDownAcceptance.recoveryQueueRecords p rate msg before u =
                    ((R.drop v).take (u - msg.val.sigma)).map
                      (fun record =>
                        (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution
                          msg i record))
                | _ => True
          | _ => True
      | _ => True := by
  classical
  have hgeometry :=
    ReferenceFirstReplacementCollectionEmissionGeometry.complete_first_replacement_collection_emission_geometry
      rate source rewards C_star C_h
  dsimp only at hgeometry ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hbirthGet : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hbirthGet] at hgeometry ⊢
    cases hbirthCoord : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirthCoord] at hgeometry
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent clockData installed birthArm
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hgeometry ⊢
      let payload := installed.registers.payload
      cases hcutGet : R[c]? with
      | none => trivial
      | some cut =>
        simp only [hcutGet] at hgeometry ⊢
        cases hcutCoord : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcutCoord] at hgeometry
          cases outcome <;> try trivial
          rename_i cutoffResult
          dsimp only [ReferenceActivePhysicalStep.liveInput] at hgeometry ⊢
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          intro j
          let r := W.get j
          let N := c + 1 + j.val
          have hgeometryAt := hgeometry j
          rcases hgeometryAt with
            ⟨hrecordSome, htime, htimeWindow, hrows, hselected, hrewards, hfollowers⟩
          refine ⟨hrecordSome, htime, htimeWindow, hrows, hselected, hrewards, ?_⟩
          intro i
          cases hdown : (W.get j).output.followers i |>.down with
          | none => trivial
          | some diag =>
            cases houtcome : diag.outcome with
            | skipped _ _ => simp only [houtcome] at ⊢
            | inputFailure _ _ => simp only [houtcome] at ⊢
            | decodeOrParseRejected _ _ _ => simp only [houtcome] at ⊢
            | parsedButUnaccepted _ _ _ _ => simp only [houtcome] at ⊢
            | outputFailure _ _ => simp only [houtcome] at ⊢
            | accepted before after raw msg scan registers lastService =>
              simp only [houtcome] at ⊢
              have hbranch := hfollowers i
              simp only [W, hdown, houtcome] at hbranch
              rcases hbranch with
                ⟨hmsg, hinput, hdiag, hscanEndpoint, hgeometryNoReset,
                  hgeometryUnoccupied⟩
              have hv : v < R.length := (List.getElem?_eq_some_iff.mp hbirthGet).1
              have hc : c < R.length := (List.getElem?_eq_some_iff.mp hcutGet).1
              have hcutIndex : R.get ⟨c, hc⟩ = cut := by
                apply Option.some.inj
                exact (List.getElem?_eq_some_iff.mpr ⟨hc, by rfl⟩).symm.trans hcutGet
              have hbirthIndex : R.get ⟨v, hv⟩ = birth := by
                apply Option.some.inj
                exact (List.getElem?_eq_some_iff.mpr ⟨hv, by rfl⟩).symm.trans hbirthGet
              have htimeAt : ∀ k : Fin R.length,
                  (R.get k).input.time.val = s + k.val := by
                intro k
                obtain ⟨_, _, hactual⟩ :=
                  ReferenceLaterLiveNumericalReadout.source_record_prefix
                    rate rewards C_star C_h source k
                have htime := congrArg
                  (fun x : ReferenceActivePhysicalHorizon.RoundRecord
                    (p := p) (rate := rate) => x.input.time.val) hactual
                simpa [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
                  ReferenceActivePhysicalHorizon.roundInputAt] using htime
              have hsourceDateUnique : ∀ k₁ k₂ : Fin R.length,
                  (R.get k₁).input.time.val + 1 = (R.get k₂).input.time.val + 1 →
                    k₁ = k₂ := by
                intro k₁ k₂ hdate
                apply Fin.ext
                rw [htimeAt k₁, htimeAt k₂] at hdate
                omega
              have hRlen : R.length = p.T - s := by
                simpa [R, s] using
                  ReferenceCompletePhysicalHistory.completeSuffixRecords_length
                    rate source rewards C_star C_h
              have hcutTime : cut.input.time.val = s + c := by
                rw [← hcutIndex]
                exact htimeAt ⟨c, hc⟩
              have hbirthTime : birth.input.time.val = s + v := by
                rw [← hbirthIndex]
                exact htimeAt ⟨v, hv⟩
              have hbirthProvenance :=
                ReferenceLaterInstallationProvenance.record_laterChosen_birth birth
              rw [hbirthCoord] at hbirthProvenance
              simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth,
                hbirthCoord] at hbirthProvenance
              have hpayloadSigma : payload.sigma.val = birth.input.time.val := by
                simpa only [payload] using hbirthProvenance.2
              have hmsgSigma : msg.val.sigma = s + v + 1 := by
                calc
                  msg.val.sigma = (payload.downRecord i).val.sigma := by
                    calc
                      msg.val.sigma =
                          (installed.registers.payload.downRecord i).val.sigma :=
                        congrArg (fun x : OrdinaryMessageCodec.DownRecord
                          (ReferencePrelaunchFollower.codecParams p rate.eta) => x.val.sigma) hmsg
                      _ = (payload.downRecord i).val.sigma := by rfl
                  _ = s + v + 1 := by
                    rw [payload.downRecord_fields i, hpayloadSigma, hbirthTime]
              have hcutoffSelected : msg.val.sigma < u := by
                have hdiagAccepted := houtcome
                have hlogged :=
                  ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice
                    r i diag hdown
                rcases hlogged with ⟨choice, memory, logged, hprepared, hstatus,
                  hlogging, hdownInput, hactualDiag⟩
                have hloggedEq : logged = before :=
                  Option.some.inj (hdownInput.symm.trans hinput)
                subst logged
                have hactualAccepted :=
                  ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
                    r i before diag after raw msg scan registers lastService hinput hdown
                    hdiagAccepted
                have hchecked := ActiveFollowerDownAcceptance.downTransition_accepted_checked p
                  (r.output.preparation.followers.followers i).follower
                  (r.output.preparation.followers.followers i).row
                  (r.output.preparation.followers.followers i).time
                  (r.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                  rate before after raw msg scan registers lastService hactualAccepted
                have hinterval : msg.val.sigma < scan.endpoint := hchecked.2.2.1
                simpa [u] using hinterval.trans_eq hscanEndpoint
              have hlaunchSource :=
                ReferenceLaterLiveNumericalReadout.source_record_prefix
                  rate rewards C_star C_h source ⟨v, hv⟩
              obtain ⟨hcSource, hspanBirth, hbirthActual⟩ := hlaunchSource
              have hlaunch' := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
                rate source rewards C_star C_h hcSource
              let active' := ReferenceFirstLaunchNumericalCell.launchState
                rate source rewards C_star C_h hcSource
              let seed' := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
                rate source rewards C_star C_h hcSource
              have hactiveMode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
                rate source rewards C_star C_h active' hlaunch'
              have hcompleteRecords :=
                ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
                  rate source rewards C_star C_h active' hlaunch'
              have htotalSpan : s + (p.T - s) ≤ p.T := by omega
              have hN : N < R.length := (List.getElem?_eq_some_iff.mp hrecordSome).1
              have hcurrentGet : R.get ⟨N, hN⟩ = r :=
                (List.getElem?_eq_some_iff.mp hrecordSome).2
              have hN' : N < p.T - s := by simpa [hRlen] using hN
              have hspanN : s + N ≤ p.T := by omega
              have hspanNNext : s + (N + 1) ≤ p.T := by
                have hN' : N < p.T - s := by simpa [hRlen] using hN
                omega
              have hprefixN :
                  (ReferenceActivePhysicalHorizon.run active' source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s N
                    hspanN seed'.activeAtStart).records = R.take N := by
                calc
                  (ReferenceActivePhysicalHorizon.run active' source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s N
                    hspanN seed'.activeAtStart).records =
                      (ReferenceActivePhysicalHorizon.run active' source.1.2
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                        (p.T - s) htotalSpan hactiveMode).records.take N := by
                          symm
                          exact run_records_take active' source.1.2
                            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
                            s (p.T - s) htotalSpan hactiveMode N (Nat.le_of_lt hN')
                  _ = R.take N := by rw [← hcompleteRecords]
              have hseedConfig : active'.followers i =
                  .ordinary (seed'.followers i) (seed'.memory i) := seed'.configuration i
              have hseedValid : ActiveFollowerLifecycle.localBufferValid (seed'.followers i) :=
                seed'.bufferValid i
              have hseedPair : (seed'.followers i).buffer.Pairwise
                  (fun a b => a.calendarRound < b.calendarRound) := seed'.chronologicalBuffer i
              have hseedStamps : ∀ saved ∈ (seed'.followers i).buffer,
                  saved.calendarRound ≤ s := by
                simpa only [s, ReferenceCompletePhysicalHistory.physicalStart,
                  ReferenceCompletePhysicalHistory.generatedBoundary,
                  ReferenceCompletePhysicalHistory.generatedInput] using seed'.bufferStamps i
              obtain ⟨_, _, hcurrentActual⟩ :=
                ReferenceLaterLiveNumericalReadout.source_record_prefix
                  rate rewards C_star C_h source ⟨N, hN⟩
              have hcurrentRecord :
                  ReferenceAssignmentPayloadChronology.actualRunRecordAt active' source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s N
                    hspanNNext seed'.activeAtStart = r := by
                have hindexed : R.get ⟨N, hN⟩ =
                    ReferenceAssignmentPayloadChronology.actualRunRecordAt active' source.1.2
                      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s N
                      hspanNNext seed'.activeAtStart := by
                  simpa [active', seed'] using hcurrentActual
                exact hindexed.symm.trans hcurrentGet
              obtain ⟨choice, choiceMemory, logged, hprepared, hunoccupied,
                  hlogging, hdownInput, hactualCut⟩ :=
                ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice
                  r i diag hdown
              have hloggedEq : logged = before := Option.some.inj (hdownInput.symm.trans hinput)
              subst logged
              have hcanonicalPrepared :
                  ((ReferenceAssignmentPayloadChronology.actualRunRecordAt active' source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s N
                    hspanNNext seed'.activeAtStart).output.preparation.followers.followers i).configuration =
                    .ordinary choice choiceMemory := hcurrentRecord.symm ▸ hprepared
              have hrunLogging := ReferenceFollowerBufferProvenance.run_logging_ne_error
                i active' source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                rewards s N hspanNNext seed'.activeAtStart (seed'.followers i) (seed'.memory i)
                hseedConfig hseedValid hseedPair hseedStamps choice choiceMemory
                hcanonicalPrepared hunoccupied
              rcases hrunLogging.1 with ⟨loggedRun, hrunInput, hrunBuffer, _⟩
              have hrunInput' : (r.output.followers i).downInput = some loggedRun := by
                rw [← hcurrentRecord]
                exact hrunInput
              have hloggedRunEq : loggedRun = before :=
                Option.some.inj (hrunInput'.symm.trans hinput)
              have hloggedBuffer : before.buffer =
                  ReferenceFollowerBufferProvenance.bufferFold i (seed'.followers i).buffer
                    (R.take N) ++ ReferenceFollowerBufferProvenance.logEmission i r := by
                change loggedRun.buffer =
                  ReferenceFollowerBufferProvenance.bufferFold i (seed'.followers i).buffer
                    (ReferenceActivePhysicalHorizon.run active' source.1.2
                      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s N
                      hspanN seed'.activeAtStart).records ++
                  ReferenceFollowerBufferProvenance.logEmission i
                    (ReferenceAssignmentPayloadChronology.actualRunRecordAt active' source.1.2
                      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s N
                      hspanNNext seed'.activeAtStart) at hrunBuffer
                rw [hloggedRunEq, hcurrentRecord, hprefixN] at hrunBuffer
                exact hrunBuffer
              have hintervalResetFree :
                  ∀ record ∈ (R.drop v).take (N - v),
                    ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i record := by
                intro record hrecord hreset
                obtain ⟨q, hq, hrecordEq⟩ := List.mem_iff_getElem.mp hrecord
                have hqBound : q < N - v := by
                  simp only [List.length_take] at hq
                  omega
                have hjBound : v + q < N := by omega
                have hjR : v + q < R.length := by omega
                let k : Fin R.length := ⟨v + q, hjR⟩
                have hrecordAt : ((R.drop v).take (N - v))[q] = R[k.val] := by
                  simp only [List.getElem_take, List.getElem_drop, k]
                have hrecordEq' : record = R.get k := by
                  calc
                    record = ((R.drop v).take (N - v))[q] := hrecordEq.symm
                    _ = R[k.val] := hrecordAt
                    _ = R.get k := by simp only [List.get_eq_getElem]
                rw [hrecordEq'] at hreset
                exact hgeometryNoReset k (by simp [k]) (by simp [k]; omega) hreset
              have hsplitTake : R.take N = R.take v ++ (R.drop v).take (N - v) := by
                calc
                  R.take N = R.take (v + (N - v)) := by congr 1; omega
                  _ = R.take v ++ (R.drop v).take (N - v) := List.take_add
              let prefixFold := ReferenceFollowerBufferProvenance.bufferFold i
                (seed'.followers i).buffer (R.take v)
              have hfoldSplit :
                  ReferenceFollowerBufferProvenance.bufferFold i (seed'.followers i).buffer
                    (R.take N) =
                  prefixFold ++ ((R.drop v).take (N - v)).flatMap
                    (ReferenceFollowerBufferProvenance.logEmission i) := by
                calc
                  _ = ReferenceFollowerBufferProvenance.bufferFold i
                        (seed'.followers i).buffer
                        (R.take v ++ (R.drop v).take (N - v)) := by rw [hsplitTake]
                  _ = ReferenceFollowerBufferProvenance.bufferFold i prefixFold
                        ((R.drop v).take (N - v)) := by
                          simp [prefixFold, ReferenceFollowerBufferProvenance.bufferFold,
                            List.foldl_append]
                  _ = prefixFold ++ ((R.drop v).take (N - v)).flatMap
                        (ReferenceFollowerBufferProvenance.logEmission i) :=
                    ReferenceFollowerSparseEmissionRecovery.bufferFold_eq_seed_append_emissions_of_no_reset
                      i prefixFold ((R.drop v).take (N - v)) hintervalResetFree
              have hprefixFoldBound : ∀ saved ∈ prefixFold,
                  saved.calendarRound ≤ s + v := by
                have hv' : v < p.T - s := by simpa [hRlen] using hv
                have hsafety := ReferenceFollowerBufferProvenance.run_bufferFold_safety i
                  (seed'.followers i) active' source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
                  s v (by omega) seed'.activeAtStart hseedValid hseedPair hseedStamps
                intro saved hsaved
                have hsafety' := hsafety.2.2
                have hprefixV :
                    (ReferenceActivePhysicalHorizon.run active' source.1.2
                      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s v
                      (by omega) seed'.activeAtStart).records = R.take v := by
                  calc
                    _ = (ReferenceActivePhysicalHorizon.run active' source.1.2
                          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                          (p.T - s) htotalSpan hactiveMode).records.take v := by
                            symm
                            exact run_records_take active' source.1.2
                              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
                              s (p.T - s) htotalSpan hactiveMode v (Nat.le_of_lt hv')
                    _ = R.take v := by rw [← hcompleteRecords]
                rw [hprefixV] at hsafety'
                exact hsafety' saved hsaved
              have hprefixFoldZero (date : ℕ) (hdate : s + v < date) :
                  SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                    rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg)
                    date prefixFold = 0 := by
                apply ReferenceFollowerSparseEmissionRecovery.sparseBufferContribution_zero_of_no_matching_round
                intro saved hsaved heq
                have hstamp := hprefixFoldBound saved hsaved
                omega
              have hpreEmissionZero (date : ℕ) (hdate : s + v < date) :
                  SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                    rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg)
                    date ((R.take v).flatMap (ReferenceFollowerBufferProvenance.logEmission i)) = 0 := by
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
                  exact htimeAt ⟨q, hqR⟩
                omega
              have htakeAll : R.take (N + 1) = R.take N ++ [r] := by
                rw [List.take_succ_eq_append_getElem hN]
                have hcurrentElem : R[N]'hN = r := by
                  apply Option.some.inj
                  exact (List.getElem?_eq_some_iff.mpr ⟨hN, by simp⟩).symm.trans hrecordSome
                rw [hcurrentElem]
              have hallSplit :
                  R.take (N + 1) =
                    R.take v ++ (R.drop v).take (N - v) ++ [r] := by
                rw [htakeAll, hsplitTake]
              have hloggedBuffer' : before.buffer =
                  (prefixFold ++ ((R.drop v).take (N - v)).flatMap
                    (ReferenceFollowerBufferProvenance.logEmission i)) ++
                    ReferenceFollowerBufferProvenance.logEmission i r := by
                rw [hloggedBuffer, hfoldSplit]
              have htimesAll : ∀ (q : ℕ) (hq : q < (R.take (N + 1)).length),
                  ((R.take (N + 1))[q]'hq).input.time.val = s + q := by
                intro q hq
                have hqTake : q < N + 1 := by
                  simp only [List.length_take] at hq
                  omega
                have hqR : q < R.length := by omega
                rw [List.getElem_take]
                exact htimeAt ⟨q, hqR⟩
              have hRlenN : (R.take (N + 1)).length = N + 1 := by
                simp only [List.length_take]
                omega
              have hExtraDate :
                  ∀ date : ℕ, msg.val.sigma ≤ date → date < u →
                    ∃ k : Fin R.length,
                      k.val = date - s - 1 ∧
                      (R.get k).input.time.val + 1 = date ∧
                      ActiveFollowerDownAcceptance.bufferArrivalAt p rate msg before date =
                        ReferenceFollowerSparseEmissionRecovery.emissionContribution msg i (R.get k) := by
                intro date hdateStart hdateStop
                let d := date - s - 1
                have hdLower : v ≤ d := by rw [hmsgSigma] at hdateStart; dsimp [d]; omega
                have hdUpper : d ≤ N := by
                  have hNtime : r.input.time.val = s + N := htime
                  have huTime : u ≤ r.input.time.val := by
                    rw [htimeWindow]
                    omega
                  have huBound : u ≤ s + N := by
                    rw [← hNtime]
                    exact huTime
                  dsimp [d]
                  omega
                have hdltN : d < N + 1 := by omega
                have hdR : d < R.length := by omega
                let k : Fin R.length := ⟨d, hdR⟩
                have hdateEq : s + d + 1 = date := by dsimp [d]; omega
                have hrecordDate : (R.get k).input.time.val + 1 = date := by
                  rw [htimeAt k]
                  exact hdateEq
                have hpreZero := hprefixFoldZero date (by rw [hmsgSigma] at hdateStart; omega)
                have hsourcePrefixZero := hpreEmissionZero date
                  (by rw [hmsgSigma] at hdateStart; omega)
                have hcontribution :=
                  ReferenceFollowerSparseEmissionRecovery.emissionFlatMapContribution_getElem
                    msg i s (R.take (N + 1)) d (by simpa [hRlenN] using hdltN) htimesAll
                have hcontribution' :
                    SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                      rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg)
                      date ((R.take (N + 1)).flatMap
                        (ReferenceFollowerBufferProvenance.logEmission i)) =
                    ReferenceFollowerSparseEmissionRecovery.emissionContribution msg i
                      ((R.take (N + 1)).get ⟨d, by simpa [hRlenN] using hdltN⟩) := by
                  simpa only [hdateEq, List.get_eq_getElem] using hcontribution
                have hgetTake : (R.take (N + 1)).get ⟨d, by simpa [hRlenN] using hdltN⟩ =
                    R.get k := by
                  have htake : (R.take (N + 1))[d]'(by simpa [hRlenN] using hdltN) =
                      R[d]'hdR := (List.getElem_take' hdR hdltN).symm
                  simpa only [List.get_eq_getElem, k] using htake
                have hbufferFlat :
                    ActiveFollowerDownAcceptance.bufferArrivalAt p rate msg before date =
                      SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                        rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg)
                        date ((R.take (N + 1)).flatMap
                        (ReferenceFollowerBufferProvenance.logEmission i)) := (by
                  change SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                    rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg)
                    date before.buffer = _
                  rw [hloggedBuffer']
                  exact calc
                    SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                        rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg)
                        date ((prefixFold ++ ((R.drop v).take (N - v)).flatMap
                          (ReferenceFollowerBufferProvenance.logEmission i)) ++
                          ReferenceFollowerBufferProvenance.logEmission i r) =
                      SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                        rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg)
                        date ((R.take (N + 1)).flatMap
                          (ReferenceFollowerBufferProvenance.logEmission i)) := by
                      rw [hallSplit, List.flatMap_append, List.flatMap_append]
                      simp only [List.flatMap_singleton]
                      rw [SparseCalendarReplay.sparseBufferContribution_append,
                        SparseCalendarReplay.sparseBufferContribution_append,
                        SparseCalendarReplay.sparseBufferContribution_append,
                        SparseCalendarReplay.sparseBufferContribution_append,
                        hpreZero, hsourcePrefixZero])
                apply Exists.intro k
                constructor
                · rfl
                constructor
                · exact hrecordDate
                · exact (Eq.trans hbufferFlat
                    (Eq.trans hcontribution'
                      (congrArg (ReferenceFollowerSparseEmissionRecovery.emissionContribution msg i)
                        hgetTake)))
              refine ⟨hmsg, hinput, hdiag, hscanEndpoint, hgeometryNoReset,
                hgeometryUnoccupied,
                hExtraDate, ?_⟩
              have hcutTime' : cut.input.time.val = s + c := hcutTime
              have hu : u = s + c + 1 := by dsimp [u]; omega
              have hsigma : msg.val.sigma = s + v + 1 := hmsgSigma
              have hcount : u - msg.val.sigma = c - v := by rw [hu, hsigma]; omega
              have hcountBound : u - msg.val.sigma ≤ (R.drop v).length := by
                rw [hcount, List.length_drop, hRlen]
                have hcBound : c ≤ R.length := Nat.le_of_lt hc
                omega
              have hleftLength :
                  (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate msg before u).length =
                    u - msg.val.sigma := by
                simp [ActiveFollowerDownAcceptance.recoveryQueueRecords,
                  ActiveFollowerDownAcceptance.recoveryArrivals,
                  ActiveFollowerDownAcceptance.recoveryRounds,
                  SparseCalendarReplay.sparseCalendarRounds]
              have hrightLength :
                  (((R.drop v).take (u - msg.val.sigma)).map
                    (fun record => (true,
                      ReferenceFollowerSparseEmissionRecovery.emissionContribution msg i record))).length =
                    u - msg.val.sigma := by
                simp [List.length_map, List.length_take]
                omega
              apply List.ext_getElem
              · rw [hleftLength, hrightLength]
              · intro q hqLeft hqRight
                have hq : q < u - msg.val.sigma := by rw [← hleftLength]; exact hqLeft
                have hleft :
                    (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate msg before u)[q]'hqLeft =
                      (true, ActiveFollowerDownAcceptance.bufferArrivalAt p rate msg before
                        (msg.val.sigma + q)) := by
                  simp [ActiveFollowerDownAcceptance.recoveryQueueRecords,
                    ActiveFollowerDownAcceptance.recoveryArrivals,
                    ActiveFollowerDownAcceptance.recoveryRounds,
                    SparseCalendarReplay.sparseCalendarRounds,
                    List.getElem_map, List.getElem_range]
                have hright :
                    (((R.drop v).take (u - msg.val.sigma)).map
                      (fun record => (true,
                        ReferenceFollowerSparseEmissionRecovery.emissionContribution msg i record)))[q]'hqRight =
                      (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution msg i
                        (((R.drop v).take (u - msg.val.sigma))[q]'(by simpa using hqRight))) := by
                  simp only [List.getElem_map]
                have hqueueDate : msg.val.sigma + q < u := by omega
                obtain ⟨k, hkFormula, hkDate, harrival⟩ :=
                  hExtraDate (msg.val.sigma + q) (by omega) hqueueDate
                rw [hsigma] at hkFormula
                have hkVal : k.val = v + q := by omega
                have hindex : v + q < R.length := by rw [← hkVal]; exact k.isLt
                let k' : Fin R.length := ⟨v + q, hindex⟩
                have hk' : (R.get k').input.time.val + 1 = msg.val.sigma + q := by
                  rw [htimeAt k', hsigma]
                  simp only [k']
                  omega
                have hkEq : k = k' := hsourceDateUnique k k' (hkDate.trans hk'.symm)
                have hindexVal : k.val = v + q := congrArg Fin.val hkEq
                have htakeIndex :
                    ((R.drop v).take (u - msg.val.sigma))[q]'(by simpa using hqRight) = R.get k := by
                  have hqTake : q < (R.drop v).length := lt_of_lt_of_le hq hcountBound
                  have htake : ((R.drop v).take (u - msg.val.sigma))[q]'(by simpa using hqRight) =
                      (R.drop v)[q]'hqTake := (List.getElem_take' hqTake hq).symm
                  have hdrop : (R.drop v)[q]'hqTake = R[v + q]'hindex := by
                    simp only [List.getElem_drop]
                  calc
                    _ = (R.drop v)[q]'hqTake := htake
                    _ = R[v + q]'hindex := hdrop
                    _ = R.get k := by
                      rw [hkEq]
                      simp [k']
                calc
                  (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate msg before u)[q]'hqLeft =
                      (true, ActiveFollowerDownAcceptance.bufferArrivalAt p rate msg before
                        (msg.val.sigma + q)) := hleft
                  _ = (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution msg i
                        (((R.drop v).take (u - msg.val.sigma))[q]'(by simpa using hqRight))) := by
                    rw [harrival, ← htakeIndex]
                  _ = (((R.drop v).take (u - msg.val.sigma)).map
                        (fun record => (true,
                          ReferenceFollowerSparseEmissionRecovery.emissionContribution msg i record)))[q]'hqRight :=
                      hright.symm

end Bandits.Support.ReferenceFirstReplacementCollectionDatedSparseEmissions

end
