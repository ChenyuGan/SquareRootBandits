/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionDatedSparseEmissions
public import Bandits.Support.ReferenceFirstReplacementCutoffCurrentNumericalOutputs

import Lean.Elab.Tactic.Omega

/-!
# Delayed numerical replay during first replacement collection

The actual accepted DOWN diagnostics in the original post-cutoff collection
window replay the same enabled numerical stream as the first replacement
cutoff.  The dated sparse-emission API remains the physical source of every
arrival, including enabled dates with zero arrival.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceFirstReplacementLiveFollowerPrefix
open ReferenceLaterLiveNumericalReadout
open ReferenceFirstWindowNumericalStream
open ReferenceFollowerSparseEmissionRecovery
open ActiveFollowerDownAcceptance
open RecordedQueueRun
open QueueReplay
open PublicDiscreteDraws
open DeclaredFollowerLocalRound
open ReferencePrelaunchFollower
open ActiveFollowerLifecycle

namespace Bandits.Support.ReferenceFirstReplacementCollectionDelayedNumericalReplay

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem get_drop_take_eq {α : Type} (records : List α) (start count index : ℕ)
    (hspan : start + count ≤ records.length) (hindex : index < count) :
    ((records.drop start).take count).get
        ⟨index, by simp [List.length_take, List.length_drop]; omega⟩ =
      records.get ⟨start + index, by omega⟩ := by
  have hdrop : index < (records.drop start).length := by
    simp [List.length_drop]
    omega
  simp only [List.get_eq_getElem]
  rw [(List.getElem_take' hdrop hindex).symm]
  simp only [List.getElem_drop]

private theorem sourceCell_state_eq
    {record other : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (cell : ActualLiveSourceCell record) (hrecord : record = other)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared : (other.output.preparation.followers.followers i).configuration =
      .ordinary state memory) :
    cell.states i = state := by
  cases hrecord
  have hstates := (cell.ordinary i).symm.trans hprepared
  exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hstates).1

/-- An accepted delayed DOWN during the first replacement collection replays
the original sparse emissions as numerical arrivals, including zero dates.
All selectors, physical records, local inputs, and final local operations are
the ones from the actual run. -/
theorem complete_first_replacement_collection_delayed_numerical_replay
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
        let X := (R.drop v).take (1 + tail.length)
        let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
        let L := X.length
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            C.length = L ∧ X = birth :: tail ∧ 1 ≤ L ∧
            (∀ j : Fin W.length,
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
                | .accepted before after _raw M scan registers lastService =>
                  let a := payload.assignment.assigned i
                  let A := fun b => (C.take b).map (fun z =>
                    (true, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) z a))
                  let Q := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q) (A b)
                  M = payload.downRecord i ∧
                  (r.output.followers i).downInput = some before ∧
                  diag = ReferenceDownReception.referenceDownCut p
                    r.output.preparation.coordinator.downView i r.input.row r.input.time
                    (r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate before ∧
                  scan.endpoint = u ∧
                  (∀ k : Fin R.length, v ≤ k.val → k.val < N →
                    ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i (R.get k)) ∧
                  (∀ k : Fin R.length, M.val.sigma ≤ (R.get k).input.time.val + 1 →
                    (R.get k).input.time.val + 1 < u →
                    ∃ state : ReferencePrelaunchFollower.State p rate.eta,
                      ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
                        ((R.get k).output.preparation.followers.followers i).configuration =
                          .ordinary state memory ∧ state.status = .unoccupied) ∧
                  (∀ date : ℕ, M.val.sigma ≤ date → date < u →
                    ∃ k : Fin R.length,
                      k.val = date - s - 1 ∧
                      (R.get k).input.time.val + 1 = date ∧
                      ActiveFollowerDownAcceptance.bufferArrivalAt p rate M before date =
                        ReferenceFollowerSparseEmissionRecovery.emissionContribution M i
                          (R.get k)) ∧
                  ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M before u =
                    ((R.drop v).take (u - M.val.sigma)).map
                      (fun record => (true,
                        ReferenceFollowerSparseEmissionRecovery.emissionContribution M i record)) ∧
                  u = M.val.sigma + L ∧
                  ActiveFollowerDownAcceptance.recoveryRounds p rate M u =
                    X.map (fun x => x.input.time.val + 1) ∧
                  X.map (fun x => x.input.time.val + 1) =
                    (List.range L).map (M.val.sigma + ·) ∧
                  ActiveFollowerDownAcceptance.recoveryArrivals p rate M before u =
                    C.map (fun z => RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) z a) ∧
                  ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M before u = A L ∧
                  (∀ b : ℕ,
                    (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M before u).take b =
                      A b) ∧
                  registers = Q L ∧
                  lastService = (Q L).1 - (Q (L - 1)).1 ∧
                  after.lastDown = some M ∧
                  (after.S, after.backlog) = Q L ∧
                  after.delta = lastService ∧
                  after.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
                  after.buffer = [] ∧
                  (∃ old memory,
                    r.input.state.followers i = .ordinary old memory ∧
                    (r.output.followers i).configuration = .ordinary after memory ∧
                    (r.output.followers i).failure = none ∧
                    DeclaredFollowerLocalRound.releaseAndFinish rate i r.input.row r.input.time
                      (r.output.preparation.feedback.observations
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                      old memory after = .ok (after, memory) ∧
                    after.initializationFailure = old.initializationFailure) ∧
                  (∃ recovered : ActiveFollowerDownAcceptance.ReplayRegisters,
                    ActiveFollowerDownAcceptance.checkedRecovery p rate M before u =
                      .ok recovered ∧
                    recovered.registers = registers ∧ recovered.lastService = lastService ∧
                    ∀ b : ℕ, ∃ middle,
                      ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
                        (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩ (A b) = .ok middle ∧
                      ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p)
                        middle ∧ middle.registers = Q b)
                | _ => True)
          | _ => True
      | _ => True := by
  classical
  have hD :=
    ReferenceFirstReplacementCollectionDatedSparseEmissions.complete_first_replacement_collection_dated_sparse_emissions
      rate source rewards C_star C_h
  have hCut :=
    ReferenceFirstReplacementCutoffCurrentNumericalOutputs.complete_first_replacement_cutoff_current_numerical_outputs
      rate source rewards C_star C_h
  have hSource :=
    ReferenceFirstReplacementNumericalSourceRecovery.complete_first_replacement_numerical_source_stream
      rate source rewards C_star C_h
  have hBoundary :=
    ReferenceFirstReplacementFollowerBoundary.complete_first_replacement_follower_boundary
      rate source rewards C_star C_h
  have hBirth :=
    ReferenceFirstReplacementDownRecovery.complete_first_replacement_down_recovery_and_finish
      rate source rewards C_star C_h
  have hPrefix :=
    ReferenceFirstReplacementCollectionPrefix.complete_first_replacement_collection_follower_prefix
      rate source rewards C_star C_h
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  dsimp only [PublicDiscreteDraws.followerCount, ActiveRoundActions.Follower]
    at hD hCut hSource hBoundary hBirth hPrefix ⊢
  cases hBirthGet : R[v]? with
  | none => trivial
  | some birth =>
    have hBirthGetNorm :
        R[((ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length +
          (ReferenceCollectionPhaseHistory.collectionWindow R
            (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length)]? =
          some birth := by
      simpa only [v, w] using hBirthGet
    simp only [hBirthGetNorm] at hD hCut hSource hBoundary hBirth hPrefix ⊢
    cases hBirthCoordinator : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hBirthCoordinator] at hD hCut hSource hBoundary hBirth hPrefix ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed birthArm
      let payload := installed.registers.payload
      cases hCutGet : R[c]? with
      | none => trivial
      | some cut =>
        have hCutGetNorm :
            R[((ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length +
              (ReferenceCollectionPhaseHistory.collectionWindow R
                (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length + 1 +
              (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R
                ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length +
                  (ReferenceCollectionPhaseHistory.collectionWindow R
                    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length)).length)]? =
              some cut := by
          simpa only [c, v, tail, w] using hCutGet
        simp only [hCutGetNorm] at hD hCut hSource hBoundary hBirth hPrefix ⊢
        cases hCutCoordinator : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live _ _ _ cutoffOutcome =>
          simp only [hCutCoordinator] at hD hCut hSource hBoundary hBirth hPrefix ⊢
          cases cutoffOutcome <;> try trivial
          rename_i cutoffResult
          let u := cut.input.time.val + 1
          let X := (R.drop v).take (1 + tail.length)
          let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
          let L := X.length
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          rcases hCut with ⟨hClength, hX, hLpositive, hCutRest⟩
          have hXlocal : X = birth :: tail := by
            simpa only [X, v, tail, w] using hX
          rcases hCutRest with ⟨_hNotLater, hCutRest⟩
          rcases hCutRest with ⟨hInstalled, hCutTime, hCutTimeSource,
            hCutRows, hCutSelected, hCutRewards, hPayloadSigma, hSourceStart, hCutRest⟩
          rcases hSource with ⟨hSourceLength, hCells, _hSourceTail⟩
          change C.length = L ∧ X = birth :: tail ∧ 1 ≤ L ∧ _
          refine ⟨hClength, hX, hLpositive, ?_⟩
          intro j
          let r := W.get j
          let N := c + 1 + j.val
          have hDAt := hD j
          rcases hDAt with ⟨hRecord, hTime, hTimeW, hRows, hSelected, hRewards, hDowns⟩
          refine ⟨hRecord, hTime, hTimeW, hRows, hSelected, hRewards, ?_⟩
          intro i
          cases hDown : (W.get j).output.followers i |>.down with
          | none => trivial
          | some diag =>
            cases hOutcome : diag.outcome with
            | skipped _ _ => simp only [hOutcome]
            | inputFailure _ _ => simp only [hOutcome]
            | decodeOrParseRejected _ _ _ => simp only [hOutcome]
            | parsedButUnaccepted _ _ _ _ => simp only [hOutcome]
            | outputFailure _ _ => simp only [hOutcome]
            | accepted before after raw M scan registers lastService =>
              simp only [hOutcome]
              have hDBranch := hDowns i
              have hDownNorm := by simpa only [W] using hDown
              rw [hDownNorm] at hDBranch
              simp only [hOutcome] at hDBranch
              rcases hDBranch with ⟨hMessage, hDownInput, hDiagnostic, hScan,
                hNoReset, hUnoccupied, hDates, hEmissionRecords⟩
              have hBirthBranch := hBirth
              rcases hBirthBranch with ⟨_, hBirthFollowers⟩
              have hPrefixBranch := hPrefix
              rcases hPrefixBranch with
                ⟨_, _, _, _, _, _, hPrefixFollowers⟩
              rcases hPrefixFollowers i with
                ⟨_, _, oldCut, initial, memory, hCutInput, hCutOutput,
                  hCutFailure, hEZero, hInitialUnoccupied, _, _, _, _, _, _, _, _,
                  hPrefixStates, hPrefixSteps, _⟩
              have hPrefixStep := hPrefixSteps j.val j.isLt
              rcases hPrefixStep with ⟨_, hPrefixExists⟩
              rcases hPrefixExists with
                ⟨state, logged, post, hInputState, hStateUnoccupied,
                  _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                  _, _, _, _, hRecordResult, hRecordDownInput, hRecordDown,
                  _, _, hRelease, hActualFollowerOutput, hConsume, hPostUnoccupied,
                  _, _, _, hPostInitializationFailure, _, _, _, _, _, _,
                  hPrefixBranches, _⟩
              have hOutputInput := congrArg
                (fun observed : ReferenceActivePhysicalStep.FollowerObservation p rate =>
                  observed.downInput) hActualFollowerOutput
              have hLoggedEq : logged = before :=
                Option.some.inj (hOutputInput.symm.trans hDownInput)
              have hPrefixDiagEq :
                  ReferenceDownReception.referenceDownCut p
                    r.output.preparation.coordinator.downView i r.input.row r.input.time
                    (r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged = diag := by
                rw [hLoggedEq, hDiagnostic.symm]
              have hOutcomeLogged := hOutcome
              rw [← hLoggedEq] at hOutcomeLogged
              have hPrefixOutcome :
                  (ReferenceDownReception.referenceDownCut p
                    r.output.preparation.coordinator.downView i r.input.row r.input.time
                    (r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).outcome =
                    .accepted logged after raw M scan registers lastService := by
                rw [hPrefixDiagEq]
                rw [hOutcomeLogged]
              have hPostEq : post = after := by
                have hconsume := hConsume
                rw [hPrefixOutcome, DeclaredFollowerLocalRound.consumeDownResult_accepted]
                  at hconsume
                injection hconsume with hEq
                exact hEq.symm
              have hActualConfig :
                  (r.output.followers i).configuration = .ordinary after memory := by
                have h := congrArg
                  (fun observed : ReferenceActivePhysicalStep.FollowerObservation p rate =>
                    observed.configuration) hActualFollowerOutput
                rw [hPostEq] at h
                simpa [r] using h
              have hActualFailure : (r.output.followers i).failure = none := by
                have h := congrArg
                  (fun observed : ReferenceActivePhysicalStep.FollowerObservation p rate =>
                    observed.failure) hActualFollowerOutput
                simpa [r, hPostEq] using h
              have hActualRelease :
                  DeclaredFollowerLocalRound.releaseAndFinish rate i r.input.row r.input.time
                    (r.output.preparation.feedback.observations
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                    state memory after = .ok (after, memory) := by
                simpa [r, hPostEq] using hRelease
              have hActualInitializationFailure :
                  after.initializationFailure = state.initializationFailure := by
                simpa [hPostEq] using hPostInitializationFailure

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
              have hv : v < R.length := (List.getElem?_eq_some_iff.mp hBirthGet).1
              have hc : c < R.length := (List.getElem?_eq_some_iff.mp hCutGet).1
              have hBirthIndex : R.get ⟨v, hv⟩ = birth := by
                apply Option.some.inj
                exact (List.getElem?_eq_some_iff.mpr ⟨hv, by rfl⟩).symm.trans hBirthGet
              have hBirthTime : birth.input.time.val = s + v := by
                rw [← hBirthIndex]
                exact htimeAt ⟨v, hv⟩
              have hLlen : 1 + tail.length = L := by
                have hxlen := congrArg List.length hXlocal
                simp only [List.length_cons] at hxlen
                change 1 + tail.length = X.length
                omega
              have hMsigma : M.val.sigma = s + v + 1 := by
                calc
                  M.val.sigma = (payload.downRecord i).val.sigma :=
                    congrArg (fun x : OrdinaryMessageCodec.DownRecord
                      (ReferencePrelaunchFollower.codecParams p rate.eta) => x.val.sigma)
                      hMessage
                  _ = s + v + 1 := by
                    rw [payload.downRecord_fields i, hPayloadSigma, hBirthTime]
              have hU : u = M.val.sigma + L := by
                have hcutTimeLocal : cut.input.time.val =
                    birth.input.time.val + 1 + tail.length := hCutTime
                change cut.input.time.val + 1 = M.val.sigma + L
                rw [hcutTimeLocal, hBirthTime, hMsigma, ← hLlen]
                omega
              have hspan : v + (1 + tail.length) ≤ R.length := by
                have hcutIndex : v + 1 + tail.length < R.length := hc
                omega
              have hindexBound : ∀ q : ℕ, q < L → v + q < R.length := by
                intro q hq
                omega
              have hLpos : 1 ≤ L := by
                change 1 ≤ X.length
                rw [hXlocal]
                simp only [List.length_cons]
                omega
              have hcurrentIndex : ∀ (q : ℕ) (hq : q < L),
                  X.get ⟨q, hq⟩ = R.get ⟨v + q, hindexBound q hq⟩ := by
                intro q hq
                have hget := get_drop_take_eq R v (1 + tail.length) q hspan
                  (by rwa [hLlen])
                exact hget
              have hXdates : X.map (fun x => x.input.time.val + 1) =
                  (List.range L).map (M.val.sigma + ·) := by
                apply List.ext_getElem
                · simp only [List.length_map, List.length_range]
                  rfl
                · intro q hqX hqRange
                  simp only [List.getElem_map, List.getElem_range]
                  have hget := hcurrentIndex q (by simpa only [List.length_map] using hqX)
                  have hdate := htimeAt ⟨v + q, hindexBound q
                    (by simpa only [List.length_map] using hqX)⟩
                  simp only [List.get_eq_getElem] at hget hdate
                  rw [hget, hdate, hMsigma]
                  omega

              have hEmissionMap :
                  X.map (fun record => (true,
                    ReferenceFollowerSparseEmissionRecovery.emissionContribution M i record)) =
                  C.map (fun z => (true,
                    RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) z
                      (payload.assignment.assigned i))) := by
                apply List.ext_getElem
                · simp only [List.length_map]
                  rw [hSourceLength]
                · intro q hqX hqC
                  simp only [List.getElem_map]
                  have hq : q < X.length := by
                    simpa only [List.length_map] using hqX
                  let idx : Fin X.length := ⟨q, hq⟩
                  obtain ⟨cell, hCellIndex, _hread, hCellPayload, _, _, _, _, _⟩ := hCells idx
                  have hCbound : q < C.length := by
                    simpa only [List.length_map] using hqC
                  have hCvalue : C[q]'hCbound = cell.input := by
                    apply Option.some.inj
                    exact (List.getElem?_eq_getElem hCbound).symm.trans hCellIndex
                  have hfields : ∀ k,
                      (cell.states k).status ≠ ActiveRoundActions.FollowerStatus.unoccupied →
                      (cell.states k).lastDown =
                        some (cell.selected.view.payload.downRecord k) := by
                    intro k hkBusy
                    by_cases hqzero : q = 0
                    ·
                        have hXBirthOpt : X[q]? = some birth := by
                          rw [hXlocal]
                          simp [hqzero]
                        have hXBirth : X.get idx = birth := by
                          apply Option.some.inj
                          have hget := (List.getElem?_eq_getElem hq).symm
                          exact hget.trans hXBirthOpt
                        have hBirthFollower := hBirthFollowers k
                        rcases hBirthFollower with
                          ⟨oldBirth, memoryBirth, loggedBirth, hBirthInput,
                            hBirthUnoccupied, hBirthPrepared, hBirthLogging, _⟩
                        have hstatesEq := sourceCell_state_eq cell hXBirth k
                          oldBirth memoryBirth hBirthPrepared
                        exact (hkBusy (hstatesEq ▸ hBirthUnoccupied)).elim
                    ·
                        have hqTail : q - 1 < tail.length := by
                          have hqL : q < L := by simpa [L] using hq
                          omega
                        let kTail : Fin tail.length := ⟨q - 1, hqTail⟩
                        have htailStep := hBoundary kTail
                        rcases htailStep with
                          ⟨_, _, _, _, selected, hselected, hselectedPayload, _, _, _,
                            hfollowers⟩
                        rcases hfollowers k with
                          ⟨stateTail, memoryTail, nextTail, nextMemoryTail,
                            hinputTail, hdomainTail, hmassTail, hzeroTail,
                            hstrictTail, hbusyTail, hpairTail, hbeforeTail,
                            hsigmaTail, hstartTail, hcreditTail, hdecisionTail,
                            hpreparedTail, _⟩
                        have hXtailOpt : X[q]? = some (tail.get kTail) := by
                          rw [hXlocal]
                          calc
                            (birth :: tail)[q]? = tail[q - 1]? := by
                              conv_lhs => rw [show q = (q - 1) + 1 by omega]
                              rw [List.getElem?_cons_succ]
                            _ = some (tail.get kTail) := List.getElem?_eq_getElem hqTail
                        have hXtail : X.get idx = tail.get kTail := by
                          apply Option.some.inj
                          have hget := (List.getElem?_eq_getElem hq).symm
                          exact hget.trans hXtailOpt
                        have hstatesEq := sourceCell_state_eq cell hXtail k
                          stateTail memoryTail hpreparedTail
                        have hbusyState : stateTail.status ≠
                            ActiveRoundActions.FollowerStatus.unoccupied := by
                          rw [← hstatesEq]
                          exact hkBusy
                        rw [hstatesEq, hCellPayload]
                        exact (hbusyTail hbusyState).1
                  have hUnoccupiedCell :
                      (cell.states i).status = ActiveRoundActions.FollowerStatus.unoccupied := by
                    have hqL : q < L := by
                      simpa only [List.length_map, L] using hqX
                    have hindex := hcurrentIndex q hqL
                    let k : Fin R.length := ⟨v + q, hindexBound q hqL⟩
                    have hdate : (R.get k).input.time.val + 1 = M.val.sigma + q := by
                      rw [htimeAt k, hMsigma]
                      simp only [k]
                      omega
                    have hpre : M.val.sigma ≤ (R.get k).input.time.val + 1 := by
                      rw [hdate]
                      omega
                    have hpost : (R.get k).input.time.val + 1 < u := by
                      rw [hdate, hU]
                      omega
                    obtain ⟨dateState, dateMemory, hprepared, hdateUnoccupied⟩ :=
                      hUnoccupied k hpre hpost
                    have hstatesEq := sourceCell_state_eq cell hindex i
                      dateState dateMemory hprepared
                    rw [hstatesEq]
                    exact hdateUnoccupied
                  have hquantized :=
                    ReferenceFirstLiveUnoccupiedEmission.emissionContribution_eq_quantizedArrival
                      (X.get idx) cell hfields i hUnoccupiedCell
                  rw [hCellPayload] at hquantized
                  have hquantized' :
                      ReferenceFollowerSparseEmissionRecovery.emissionContribution M i
                        (X.get idx) =
                      RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                        (C[q]'hCbound) (payload.assignment.assigned i) := by
                    rw [hCvalue, hMessage]
                    exact hquantized
                  change (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution
                    M i (X.get idx)) = (true, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                      (C[q]'hCbound) (payload.assignment.assigned i))
                  exact congrArg (fun n : ℕ => (true, n)) hquantized'
              let A := fun b => (C.take b).map (fun z =>
                (true, RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) z
                  (payload.assignment.assigned i)))
              let Q := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q) (A b)
              have hPhysicalX : (R.drop v).take (u - M.val.sigma) = X := by
                rw [hU]
                simp only [Nat.add_sub_cancel_left]
                simp only [X, hLlen]
              have hFullQueue :
                  ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M before u = A L := by
                calc
                  _ = ((R.drop v).take (u - M.val.sigma)).map (fun record =>
                      (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution M i record)) :=
                    hEmissionRecords
                  _ = X.map (fun record => (true,
                      ReferenceFollowerSparseEmissionRecovery.emissionContribution M i record)) := by
                    rw [hPhysicalX]
                  _ = C.map (fun z => (true,
                      RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) z
                        (payload.assignment.assigned i))) := hEmissionMap
                  _ = A L := by
                    dsimp only [A]
                    rw [List.take_of_length_le (le_of_eq hClength)]
              have hAFull : A L = C.map (fun z =>
                  (true, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) z
                    (payload.assignment.assigned i))) := by
                dsimp only [A]
                rw [List.take_of_length_le (le_of_eq hClength)]
              have hQueueTake : ∀ b : ℕ,
                  (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M before u).take b =
                    A b := by
                intro b
                rw [hFullQueue, hAFull]
                simp only [A, List.map_take]
              have hArrivals :
                  ActiveFollowerDownAcceptance.recoveryArrivals p rate M before u =
                    C.map (fun z => RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) z
                      (payload.assignment.assigned i)) := by
                apply (Function.Injective.list_map
                  (f := fun n : ℕ => (true, n)) (by intro x y h; exact congrArg Prod.snd h))
                calc
                  (ActiveFollowerDownAcceptance.recoveryArrivals p rate M before u).map
                      (fun n => (true, n)) =
                      ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M before u := rfl
                  _ = A L := hFullQueue
                  _ = C.map (fun z => (true,
                        RecordedQueueRun.quantizedArrival
                          (ReferenceFirstLaunchNumericalCell.queueParameters rate) z
                          (payload.assignment.assigned i))) := hAFull
                  _ = (C.map (fun z => RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) z
                        (payload.assignment.assigned i))).map (fun n => (true, n)) := by
                    simp only [List.map_map, Function.comp_def]
              have hRounds :
                  ActiveFollowerDownAcceptance.recoveryRounds p rate M u =
                    X.map (fun x => x.input.time.val + 1) := by
                calc
                  ActiveFollowerDownAcceptance.recoveryRounds p rate M u =
                    (List.range L).map (M.val.sigma + ·) := by
                      change SparseCalendarReplay.sparseCalendarRounds M.val.sigma u = _
                      unfold SparseCalendarReplay.sparseCalendarRounds
                      rw [hU, Nat.add_sub_cancel_left]
                  _ = X.map (fun x => x.input.time.val + 1) := hXdates.symm
              have hCheckedTransition :=
                ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
                  (W.get j) i before diag after raw M scan registers lastService
                  hDownInput hDown hOutcome
              have hAlignment := r.output.preparation.follower_alignment i
              rw [hAlignment.1, hAlignment.2.1, hAlignment.2.2.1] at hCheckedTransition
              rcases ActiveFollowerDownAcceptance.downTransition_accepted_checked p i
                  r.input.row r.input.time
                  (r.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                  rate before after raw M scan registers lastService hCheckedTransition with
                ⟨_, hCheckedRecovery, _, _hEndpointBound, _, _, hAfterEquation⟩
              rw [hScan] at hCheckedRecovery
              have hCheckedReplay :
                  ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
                    (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩ (A L) =
                      .ok ⟨registers, lastService⟩ := by
                rw [ActiveFollowerDownAcceptance.checkedRecovery_eq_checkedReplay] at hCheckedRecovery
                rw [hFullQueue] at hCheckedRecovery
                exact hCheckedRecovery
              have hQueueSuccess :=
                ActiveFollowerDownAcceptance.checkedReplay_success (D p) (p.T * D p)
                  (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩ ⟨registers, lastService⟩ (A L)
                  hCheckedReplay
              have hRegistersQ : registers = Q L := by
                simpa only [Q, A] using hQueueSuccess.2.1
              have hAlength : (A L).length = L := by
                rw [hAFull, List.length_map]
                exact hClength
              have hLminus : L - 1 + 1 = L := Nat.sub_add_cancel hLpos
              have hCheckedLast :
                  ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
                    (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩ ((A L).take L) =
                      .ok ⟨registers, lastService⟩ := by
                simpa only [List.take_of_length_le (by rw [hAlength])] using hCheckedReplay
              have hLastPackage :=
                ReferenceFirstReplacementAcceptedTailNumericalReplay.checkedReplay_take_last_service
                  (4 * rate.n) (D p) (p.T * D p) (0, M.val.q) (A L) (L - 1)
                  (by rw [hAlength]; omega) ⟨registers, lastService⟩
                  (by simpa only [hLminus] using hCheckedLast)
              have hATake (b : ℕ) : (A L).take b = A b := by
                rw [hAFull]
                simp only [A, List.map_take]
              simp only [hLminus, hATake] at hLastPackage
              have hLastService :
                  lastService = (Q L).1 - (Q (L - 1)).1 := by
                exact hLastPackage.2.1
              have hActualAfter :
                  after.lastDown = some M ∧ (after.S, after.backlog) = Q L ∧
                  after.delta = lastService ∧ after.status = .unoccupied ∧
                  after.buffer = [] := by
                have hstatus : scan.endpoint ≠ r.input.time.val + 2 := by
                  rw [hScan, hTimeW]
                  omega
                rw [hAfterEquation]
                simp only [hstatus, ↓reduceIte]
                exact ⟨True.intro, hRegistersQ, True.intro, True.intro, True.intro⟩
              refine ⟨hMessage, hDownInput, hDiagnostic, hScan, hNoReset,
                hUnoccupied, hDates, hEmissionRecords, hU, hRounds, hXdates,
                hArrivals, hFullQueue, hQueueTake, hRegistersQ, hLastService,
                hActualAfter.1, hActualAfter.2.1, hActualAfter.2.2.1,
                hActualAfter.2.2.2.1, hActualAfter.2.2.2.2,
                ⟨state, memory, hInputState, hActualConfig, hActualFailure,
                  hActualRelease, hActualInitializationFailure⟩,
                ⟨⟨registers, lastService⟩, hCheckedRecovery, rfl, rfl, ?_⟩⟩
              intro b
              obtain ⟨middle, hmiddle, hdomain, hmiddleRegisters⟩ := hLastPackage.2.2 b
              refine ⟨middle, ?_, hdomain, ?_⟩
              · exact hmiddle
              · exact hmiddleRegisters

end Bandits.Support.ReferenceFirstReplacementCollectionDelayedNumericalReplay

end
