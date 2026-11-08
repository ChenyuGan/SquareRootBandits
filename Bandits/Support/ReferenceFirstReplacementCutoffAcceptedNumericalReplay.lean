/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCutoffAcceptedSparseEmissions

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeDrop

/-!
# Numerical replay at the first accepted replacement cutoff

Sources: `sources/zip4/manuscript/06_interruptions.tex:193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This internal result identifies the actual accepted cutoff recovery with the
replay of every original enabled date from the transmitted DOWN queue. It
preserves the checked operation and each checked prefix, including zero
arrivals, and identifies the actual post-finish local state and memory.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ActiveFollowerDownAcceptance
open ReferenceFirstReplacementLiveFollowerPrefix
open ReferenceLaterLiveNumericalReadout
open ReferenceFirstWindowNumericalStream
open ReferencePrelaunchFollower
open ReferenceAcceptedUpFollowerHistory
open ReferenceFollowerSparseEmissionRecovery
open ReferenceFollowerBufferProvenance
open DeclaredFollowerLocalRound
open RecordedQueueRun
open QueueReplay
open PublicDiscreteDraws

namespace Bandits.Support.ReferenceFirstReplacementCutoffAcceptedNumericalReplay

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The actual first accepted replacement cutoff recovers the numerical
queue obtained by serving every original date from the transmitted DOWN
queue. The result keeps the physical branch selectors and checked operation
outputs in the conclusion; no trajectory or success predicate is an input. -/
theorem complete_first_replacement_cutoff_accepted_numerical_replay
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
            C.length = L ∧ X = birth :: tail ∧ 1 ≤ L ∧
            ∀ i : Fin (p.m - 1),
              match (cut.output.followers i).down with
              | none => True
              | some diagnostic =>
                match diagnostic.outcome with
                | .accepted before after _raw M scan registers lastService =>
                  let a := payload.assignment.assigned i
                  let A := fun b => (C.take b).map (fun z =>
                    (true, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) z a))
                  let Q := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q) (A b)
                  M = payload.downRecord i ∧
                  (cut.output.followers i).downInput = some before ∧
                  scan.endpoint = u ∧
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
                    (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M before u).take b = A b) ∧
                  registers = Q L ∧
                  lastService = (Q L).1 - (Q (L - 1)).1 ∧
                  after.lastDown = some M ∧
                  (after.S, after.backlog) = Q L ∧
                  after.delta = lastService ∧
                  after.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
                  after.buffer = [] ∧
                  (∃ old actualMemory,
                    cut.input.state.followers i = .ordinary old actualMemory ∧
                    (cut.output.followers i).configuration = .ordinary after actualMemory ∧
                    (cut.output.followers i).failure = none ∧
                    DeclaredFollowerLocalRound.releaseAndFinish rate i cut.input.row cut.input.time
                      (cut.output.preparation.feedback.observations
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                      { old with status := ActiveRoundActions.FollowerStatus.unoccupied }
                      actualMemory after = .ok (after, actualMemory) ∧
                    after.initializationFailure = old.initializationFailure) ∧
                  ReferenceAcceptedUpFollowerHistory.RetainedDown cut i M ∧
                  (∃ recovered : ActiveFollowerDownAcceptance.ReplayRegisters,
                    ActiveFollowerDownAcceptance.checkedRecovery p rate M before u = .ok recovered ∧
                    recovered.registers = registers ∧
                    recovered.lastService = lastService ∧
                    ∀ b : ℕ, ∃ middle,
                      ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
                        (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩ (A b) = .ok middle ∧
                      ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
                      middle.registers = Q b)
                | _ => True
          | _ => True
      | _ => True := by
  classical
  have hcontinuing :=
    ReferenceFirstReplacementContinuingNumericalReplay.complete_first_replacement_continuing_follower_numerical_replay
      rate source rewards C_star C_h
  have hsource :=
    ReferenceFirstReplacementNumericalSourceRecovery.complete_first_replacement_numerical_source_stream
      rate source rewards C_star C_h
  have hemissions :=
    ReferenceFirstReplacementCutoffAcceptedSparseEmissions.complete_first_replacement_cutoff_accepted_sparse_emissions
      rate source rewards C_star C_h
  have hdown :=
    ReferenceFirstReplacementCutoffDownRecovery.complete_first_replacement_cutoff_down_recovery_and_finish
      rate source rewards C_star C_h
  dsimp only at hcontinuing hsource hemissions hdown ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
      simp only [hb] at hcontinuing hsource hemissions hdown ⊢
      cases hc : birth.output.preparation.coordinator with
      | first _ => trivial
      | live _ _ _ _ => trivial
      | dagger => trivial
      | invalidCollectionCutoff => trivial
      | collection old ledger clock cutoff outcome =>
          rw [hc] at hcontinuing hsource hemissions hdown
          cases outcome <;> try trivial
          rename_i core consistent started hs instruction hinstruction output hcons
            clockData installed arm
          dsimp only [ReferenceActivePhysicalStep.collectionInput]
            at hcontinuing hsource hemissions hdown ⊢
          let payloadRoot : ReferenceActivePhysicalStep.Payload rate :=
            installed.registers.payload
          have payloadRootEq : payloadRoot = installed.registers.payload := rfl
          let payload := payloadRoot
          let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
          let X := (R.drop v).take (1 + tail.length)
          let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
          let L := X.length
          let cIndex := v + 1 + tail.length
          obtain ⟨hCcontinuing, hXcontinuing, hsteps⟩ := hcontinuing
          obtain ⟨hCsource, hcells, hrecoveries⟩ := hsource
          have hstream : X = birth :: tail := hXcontinuing
          have hL : L = X.length := rfl
          have hLpos : 1 ≤ L := by
            rw [hL, hstream]
            simp only [List.length_cons]
            omega
          cases hcGet : R[cIndex]? with
          | none => trivial
          | some cut =>
              dsimp only [tail, cIndex] at hdown hemissions ⊢
              have hcGetExpanded :
                  R[v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length]? =
                    some cut := by
                simpa only [cIndex, tail] using hcGet
              simp only [hcGetExpanded] at hdown
              simp only [hcGetExpanded] at hemissions
              rcases hdown with ⟨hnotContinuing, hcutBranch⟩
              refine ⟨hnotContinuing, ?_⟩
              cases hcutCoord : cut.output.preparation.coordinator with
              | first _ => trivial
              | collection _ _ _ _ _ => trivial
              | dagger => trivial
              | invalidCollectionCutoff => trivial
              | live liveRegisters owned base outcome =>
                  rw [hcutCoord] at hcutBranch hemissions
                  cases outcome <;> try trivial
                  rename_i dispatched hsLedger ledger hi he hd hcPayload hn chosen
                  dsimp only [ReferenceActivePhysicalStep.liveInput]
                    at hcutBranch hemissions ⊢
                  have hCemissions := hemissions.1
                  have hXemissions := hemissions.2.1
                  have hEmissionsAtAll := hemissions.2.2
                  rcases hcutBranch with ⟨hpayload, htimeBirth, htimeSource,
                    hrows, hselectedRow, hrewards, hsigmaPayload, hsourceStart,
                    hfirstCutoff, hgridBound, hcause, hselectedBlock⟩
                  rcases hselectedBlock with ⟨selected, hselection, hselectedPayload,
                    hpendingChoice, hcutoffChoice, hfollower⟩
                  let M := payload.downRecord
                  let a := payload.assignment.assigned
                  have hresultPrefix :
                      C.length = L ∧ X = birth :: tail ∧ 1 ≤ L := by
                    refine ⟨?_, hstream, hLpos⟩
                    calc
                      C.length = X.length := hCcontinuing
                      _ = L := hL.symm
                  refine ⟨hresultPrefix.1, hresultPrefix.2.1, hresultPrefix.2.2, ?_⟩
                  intro i
                  cases hdiagnostic : (cut.output.followers i).down with
                  | none => trivial
                  | some diagnostic =>
                          cases houtcome : diagnostic.outcome with
                      | skipped _ _ => simp only [houtcome]
                      | inputFailure _ _ => simp only [houtcome]
                      | decodeOrParseRejected _ _ _ => simp only [houtcome]
                      | parsedButUnaccepted _ _ _ _ => simp only [houtcome]
                      | outputFailure _ _ => simp only [houtcome]
                      | accepted before after raw message scan registers' lastService' =>
                          simp only [houtcome]
                          have hEaccepted := hEmissionsAtAll.2 i
                          simp only [hdiagnostic, houtcome] at hEaccepted
                          rcases hEaccepted with ⟨hEMessage, hEDownInput, hEScan,
                            hEU, hENoReset, hEUnoccupied, hEDates⟩
                          rcases hfollower i with ⟨oldState, incomingMemory, hinput,
                            hdomainOld, hmassOld, hzeroOld, hstrictOld, hbusyOld,
                            hdecision, hstartRound, hprepared, hdomainChoice,
                            hmassChoice, hpair, hdates, hup, hstarted, hcredit,
                            logged, post, hlogging, hbuffer, hoperation, hlast,
                            hS, hdelta, hbacklog, hflagChoice, hloggedUnoccupied,
                            hloggedPair, hloggedDates, hnoAppend, hconsume,
                            hpostUnoccupied, hpostDomain, hpostMass, hpostDelta,
                            hpostFlag, hbranches, hrecordResult, hloggedInput,
                            hloggedCut, hrelease, hfinishRound, hreleaseFinish,
                            hfollowersActual⟩
                          have hcutInput : (cut.output.followers i).downInput = some logged := by
                            rw [hfollowersActual]
                          have hcutDiagnosticOutput : (cut.output.followers i).down =
                              some (ReferenceDownReception.referenceDownCut p
                                cut.output.preparation.coordinator.downView i cut.input.row
                                cut.input.time
                                (cut.output.preparation.feedback.observations
                                  (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                                rate logged) := by
                            rw [hcutCoord, hfollowersActual]
                            rfl
                          have hdiagEq : diagnostic =
                              ReferenceDownReception.referenceDownCut p
                                cut.output.preparation.coordinator.downView i cut.input.row
                                cut.input.time
                                (cut.output.preparation.feedback.observations
                                  (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                                rate logged := by
                            apply Option.some.inj
                            exact hdiagnostic.symm.trans hcutDiagnosticOutput
                          have hdiagnosticOutcome :
                              (ReferenceDownReception.referenceDownCut p
                                cut.output.preparation.coordinator.downView i cut.input.row
                                cut.input.time
                                (cut.output.preparation.feedback.observations
                                  (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                                rate logged).outcome =
                              .accepted before after raw message scan registers' lastService' := by
                            rw [hcutCoord] at hdiagEq
                            rw [hcutCoord, ← hdiagEq]
                            exact houtcome
                          rw [hcutCoord] at hdiagnosticOutcome
                          rcases hbranches with hskipped | hrejected | hparsed | haccepted
                          · have hfalse := hdiagnosticOutcome.symm.trans hskipped.2.1
                            cases hfalse
                          · have hrejectedOutcome := hrejected.2.2.2.2.2.2.2.2.1
                            have hfalse := hdiagnosticOutcome.symm.trans hrejectedOutcome
                            cases hfalse
                          · have hparsedOutcome := hparsed.2.2.2.2.2.2.2.1
                            have hfalse := hdiagnosticOutcome.symm.trans hparsedOutcome
                            cases hfalse
                          · rcases haccepted with ⟨hselectedDown, hdecodedWord,
                              hraw, hfiltered, hrawComparison, hordinaryParse,
                              hordinaryAcceptance, hcheckedData⟩
                            rcases hcheckedData with ⟨accepted, hcheckedData⟩
                            rcases hcheckedData with ⟨recovered, hchecked,
                              hscanEndpoint, hrounds, hqueueRecords, hallEnabled,
                              hregisters, hprefixReplay, hlastService,
                              hcutOutcome, hpostEq⟩
                            have hacceptedOutcome := hdiagnosticOutcome.symm.trans hcutOutcome
                            injection hacceptedOutcome with hbefore hafter hrawEq
                              hmessage hscan hregistersEq hlastServiceEq
                            subst before
                            subst message
                            let Msg := payload.downRecord i
                            have hXdates :
                                X.map (fun x => x.input.time.val + 1) =
                                  (List.range L).map (Msg.val.sigma + ·) := by
                              apply List.ext_getElem
                              · simp only [List.length_map, List.length_range]
                                exact hL
                              · intro q hqX hqRange
                                simp only [List.getElem_map, List.getElem_range]
                                have hj : q < X.length := by
                                  simpa only [List.length_map] using hqX
                                have hdate := (hEDates ⟨q, hj⟩).1
                                simpa only [X, Msg, payload, payloadRoot,
                                  List.get_eq_getElem] using hdate
                            let Arrivals := fun b => (C.take b).map (fun z =>
                              (true, RecordedQueueRun.quantizedArrival
                                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                z (payload.assignment.assigned i)))
                            let Replay := fun b => QueueReplay.replay
                              (4 * rate.n) (0, Msg.val.q) (Arrivals b)
                            let arrivals := C.map (fun z =>
                              RecordedQueueRun.quantizedArrival
                                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                z (payload.assignment.assigned i))
                            let records := C.map (fun z =>
                              (true, RecordedQueueRun.quantizedArrival
                                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                z (payload.assignment.assigned i)))
                            have hUactual : cut.input.time.val + 1 = Msg.val.sigma + L := hEU
                            have hRoundsRange :
                                ActiveFollowerDownAcceptance.recoveryRounds p rate Msg
                                  (cut.input.time.val + 1) =
                                  (List.range L).map (Msg.val.sigma + ·) := by
                              change SparseCalendarReplay.sparseCalendarRounds
                                Msg.val.sigma (cut.input.time.val + 1) =
                                  (List.range L).map (Msg.val.sigma + ·)
                              rw [hUactual]
                              simp only [SparseCalendarReplay.sparseCalendarRounds,
                                Nat.add_sub_cancel_left]
                            have hRoundsDates :
                                ActiveFollowerDownAcceptance.recoveryRounds p rate Msg
                                  (cut.input.time.val + 1) =
                                  X.map (fun x => x.input.time.val + 1) := by
                              rw [hRoundsRange]
                              exact hXdates.symm
                            have hArrivals :
                                ActiveFollowerDownAcceptance.recoveryArrivals p rate Msg logged
                                  (cut.input.time.val + 1) = arrivals := by
                              have hArrivalsLength :
                                  (ActiveFollowerDownAcceptance.recoveryArrivals p rate Msg logged
                                    (cut.input.time.val + 1)).length = L := by
                                simp only [ActiveFollowerDownAcceptance.recoveryArrivals,
                                  List.length_map,
                                  ActiveFollowerDownAcceptance.recoveryRounds_length]
                                rw [hUactual]
                                omega
                              apply List.ext_getElem
                              · dsimp only [arrivals]
                                rw [hArrivalsLength]
                                simp only [List.length_map]
                                exact (hCsource.trans hL.symm).symm
                              · intro q hqArrivals hqRecords
                                have hq : q < L := by
                                  rw [hArrivalsLength] at hqArrivals
                                  exact hqArrivals
                                have hj : q < X.length := by rw [← hL]; exact hq
                                let j : Fin X.length := ⟨q, hj⟩
                                have hroundBound : q <
                                    (ActiveFollowerDownAcceptance.recoveryRounds p rate Msg
                                      (cut.input.time.val + 1)).length := by
                                  rw [hRoundsDates]
                                  simp only [List.length_map]
                                  exact hj
                                have hroundAtOpt :
                                    (ActiveFollowerDownAcceptance.recoveryRounds p rate Msg
                                      (cut.input.time.val + 1))[q]? =
                                      some (Msg.val.sigma + q) := by
                                  rw [hRoundsRange]
                                  simp only [List.getElem?_map,
                                    List.getElem?_range hq, Option.map_some]
                                have hroundAt :
                                    (ActiveFollowerDownAcceptance.recoveryRounds p rate Msg
                                      (cut.input.time.val + 1))[q]'hroundBound =
                                      Msg.val.sigma + q := by
                                  have hlookup := List.getElem?_eq_getElem hroundBound
                                  exact Option.some.inj (hlookup.symm.trans hroundAtOpt)
                                have hdate := (hEDates j).1
                                have hbufferEmission := (hEDates j).2
                                obtain ⟨cell, hcellIndex, hreadout, hcellPayload,
                                  _henabled, _hreward, _hrate, _hmarker, _howners⟩ := hcells j
                                have hCbound : q < C.length := by
                                  rw [hCsource]
                                  exact hj
                                have hCself : C[q]? = some (C.get ⟨q, hCbound⟩) :=
                                  List.getElem?_eq_some_iff.mpr ⟨hCbound, rfl⟩
                                have hCvalue : C.get ⟨q, hCbound⟩ = cell.input :=
                                  Option.some.inj (hCself.symm.trans hcellIndex)
                                have hCindex : C[q]'hCbound = C.get ⟨q, hCbound⟩ := by
                                  simp only [List.get_eq_getElem]
                                have hfields : ∀ k,
                                    (cell.states k).status ≠
                                      ActiveRoundActions.FollowerStatus.unoccupied →
                                    (cell.states k).lastDown =
                                      some (cell.selected.view.payload.downRecord k) := by
                                  intro k hk
                                  obtain ⟨preK, preMemoryK, nextK, nextMemoryK,
                                    hpreparedK, _houtputK, _hfailureK,
                                    hpreOccupiedK, _hnextOccupiedK⟩ := hsteps j k
                                  have hconfig := (cell.ordinary k).symm.trans hpreparedK
                                  simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq]
                                    at hconfig
                                  have hstate : cell.states k = preK := hconfig.1
                                  have hkPre : preK.status ≠
                                      ActiveRoundActions.FollowerStatus.unoccupied := by
                                    rw [← hstate]
                                    exact hk
                                  have hlast := (hpreOccupiedK hkPre).1
                                  rw [← hcellPayload] at hlast
                                  rw [hstate]
                                  exact hlast
                                have hunoccupied : (cell.states i).status =
                                    ActiveRoundActions.FollowerStatus.unoccupied := by
                                  exact hEUnoccupied j (cell.states i) (cell.memories i)
                                    (cell.ordinary i)
                                have harrival :=
                                  ReferenceFirstLiveUnoccupiedEmission.emissionContribution_eq_quantizedArrival
                                    (X.get j) cell hfields i hunoccupied
                                rw [hcellPayload] at harrival
                                have hbufferQuantized := hbufferEmission.trans harrival
                                have hleft :
                                    (ActiveFollowerDownAcceptance.recoveryArrivals p rate Msg
                                      logged (cut.input.time.val + 1))[q] =
                                      ActiveFollowerDownAcceptance.bufferArrivalAt p rate Msg
                                        logged (Msg.val.sigma + q) := by
                                  simp only [ActiveFollowerDownAcceptance.recoveryArrivals,
                                    List.getElem_map]
                                  rw [hroundAt]
                                have hright : arrivals[q] =
                                    RecordedQueueRun.quantizedArrival
                                      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                      (C.get ⟨q, hCbound⟩)
                                      (payload.assignment.assigned i) := by
                                  simp only [arrivals, List.getElem_map]
                                  rw [hCindex]
                                rw [hleft, hright, hCvalue]
                                calc
                                  ActiveFollowerDownAcceptance.bufferArrivalAt p rate Msg logged
                                      (Msg.val.sigma + q) =
                                      ReferenceFollowerSparseEmissionRecovery.emissionContribution
                                        Msg i (X.get j) := by
                                          simpa only [Msg] using hbufferEmission
                                  _ = RecordedQueueRun.quantizedArrival
                                        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                                        cell.input (payload.assignment.assigned i) := by
                                          simpa only [Msg, hcellPayload] using harrival
                            have hQueueFull :
                                ActiveFollowerDownAcceptance.recoveryQueueRecords p rate Msg
                                  logged (cut.input.time.val + 1) = Arrivals L := by
                              change (ActiveFollowerDownAcceptance.recoveryArrivals p rate Msg
                                logged (cut.input.time.val + 1)).map (fun n => (true, n)) = Arrivals L
                              rw [hArrivals]
                              have hCL : C.length = L := hCsource.trans hL.symm
                              have htake : C.take L = C :=
                                List.take_of_length_le (le_of_eq hCL)
                              dsimp only [Arrivals, arrivals]
                              rw [htake]
                              simp only [List.map_map, Function.comp_def]
                            have hArrivalsFull : Arrivals L = records := by
                              dsimp only [Arrivals, records]
                              rw [List.take_of_length_le
                                (le_of_eq (hCsource.trans hL.symm))]
                            have hrecordsTake (b : ℕ) : records.take b = Arrivals b := by
                              dsimp only [records, Arrivals, arrivals]
                              rw [List.map_take]
                            have hTakePrefix (b : ℕ) :
                                (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate Msg
                                  logged (cut.input.time.val + 1)).take b = Arrivals b := by
                              rw [hQueueFull]
                              rw [hArrivalsFull]
                              exact hrecordsTake b
                            have hcheckedReplay :
                                ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
                                  (4 * rate.n) 0 ⟨(0, Msg.val.q), 0⟩ records = .ok recovered := by
                              have h := ActiveFollowerDownAcceptance.checkedRecovery_eq_checkedReplay
                                p rate Msg logged (cut.input.time.val + 1)
                              rw [hchecked] at h
                              rw [hQueueFull, hArrivalsFull] at h
                              exact h.symm
                            have hrecordsLength : records.length = L := by
                              simp only [records, List.length_map]
                              exact hCsource.trans hL.symm
                            have hfullCheck :
                                ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
                                  (4 * rate.n) 0 ⟨(0, Msg.val.q), 0⟩
                                  (records.take L) = .ok recovered := by
                              simpa only [List.take_of_length_le (by rw [hrecordsLength])] using
                                hcheckedReplay
                            have hLlast : L - 1 + 1 = L := by omega
                            have hlastReplay :=
                              ReferenceFirstReplacementAcceptedTailNumericalReplay.checkedReplay_take_last_service
                                (4 * rate.n) (D p) (p.T * D p) (0, Msg.val.q)
                                records (L - 1) (by rw [hrecordsLength]; omega)
                                recovered (by simpa only [hLlast] using hfullCheck)
                            have hRecoveredRegister : recovered.registers = Replay L := by
                              simpa only [hLlast, hrecordsTake, Replay] using hlastReplay.1
                            have hRecoveredService : recovered.lastService =
                                (Replay L).1 - (Replay (L - 1)).1 := by
                              simpa only [hLlast, hrecordsTake, Replay] using hlastReplay.2.1
                            have hDiagnosticRegister : registers' = Replay L :=
                              hregistersEq.trans hRecoveredRegister
                            have hDiagnosticService : lastService' =
                                (Replay L).1 - (Replay (L - 1)).1 :=
                              hlastServiceEq.trans hRecoveredService
                            have hstatus : after.status =
                                ActiveRoundActions.FollowerStatus.unoccupied := by
                              rw [hafter, hpostEq]
                            have hafterLast : after.lastDown = some Msg := by
                              rw [hafter, hpostEq]
                            have hafterPair : (after.S, after.backlog) = Replay L := by
                              rw [hafter, hpostEq]
                              exact hRecoveredRegister
                            have hafterDelta : after.delta = lastService' := by
                              rw [hafter, hpostEq]
                              exact hlastServiceEq.symm
                            have hafterBuffer : after.buffer = [] := by
                              rw [hafter, hpostEq]
                            have hactualMemory :
                                (∃ old actualMemory,
                                  cut.input.state.followers i = .ordinary old actualMemory ∧
                                  (cut.output.followers i).configuration =
                                    .ordinary after actualMemory ∧
                                  (cut.output.followers i).failure = none ∧
                                  DeclaredFollowerLocalRound.releaseAndFinish rate i cut.input.row
                                    cut.input.time
                                    (cut.output.preparation.feedback.observations
                                      (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                                    { old with status := ActiveRoundActions.FollowerStatus.unoccupied }
                                    actualMemory after = .ok (after, actualMemory) ∧
                                  after.initializationFailure = old.initializationFailure) := by
                              refine ⟨oldState, incomingMemory, hinput, ?_, ?_, ?_, ?_⟩
                              · rw [hfollowersActual, hafter]
                              · rw [hfollowersActual]
                              · simpa only [hafter] using hreleaseFinish
                              · rw [hafter]
                                exact hpostFlag
                            have hretained :
                                ReferenceAcceptedUpFollowerHistory.RetainedDown cut i Msg := by
                              refine ⟨logged, diagnostic, after, raw, scan,
                                registers', lastService', ?_, hdiagnostic, ?_⟩
                              · exact hcutInput
                              · exact houtcome
                            have hcutRecovery :
                                ∃ recovered : ActiveFollowerDownAcceptance.ReplayRegisters,
                                  ActiveFollowerDownAcceptance.checkedRecovery p rate Msg logged
                                    (cut.input.time.val + 1) = .ok recovered ∧
                                  recovered.registers = registers' ∧
                                  recovered.lastService = lastService' ∧
                                  ∀ b : ℕ, ∃ middle,
                                    ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
                                      (4 * rate.n) 0 ⟨(0, Msg.val.q), 0⟩ (Arrivals b) = .ok middle ∧
                                    ActiveFollowerDownAcceptance.replay_register_domain
                                      (D p) (p.T * D p) middle ∧ middle.registers = Replay b := by
                              refine ⟨recovered, hchecked, ?_, ?_, ?_⟩
                              · exact hregistersEq.symm
                              · exact hlastServiceEq.symm
                              · intro b
                                rcases hprefixReplay b with ⟨middle, hmiddleCheck,
                                  hmiddleDomain, hmiddleRegisters⟩
                                refine ⟨middle, ?_, hmiddleDomain, ?_⟩
                                · rw [hTakePrefix b] at hmiddleCheck
                                  exact hmiddleCheck
                                · rw [hTakePrefix b] at hmiddleRegisters
                                  simpa only [Replay] using hmiddleRegisters
                            refine ⟨rfl, hcutInput, ?_, hUactual,
                              hRoundsDates, hXdates, ?_, hQueueFull, hTakePrefix,
                              hDiagnosticRegister, hDiagnosticService, hafterLast,
                              hafterPair, hafterDelta, hstatus, hafterBuffer,
                              hactualMemory, hretained, hcutRecovery⟩
                            · rw [hscan]
                              exact hscanEndpoint
                            · simpa only [arrivals] using hArrivals

end Bandits.Support.ReferenceFirstReplacementCutoffAcceptedNumericalReplay

end
