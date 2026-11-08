/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionPrefix

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.TakeWhile

/-!
# Actual accepted DOWN geometry during replacement collection

Sources: sources/zip4/manuscript/06_interruptions.tex:193-233,246-295,
sources/zip4/manuscript/05_binary_transport.tex:354-431, and
sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79.

This proves physical provenance, the cutoff endpoint, absence of earlier
accepted resets, and actual unoccupied PREPARE states for delayed DOWN
acceptance. It leaves the launch buffer and all earlier resets intact.
Sparse-arrival and queue-list identities belong to the later consumer.
-/

@[expose] public section
noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower ActiveFollowerLifecycle ActiveFollowerDownAcceptance
open ReferenceDownReception SparseCalendarReplay PublicDiscreteDraws
open ReferenceFollowerBufferProvenance ReferenceFollowerReplyChronology
open ReferenceFirstReplacementCollectionSeedEndpoint
open ReferenceFirstReplacementCollectionDispatchOrigin
open ReferenceFirstReplacementCollectionPrefix
open ReferenceFirstReplacementLiveFollowerPrefix
open ReferenceFirstReplacementFollowerBoundary
open ReferenceFirstReplacementCutoffPreparedBoundary
open ReferenceFirstReplacementDownRecovery
open ReferenceFirstReplacementNextFollowerStep

namespace Bandits.Support.ReferenceFirstReplacementCollectionEmissionGeometry

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Backward chronology for an actual prefix ending at an ordinary input. -/
private theorem prior_output_bound
    {records : List (RoundRecord (p := p) (rate := rate))}
    {initial current : ReferenceActivePhysicalStep.State p rate}
    (n : ℕ) (chain : Connected initial (records.take n) current)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : LocalMemory p) (hinput : current.followers i = .ordinary state memory)
    (k : Fin records.length) (hk : k.val < n) :
    ∃ next nextMemory, (records.get k).output.next.followers i = .ordinary next nextMemory ∧
      acceptedStart next ≤ acceptedStart state := by
  obtain ⟨next, nextMemory, hnext, hbound⟩ := connected_output_chronology
    chain i state memory hinput k.val (by simp only [List.length_take]; omega)
  rw [List.getElem_take] at hnext
  exact ⟨next, nextMemory, hnext, hbound⟩

/-- An actual accepted reset under the current selected payload would force
its start at the later ordinary input to be at least the current start. -/
private theorem no_reset_of_current_views
    {records : List (RoundRecord (p := p) (rate := rate))}
    {initial current : ReferenceActivePhysicalStep.State p rate}
    (n v : ℕ) (chain : Connected initial (records.take n) current)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : LocalMemory p) (hinput : current.followers i = .ordinary state memory)
    (payload : Payload rate) (hstrict : acceptedStart state < (payload.downRecord i).val.sigma)
    (hviews : ∀ k : Fin records.length, v ≤ k.val → k.val < n →
      (records.get k).output.preparation.coordinator.downView = none ∨
      ∃ view : ChoiceTimeView p rate.eta,
        (records.get k).output.preparation.coordinator.downView = some view ∧
          view.payload = payload) :
    ∀ k : Fin records.length, v ≤ k.val → k.val < n →
      ¬ acceptedDownReset i (records.get k) := by
  intro k hlow hhigh hreset
  obtain ⟨next, nextMemory, hnextConfig, hnextBound⟩ :=
    prior_output_bound n chain i state memory hinput k hhigh
  rcases hreset with ⟨resetDiag, hresetDown, resetBefore, resetAfter,
    resetRaw, resetMsg, resetScan, resetRegisters, resetLast, hresetAccepted⟩
  obtain ⟨_, _, resetLogged, _, _, _, hresetInput, hresetActual⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice
      (records.get k) i resetDiag hresetDown
  have hresetOutcome := hresetAccepted
  rw [hresetActual] at hresetOutcome
  have halign := (records.get k).output.preparation.follower_alignment i
  rw [halign.1, halign.2.1, halign.2.2.1] at hresetOutcome
  have hbeforeEq := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_before_eq
    _ i _ _ _ resetLogged resetBefore resetAfter resetRaw resetMsg resetScan
    resetRegisters resetLast hresetOutcome
  subst resetBefore
  have happlied : appliedDown (records.get k) i resetMsg.val.sigma :=
    ⟨resetLogged, resetDiag, resetAfter, resetRaw, resetMsg, resetScan,
      resetRegisters, resetLast, hresetInput, hresetDown, hresetAccepted, rfl⟩
  obtain ⟨_, _, _, _, hnextStart⟩ := record_appliedDown_strict
    (records.get k) i resetMsg.val.sigma happlied next nextMemory hnextConfig
  rcases hviews k hlow hhigh with hnone | ⟨view, hview, hpay⟩
  · obtain ⟨view, hview⟩ := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_someView
      _ i _ _ _ resetLogged resetLogged resetAfter resetRaw resetMsg resetScan
      resetRegisters resetLast hresetOutcome
    rw [hnone] at hview
    cases hview
  · rw [hview] at hresetOutcome
    have hmsg := ReferenceActiveDataOwnership.referenceDown_accepted_fields
      view i _ _ _ resetLogged resetLogged resetAfter resetRaw resetMsg resetScan
      resetRegisters resetLast hresetOutcome
    have hsame : resetMsg = payload.downRecord i := by
      rw [hmsg.1, hpay]
    rw [hsame] at hnextStart
    omega

/-- Every actual accepted DOWN in the replacement collection tail uses the
installed message and cutoff endpoint. Its prior replacement records have no
accepted reset, and its recovery dates have actual unoccupied PREPARE states. -/
theorem complete_first_replacement_collection_emission_geometry
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
                          .ordinary state memory ∧ state.status = .unoccupied)
                | _ => True
          | _ => True
      | _ => True := by
  classical
  have hseed := Bandits.Support.ReferenceFirstReplacementCollectionSeedEndpoint.complete_first_replacement_collection_seed_endpoint
    rate source rewards C_star C_h
  have hdispatch := Bandits.Support.ReferenceFirstReplacementCollectionDispatchOrigin.complete_first_replacement_collection_dispatch_origin
    rate source rewards C_star C_h
  have hprefix := Bandits.Support.ReferenceFirstReplacementCollectionPrefix.complete_first_replacement_collection_follower_prefix
    rate source rewards C_star C_h
  have hgeometry := Bandits.Support.ReferenceFirstReplacementLiveFollowerPrefix.complete_first_replacement_continuing_geometry
    rate source rewards C_star C_h
  have hboundary := Bandits.Support.ReferenceFirstReplacementFollowerBoundary.complete_first_replacement_follower_boundary
    rate source rewards C_star C_h
  have hcutoff := Bandits.Support.ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
    rate source rewards C_star C_h
  have hbirth := Bandits.Support.ReferenceFirstReplacementDownRecovery.complete_first_replacement_down_recovery_and_finish
    rate source rewards C_star C_h
  have hbirthReadout := Bandits.Support.ReferenceFirstReplacementNextFollowerStep.complete_first_replacement_birth_live_readout
    rate source rewards C_star C_h
  dsimp only at hseed hdispatch hprefix hgeometry hboundary hcutoff hbirth hbirthReadout ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hbirthGet : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hbirthGet] at hseed hdispatch hprefix hgeometry hboundary hcutoff hbirth hbirthReadout ⊢
    cases hbirthCoord : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      rw [hbirthCoord] at hseed hdispatch hprefix hgeometry hboundary hcutoff hbirth hbirthReadout
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent clockData installed birthArm
      dsimp only [ReferenceActivePhysicalStep.collectionInput]
        at hseed hdispatch hprefix hgeometry hboundary hcutoff hbirth hbirthReadout ⊢
      let payload := installed.registers.payload
      let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
      let c := v + 1 + tail.length
      cases hcutGet : R[c]? with
      | none => trivial
      | some cut =>
        simp only [tail, c, hcutGet] at hseed hdispatch hprefix hgeometry hboundary hcutoff hbirth hbirthReadout ⊢
        cases hcutCoord : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers _ _ outcome =>
          simp only [hcutCoord] at hseed hdispatch hprefix hcutoff
          cases outcome <;> try trivial
          rename_i cutoffResult
          dsimp only [ReferenceActivePhysicalStep.liveInput]
            at hseed hdispatch hprefix hgeometry hboundary hcutoff hbirth hbirthReadout ⊢
          let u := cut.input.time.val + 1
          let W := (R.drop (v + 1 + tail.length + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          rcases hseed with ⟨hwindow, hEzero, hcutTime, hu3, huT, hfirstCutoff, hseedFollowers⟩
          rcases hprefix with ⟨hwindowP, hEzeroP, hendpointsP, hu3P, huTP, hfirstP, hprefixFollowers⟩
          have hv : v < R.length := (List.getElem?_eq_some_iff.mp hbirthGet).1
          have hc : c < R.length := (List.getElem?_eq_some_iff.mp hcutGet).1
          have hcutIndex : R.get ⟨c, hc⟩ = cut := by
            apply Option.some.inj
            exact (List.getElem?_eq_some_iff.mpr ⟨hc, by rfl⟩).symm.trans hcutGet
          have hbirthIndex : R.get ⟨v, hv⟩ = birth := by
            apply Option.some.inj
            exact (List.getElem?_eq_some_iff.mpr ⟨hv, by rfl⟩).symm.trans hbirthGet
          have htimeAt : ∀ k : Fin R.length, (R.get k).input.time.val = s + k.val := by
            intro k
            obtain ⟨_, _, hactual⟩ :=
              ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h source k
            have htime := congrArg
              (fun x : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
                x.input.time.val) hactual
            simpa [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
              ReferenceActivePhysicalHorizon.roundInputAt] using htime
          have hbirthTime : birth.input.time.val = s + v := by
            rw [← hbirthIndex]
            exact htimeAt ⟨v, hv⟩
          have hRlen : R.length = p.T - s := by
            simpa [R, s] using
              ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate source rewards C_star C_h
          have hpayloadSigma : payload.sigma.val = s + v := by
            calc
              payload.sigma.val = birth.input.time.val := hgeometry.1
              _ = s + v := hbirthTime
          have hmsgSigma (i : Fin (p.m - 1)) :
              (payload.downRecord i).val.sigma = s + v + 1 := by
            rw [payload.downRecord_fields i]
            rw [hpayloadSigma]
          have hcutoffSelected :
              ∃ selected : ReferenceActivePhysicalStep.Selection cut.input,
                cut.output.preparation.coordinator.selection = some selected ∧
                  selected.view.payload = payload := by
            rcases hcutoff with
              ⟨_, ⟨_, _, _, _, _, _, _, _, _, _, _, selected, hsel, hpay, _, _, _⟩⟩
            refine ⟨selected, ?_, by simpa [payload] using hpay⟩
            rw [hcutCoord]
            exact hsel
          have hbirthSelected :
              ∃ selected : ReferenceActivePhysicalStep.Selection birth.input,
                birth.output.preparation.coordinator.selection = some selected ∧
                  selected.view.payload = payload := by
            rcases hbirthReadout with ⟨birthIndex, hbIndex, _hrecord, selected, hsel, hpay, _⟩
            have hbIndex' : birthIndex = (⟨v, hv⟩ : Fin R.length) := Fin.ext hbIndex
            subst birthIndex
            exact ⟨selected, by rw [hbirthCoord]; exact hsel, by simpa [payload] using hpay⟩
          have htailView :
              ∀ k : Fin R.length, v + 1 ≤ k.val → k.val < c →
                ∃ selected : ReferenceActivePhysicalStep.Selection (R.get k).input,
                  (R.get k).output.preparation.coordinator.selection = some selected ∧
                    selected.view.payload = payload := by
            intro k hlow hhigh
            let q : Fin tail.length := ⟨k.val - (v + 1), by dsimp [c] at hhigh; omega⟩
            have hqIndex : v + 1 + q.val = k.val := by simp [q]; omega
            have hqGet := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R v q
            have hkGet : R[k.val]? = some (R.get k) :=
              List.getElem?_eq_some_iff.mpr ⟨k.isLt, by simp⟩
            have htailGet : R[k.val]? = some (tail.get q) := by
              simpa [hqIndex, tail] using hqGet
            have hrecord : R.get k = tail.get q := Option.some.inj (hkGet.symm.trans htailGet)
            rcases hgeometry.2 q with ⟨_, _, _, _, _, selected, hsel, hpay, _⟩
            exact hrecord.symm ▸ ⟨selected, hsel, by simpa [payload] using hpay⟩
          have hviewAt :
              ∀ k : Fin R.length, v ≤ k.val → k.val < c + 1 + W.length →
                ( (R.get k).output.preparation.coordinator.downView = none ∨
                  ∃ view : ReferenceDownReception.ChoiceTimeView p rate.eta,
                    (R.get k).output.preparation.coordinator.downView = some view ∧
                      view.payload = payload) := by
            intro k hlow hhigh
            by_cases hbirthK : k.val = v
            · have hk : k = (⟨v, hv⟩ : Fin R.length) := Fin.ext hbirthK
              subst k
              obtain ⟨selected, hsel, hpay⟩ := hbirthSelected
              right
              refine ⟨selected.view, ?_, hpay⟩
              rw [hbirthIndex]
              change birth.output.preparation.coordinator.selection.map
                ReferenceActivePhysicalStep.Selection.view = some selected.view
              simp [hsel]
            · by_cases hcutK : k.val = c
              · have hk : k = (⟨c, hc⟩ : Fin R.length) := Fin.ext hcutK
                subst k
                obtain ⟨selected, hsel, hpay⟩ := hcutoffSelected
                right
                refine ⟨selected.view, ?_, hpay⟩
                rw [hcutIndex]
                change cut.output.preparation.coordinator.selection.map
                  ReferenceActivePhysicalStep.Selection.view = some selected.view
                simp [hsel]
              · by_cases hbefore : k.val < c
                · obtain ⟨selected, hsel, hpay⟩ := htailView k (by omega) hbefore
                  right
                  refine ⟨selected.view, ?_, hpay⟩
                  change (R.get k).output.preparation.coordinator.selection.map
                    ReferenceActivePhysicalStep.Selection.view = some selected.view
                  rw [hsel]
                  rfl
                · let q : Fin W.length := ⟨k.val - (c + 1), by omega⟩
                  rcases (hdispatch.2 q).2.2.2.1 with hnone | ⟨view, hview, hpay⟩
                  · left
                    have hkGet : R[k.val]? = some (R.get k) :=
                      List.getElem?_eq_some_iff.mpr ⟨k.isLt, by simp⟩
                    have hqRecord :=
                      ReferenceFirstReplacementCollectionFollowerPrefix.collectionWindow_get
                        R c q.val q.isLt
                    have hindex : c + 1 + q.val = k.val := by simp [q]; omega
                    have hright : R[k.val]? = some (W.get q) := by simpa [hindex] using hqRecord
                    have hrecord : R.get k = W.get q := Option.some.inj (hkGet.symm.trans hright)
                    rw [hrecord]
                    change (W.get q).output.preparation.coordinator.downView = none at hnone
                    simpa [hrecord] using hnone
                  · right
                    refine ⟨view, ?_, by simpa [payload] using hpay⟩
                    have hkGet : R[k.val]? = some (R.get k) :=
                      List.getElem?_eq_some_iff.mpr ⟨k.isLt, by simp⟩
                    have hqRecord :=
                      ReferenceFirstReplacementCollectionFollowerPrefix.collectionWindow_get
                        R c q.val q.isLt
                    have hindex : c + 1 + q.val = k.val := by simp [q]; omega
                    have hright : R[k.val]? = some (W.get q) := by simpa [hindex] using hqRecord
                    have hrecord : R.get k = W.get q := Option.some.inj (hkGet.symm.trans hright)
                    rw [hrecord]
                    change (W.get q).output.preparation.coordinator.downView = some view at hview
                    simpa [hrecord] using hview
          intro j
          let r := W.get j
          let N := c + 1 + j.val
          have hrSome : R[N]? = some r :=
            ReferenceFirstReplacementCollectionFollowerPrefix.collectionWindow_get R c j.val j.isLt
          have hN : N < R.length := (List.getElem?_eq_some_iff.mp hrSome).1
          have hrIndex : R.get ⟨N, hN⟩ = r := (List.getElem?_eq_some_iff.mp hrSome).2
          have hfields := ReferenceLaterLiveNumericalReadout.source_record_prefix
            rate rewards C_star C_h source ⟨N, hN⟩
          obtain ⟨crossing, span, hactual⟩ := hfields
          have htimeR : r.input.time.val = s + N := by
            rw [← hrIndex, hactual]
            rfl
          have hrowsR : r.input.rows = source.1.2 := by rw [← hrIndex, hactual]; rfl
          have hselectedR : r.input.selected =
              ActualInitializationPhysicalStep.selectedRowIndex p source := by
            rw [← hrIndex, hactual]
            rfl
          have hrewardsR : r.input.rewards = rewards := by rw [← hrIndex, hactual]; rfl
          have htimeCollection : r.input.time.val = u + j.val := by
            rw [htimeR]
            change s + (c + 1 + j.val) = cut.input.time.val + 1 + j.val
            change cut.input.time.val = s + c at hcutTime
            rw [hcutTime]
            omega
          refine ⟨hrSome, htimeR, htimeCollection, hrowsR, hselectedR, hrewardsR, ?_⟩
          intro i
          cases hdownOuter : (r.output.followers i).down with
          | none => trivial
          | some diag =>
            cases houtcome : diag.outcome with
            | skipped _ _ => simp [houtcome]
            | inputFailure _ _ => simp [houtcome]
            | decodeOrParseRejected _ _ _ => simp [houtcome]
            | parsedButUnaccepted _ _ _ _ => simp [houtcome]
            | outputFailure _ _ => simp [houtcome]
            | accepted before after raw msg scan registers lastService =>
              rcases hprefixFollowers i with
                ⟨_hmsgSigmaBound, _hcredit, oldBirth, stateBirth, memoryBirth,
                  hcutInput, hcutConfiguration, hcutFailure, hendpointBirth,
                  hstatusBirth, hdomainBirth, hmassBirth, hdeltaBirth, hzeroBirth,
                  horiginBirth, hinitializationFailureBirth, hpairBirth, hdatesBirth,
                  hstateInvariant, hsteps, hnextBoundary⟩
              have hstep := hsteps j.val j.isLt
              rcases hstep with
                ⟨hrecordSome, state, logged, post, hinput, hstatus, hdomain, hmass,
                  hdelta, hfailure, hzero, horigin, hpair, hdates, hstartRound,
                  hprepared, hup, hlogging, hbuffer, hlast, hS, hdeltaLog, hbacklog,
                  hlogStatus, hbatch, hinit, hlogDomain, hoperation, hpairLog,
                  hdatesLog, hrecord, hdownInput, hdown, hrelease, hfinish,
                  hreleaseFinish, houtput, hconsume, hpostStatus, hpostDomain,
                  hpostMass, hpostDelta, hpostFailure, hpostZero, hpostOrigin,
                  hpostPair, hpostDates, hexpected, hselectedWord, hpreserve,
                  hbranches, hnext⟩
              have hdiagGet : (r.output.followers i).down = some diag := by
                exact hdownOuter
              have hdiagActual : diag = ReferenceDownReception.referenceDownCut p
                  r.output.preparation.coordinator.downView i r.input.row r.input.time
                  (r.output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged := by
                apply Option.some.inj
                calc
                  some diag = (r.output.followers i).down := hdownOuter.symm
                  _ = some (ReferenceDownReception.referenceDownCut p
                      r.output.preparation.coordinator.downView i r.input.row r.input.time
                      (r.output.preparation.feedback.observations
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged) := by
                    rw [houtput]
              rcases hbranches with hskip | hreject | hparsed | haccepted
              · have hfalse : False := by
                  have hskipOutcome := hskip.2.1
                  rw [← hdiagActual, houtcome] at hskipOutcome
                  cases hskipOutcome
                exact hfalse.elim
              · have hfalse : False := by
                  have hrejectOutcome := hreject.2.1
                  rw [← hdiagActual, houtcome] at hrejectOutcome
                  cases hrejectOutcome
                exact hfalse.elim
              · have hfalse : False := by
                  have hparsedOutcome := hparsed.2.2.2.2.2.2.2.1
                  rw [← hdiagActual, houtcome] at hparsedOutcome
                  cases hparsedOutcome
                exact hfalse.elim
              · rcases haccepted with
                  ⟨_, _, _, _, _, _, _, accepted, recovered, hscanEndpointBranch, hchecked,
                    hdiagOutcome, _⟩
                have hconstructor :
                    ActiveFollowerDownAcceptance.LocalDownResult.accepted before after raw msg
                        scan registers lastService =
                      ActiveFollowerDownAcceptance.LocalDownResult.accepted logged post
                        (ActiveFollowerDownAcceptance.currentDecodeStep p i r.input.row
                          r.input.time
                          (r.output.preparation.feedback.observations
                            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).2
                        (payload.downRecord i)
                        (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate
                          (payload.downRecord i) r.input.time
                          (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate
                            (payload.downRecord i) r.input.time logged accepted) r.input.row)
                        recovered.registers recovered.lastService := by
                  calc
                    _ = diag.outcome := houtcome.symm
                    _ = (ReferenceDownReception.referenceDownCut p
                        r.output.preparation.coordinator.downView i r.input.row r.input.time
                        (r.output.preparation.feedback.observations
                          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).outcome := by
                      rw [hdiagActual]
                    _ = _ := by exact hdiagOutcome
                have hfields : msg = payload.downRecord i := by
                  injection hconstructor
                have hbefore : before = logged := by
                  injection hconstructor
                have hscanEq : scan = ActiveFollowerDownAcceptance.acceptedCutoffScan p rate
                    (payload.downRecord i) r.input.time
                    (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate
                      (payload.downRecord i) r.input.time logged accepted) r.input.row := by
                  injection hconstructor
                have hscanEndpoint : scan.endpoint = u := by
                  rw [hscanEq]
                  exact hscanEndpointBranch
                have hactualInput : (r.output.followers i).downInput = some before := by
                  rw [houtput, hbefore]
                have hpreparedAtCurrent :
                    (r.output.preparation.followers.followers i).configuration =
                      .ordinary state memoryBirth := hprepared
                have hstrictLogged : acceptedStart logged < (payload.downRecord i).val.sigma :=
                  accepted.1
                have hstartLogged : acceptedStart logged = acceptedStart state := by
                  unfold acceptedStart
                  rw [hlast]
                have hstrict : acceptedStart state < (payload.downRecord i).val.sigma := by
                  rw [← hstartLogged]
                  exact hstrictLogged
                have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
                  rate source rewards C_star C_h
                  (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h crossing)
                  (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
                    rate source rewards C_star C_h crossing)
                have hchainCurrent := connected_take_to_input hchain N hN
                change Connected _ (R.take N) (R.get ⟨N, hN⟩).input.state at hchainCurrent
                rw [hrIndex] at hchainCurrent
                have hnoReset := no_reset_of_current_views N v hchainCurrent i state
                  memoryBirth hinput payload hstrict (fun k hlow hhigh =>
                    hviewAt k hlow (hhigh.trans_le
                      (Nat.add_le_add_left (Nat.le_of_lt j.isLt) (c + 1))))
                have hunoccupied : ∀ k : Fin R.length,
                    (payload.downRecord i).val.sigma ≤ (R.get k).input.time.val + 1 →
                    (R.get k).input.time.val + 1 < u →
                    ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
                      ∃ memory : LocalMemory p,
                        ((R.get k).output.preparation.followers.followers i).configuration =
                          .ordinary choice memory ∧ choice.status = .unoccupied := by
                  intro k hlow hhigh
                  have hkTime : (R.get k).input.time.val = s + k.val := htimeAt k
                  have hsig := hmsgSigma i
                  have hkLow : v ≤ k.val := by omega
                  have hkHigh : k.val < c := by
                    change cut.input.time.val = s + c at hcutTime
                    dsimp only [u] at hhigh
                    rw [hkTime, hcutTime] at hhigh
                    omega
                  by_cases hbirthK : k.val = v
                  · have hk : k = (⟨v, hv⟩ : Fin R.length) := Fin.ext hbirthK
                    subst k
                    rw [hbirthIndex]
                    obtain ⟨old, memory, logged, _, hstatus, hprepared, _⟩ := hbirth.2 i
                    exact ⟨old, memory, hprepared, hstatus⟩
                  · let q : Fin tail.length := ⟨k.val - (v + 1), by dsimp [c] at hkHigh; omega⟩
                    have hqIndex : v + 1 + q.val = k.val := by dsimp [q]; omega
                    have hqGet := continuingTail_get R v q
                    have hkGet : R[k.val]? = some (R.get k) :=
                      List.getElem?_eq_some_iff.mpr ⟨k.isLt, by simp⟩
                    have htailGet : R[k.val]? = some (tail.get q) := by
                      simpa only [hqIndex] using hqGet
                    have hrecordEq : R.get k = tail.get q :=
                      Option.some.inj (hkGet.symm.trans htailGet)
                    rcases hboundary q with
                      ⟨_, _, _, _, selected, _, _, _, _, _, hfollowers⟩
                    rcases hfollowers i with
                      ⟨prior, memory, next, nextMemory, hprior, _, _, _, _, hoccupied,
                        _, _, _, _, _, _, hprepared, _⟩
                    obtain ⟨out, outMemory, houtConfig, houtBound⟩ :=
                      prior_output_bound N hchainCurrent i state memoryBirth hinput k
                        (by dsimp only [N]; omega)
                    obtain ⟨choice, choiceMemory, hchoice, hchoiceBound, _⟩ :=
                      record_choice_chronology (R.get k) i out outMemory houtConfig
                    have hprepared' :
                        ((R.get k).output.preparation.followers.followers i).configuration =
                          .ordinary prior memory := by rw [hrecordEq]; exact hprepared
                    have heq : choice = prior :=
                      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                        (hchoice.symm.trans hprepared')).1
                    refine ⟨prior, memory, hprepared', ?_⟩
                    by_contra hbusy
                    have hlastCurrent := (hoccupied hbusy).1
                    have hpriorStart : acceptedStart prior = (payload.downRecord i).val.sigma := by
                      simpa only [payload, acceptedStart, hlastCurrent]
                    rw [heq, hpriorStart] at hchoiceBound
                    omega
                simp only [houtcome]
                refine ⟨hfields, hactualInput, ?_, hscanEndpoint, hnoReset, ?_⟩
                · rw [hbefore]
                  exact hdiagActual
                · simpa only [hfields] using hunoccupied

end Bandits.Support.ReferenceFirstReplacementCollectionEmissionGeometry

end
