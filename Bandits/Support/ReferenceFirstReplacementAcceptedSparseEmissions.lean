/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementLiveFollowerPrefix

import Lean.Elab.Tactic.Omega

/-!
# Accepted sparse emissions after the first replacement

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:9-70,193-233,246-295`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

For an actual accepted DOWN diagnostic on the retained continuing tail, the
accepted buffer's sparse arrival is the sum of the original physical log
emissions at that date. The buffer fold keeps the original launch seed and all
actual earlier resets; only the interval from the replacement birth to the
current input is shown reset-free. This is an internal result and asserts no
boundary safety, source law, numerical queue identity, or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower ActiveFollowerLifecycle ActiveFollowerDownAcceptance
open ReferenceDownReception SparseCalendarReplay PublicDiscreteDraws
open ReferenceFollowerBufferProvenance ReferenceFollowerReplyChronology
open ReferenceFollowerSparseEmissionRecovery

namespace Bandits.Support.ReferenceFirstReplacementAcceptedSparseEmissions

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

/-- For the actual first replacement, an accepted diagnostic in the retained
continuing tail has the complete dated sparse-emission identity on every
calendar date of its checked scan. The visible inputs are the original source,
whole reward table, shared constants, and accepted capped rate. -/
theorem complete_first_replacement_accepted_sparse_emissions
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s0 := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    match R[v]? with
    | none => True
    | some birth => match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        ∀ k : Fin (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length,
          let r := (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).get k
          let N := v + 1 + k.val
          ∀ i : Fin (p.m - 1),
          match (r.output.followers i).down with
          | none => True
          | some cut => match cut.outcome with
            | .accepted before _after _raw msg scan _registers _lastService =>
              msg = installed.registers.payload.downRecord i ∧
              (r.output.followers i).downInput = some before ∧
              (∀ j : Fin R.length, v ≤ j.val → j.val < N →
                ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i (R.get j)) ∧
              (∀ date : ℕ, msg.val.sigma ≤ date → date < scan.endpoint →
                ActiveFollowerDownAcceptance.bufferArrivalAt p rate msg before date =
                  ((R.take (N + 1)).map (fun x =>
                    SparseCalendarReplay.sparseBufferContribution (p.m - 1)
                      (ConstructorDimensions.D p : ℝ) rate.eta.val msg.val.h
                      (PrelaunchBufferRecovery.downArm rate.eta msg) date
                      (ReferenceFollowerBufferProvenance.logEmission i x))).sum ∧
                ∃ j : Fin R.length,
                  j.val = date - s0 - 1 ∧
                  ActiveFollowerDownAcceptance.bufferArrivalAt p rate msg before date =
                    ReferenceFollowerSparseEmissionRecovery.emissionContribution msg i (R.get j))
            | _ => True
      | _ => True := by
  classical
  have hgeometry := ReferenceFirstReplacementLiveFollowerPrefix.complete_first_replacement_continuing_geometry
    rate source rewards C_star C_h
  have hbudgets := ReferenceFirstReplacementLiveFollowerPrefix.complete_first_replacement_logged_recovery_budgets
    rate source rewards C_star C_h
  have hbirthReadout := ReferenceFirstReplacementNextFollowerStep.complete_first_replacement_birth_live_readout
    rate source rewards C_star C_h
  dsimp only at hgeometry hbudgets hbirthReadout ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s0 := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hgeometry hbudgets hbirthReadout ⊢
    cases hc : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection old ledger clock cutoff outcome =>
      rw [hc] at hgeometry hbudgets hbirthReadout
      cases outcome <;> try trivial
      rename_i core consistent started hs instruction hinstruction output hcons clockData installed arm
      dsimp only [ReferenceActivePhysicalStep.collectionInput]
        at hgeometry hbudgets hbirthReadout ⊢
      intro k
      let r := (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).get k
      let N := v + 1 + k.val
      intro i
      cases hdown : (r.output.followers i).down with
      | none => simp only at hbudgets ⊢
      | some cut =>
        cases houtcome : cut.outcome with
        | skipped before reason => simp only [houtcome] at ⊢
        | inputFailure before reason => simp only [houtcome] at ⊢
        | decodeOrParseRejected before after raw => simp only [houtcome] at ⊢
        | parsedButUnaccepted before after raw msg => simp only [houtcome] at ⊢
        | outputFailure before reason => simp only [houtcome] at ⊢
        | accepted before after raw msg scan registers lastService =>
          simp only [houtcome] at ⊢
          have hbudget := hbudgets k i
          simp only [r, hdown] at hbudget
          obtain ⟨choice, choiceMemory, logged, hprepared, hstatus, hlogging,
            hinput, hcut⟩ := hbudget
          rcases hcut with ⟨hcut, _⟩
          have hgeometryK := hgeometry.2 k
          obtain ⟨hcurrentOption, hcurrentTime, _, _, _, selected, hselected,
            hselectedPayload, _⟩ := hgeometryK
          have hprepAlignment := r.output.preparation.follower_alignment i
          have hprepIndex := hprepAlignment.2.1
          have hdownViewCurrent :
              r.output.preparation.coordinator.downView = some selected.view := by
            change r.output.preparation.coordinator.selection.map
              ReferenceActivePhysicalStep.Selection.view = some selected.view
            rw [hselected]
            rfl
          have htailOption := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R v k
          have hindexBound : N < R.length := by
            have hsome := (List.getElem?_eq_some_iff.mp htailOption).1
            simpa only [N] using hsome
          have hcurrentIndex : R[N]? = some r := by
            simpa only [N, r] using htailOption
          have hcurrentGet : R.get ⟨N, hindexBound⟩ = r := by
            apply Option.some.inj
            have hsome := List.getElem?_eq_some_iff.mpr ⟨hindexBound, by rfl⟩
            exact hsome.symm.trans hcurrentIndex
          have hacceptedRefBefore :
              (ReferenceDownReception.referenceDownCut p
                r.output.preparation.coordinator.downView
                (r.output.preparation.followers.followers i).follower
                (r.output.preparation.followers.followers i).row
                (r.output.preparation.followers.followers i).time
                (r.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).outcome =
                .accepted before after raw msg scan registers lastService := by
            rw [hprepIndex, hprepAlignment.1, hprepAlignment.2.2.1, ← hcut]
            exact houtcome
          have hbeforeCurrent := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_before_eq
            r.output.preparation.coordinator.downView
            (r.output.preparation.followers.followers i).follower
            (r.output.preparation.followers.followers i).row
            (r.output.preparation.followers.followers i).time
            (r.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            logged before after raw msg scan registers lastService hacceptedRefBefore
          have hacceptedRef :
              (ReferenceDownReception.referenceDownCut p
                r.output.preparation.coordinator.downView
                (r.output.preparation.followers.followers i).follower
                (r.output.preparation.followers.followers i).row
                (r.output.preparation.followers.followers i).time
                (r.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).outcome =
                .accepted logged after raw msg scan registers lastService := by
            rw [hbeforeCurrent] at hacceptedRefBefore
            exact hacceptedRefBefore
          have hacceptedRefInput :
              (ReferenceDownReception.referenceDownCut p
                (some selected.view) i r.input.row r.input.time
                (r.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).outcome =
                .accepted logged after raw msg scan registers lastService := by
            simpa [hdownViewCurrent, hprepIndex, hprepAlignment.1,
              hprepAlignment.2.2.1] using hacceptedRef
          have hv : v < R.length := (List.getElem?_eq_some_iff.mp hb).1
          obtain ⟨hcSource, hspanBirth, hbirthActual⟩ :=
            ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h source
              ⟨v, hv⟩
          have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
            rate source rewards C_star C_h hcSource
          let active := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcSource
          let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hcSource
          have hactiveMode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
            rate source rewards C_star C_h active hlaunch
          have hconnected := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
            rate source rewards C_star C_h active hlaunch
          have hcompleteRecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
            rate source rewards C_star C_h active hlaunch
          have hbirthGet : R.get ⟨v, hv⟩ = birth := by
            apply Option.some.inj
            have hsome := List.getElem?_eq_some_iff.mpr ⟨hv, by rfl⟩
            exact hsome.symm.trans hb
          have htimeAt : ∀ j : Fin R.length,
              (R.get j).input.time.val = s0 + j.val := by
            intro j
            obtain ⟨_, _, hactual⟩ :=
              ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h source j
            have htime := congrArg
              (fun x : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
                x.input.time.val) hactual
            simpa [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
              ReferenceActivePhysicalHorizon.roundInputAt] using htime
          have hbirthTime : birth.input.time.val = s0 + v := by
            rw [← hbirthGet]
            exact htimeAt ⟨v, hv⟩
          have hmsgSigma : msg.val.sigma = s0 + v + 1 := by
            have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields
              selected.view i r.input.row r.input.time
              (r.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))
              logged logged after raw msg scan registers lastService hacceptedRefInput
            have hpayloadSigma : selected.view.payload.sigma.val =
                installed.registers.payload.sigma.val :=
              congrArg (fun payload : AssignmentStartPayload.Input p rate.eta =>
                payload.sigma.val) hselectedPayload
            rw [hfields.1, selected.view.payload.downRecord_fields i,
              hpayloadSigma, hgeometry.1, hbirthTime]
          have haccepted := ReferenceFollowerReplyChronology.referenceDownCut_accepted
            r.output.preparation.coordinator.downView
            (r.output.preparation.followers.followers i).follower
            (r.output.preparation.followers.followers i).row
            (r.output.preparation.followers.followers i).time
            (r.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            logged after raw msg scan registers lastService hacceptedRef
          have hstrict : ReferencePrelaunchFollower.acceptedStart logged < msg.val.sigma :=
            haccepted.1.1
          have hloggingFrame := ActiveFollowerLogging.checkedLogging_success_frame
            i
            r.input.row
            (r.input.state.activations i)
            r.input.time
            ((r.output.preparation.followers.followers i).arm,
              r.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            choice logged hlogging
          obtain ⟨incoming, incomingMemory, hinputOrdinary, hreply, _hkeep⟩ :=
            ReferenceFollowerReplyChronology.record_input_to_choice
              r i choice choiceMemory hprepared
          have hreplyLogged :
              ReferenceFollowerReplyChronology.reply logged =
                ReferenceFollowerReplyChronology.reply choice := by
            simp [ReferenceFollowerReplyChronology.reply, hloggingFrame.1,
              hloggingFrame.2.1, hloggingFrame.2.2.1, hloggingFrame.2.2.2.1]
          have hstartIncoming :
              ReferencePrelaunchFollower.acceptedStart incoming < msg.val.sigma := by
            calc
              ReferencePrelaunchFollower.acceptedStart incoming =
                  ReferencePrelaunchFollower.acceptedStart logged :=
                (ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq
                  (hreplyLogged.trans hreply)).symm
              _ < msg.val.sigma := hstrict
          have hgeometryPayload : msg = installed.registers.payload.downRecord i := by
            have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields
              selected.view i r.input.row r.input.time
              (r.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))
              logged logged after raw msg scan registers lastService hacceptedRefInput
            dsimp only [ReferenceActivePhysicalStep.collectionInput] at hselectedPayload ⊢
            rw [hfields.1, hselectedPayload]
          have hbirthSelection :
              ∃ selected : ReferenceActivePhysicalStep.Selection birth.input,
                birth.output.preparation.coordinator.selection = some selected ∧
                selected.view.payload = installed.registers.payload := by
            rcases hbirthReadout with ⟨birthIndex, hbirthIndex, _hbirthRecord,
              selectedBirth, hselectedBirth, hselectedBirthPayload, _⟩
            have hbirthIndexEq : birthIndex = (⟨v, hv⟩ : Fin R.length) :=
              Fin.ext hbirthIndex
            subst birthIndex
            have hselectedBirth' : birth.output.preparation.coordinator.selection =
                some selectedBirth := by
              rw [hc]
              exact hselectedBirth
            exact ⟨selectedBirth, hselectedBirth', hselectedBirthPayload⟩
          have hbirthSelectionAt :
              ∃ selectedAt : ReferenceActivePhysicalStep.Selection (R.get ⟨v, hv⟩).input,
                (R.get ⟨v, hv⟩).output.preparation.coordinator.selection = some selectedAt ∧
                selectedAt.view.payload = installed.registers.payload := by
            rcases hbirthSelection with ⟨selectedAt, hselectedAt, hpayloadAt⟩
            exact hbirthGet.symm ▸ ⟨selectedAt, hselectedAt, hpayloadAt⟩
          have hselectedAt : ∀ j : Fin R.length, v ≤ j.val → j.val < N →
              ∃ selectedAt : ReferenceActivePhysicalStep.Selection (R.get j).input,
                (R.get j).output.preparation.coordinator.selection = some selectedAt ∧
                selectedAt.view.payload = installed.registers.payload := by
            intro j hjlow hjhigh
            by_cases hjbirth : j.val = v
            · have hjeq : j = (⟨v, hv⟩ : Fin R.length) := Fin.ext hjbirth
              subst j
              exact hbirthSelectionAt
            · have hjtail : v + 1 ≤ j.val := by omega
              let q := j.val - (v + 1)
              have hq : q < (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length := by
                have hhigh : j.val < v + 1 + k.val := by simpa [N] using hjhigh
                dsimp [q]
                omega
              let kt : Fin (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length :=
                ⟨q, hq⟩
              obtain ⟨_hgeomIndex, _, _, _, _, selectedAt, hselectedAt,
                hpayloadAt, _⟩ := hgeometry.2 kt
              have hindexEq : v + 1 + kt.val = j.val := by
                simp [kt, q]
                omega
              have hgetOption : R[j.val]? = some
                  ((ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).get kt) := by
                simpa only [hindexEq] using
                  (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R v kt)
              have hgetJ : R[j.val]? = some (R.get j) := by
                apply List.getElem?_eq_some_iff.mpr
                refine ⟨j.isLt, ?_⟩
                simp only [List.get_eq_getElem]
              have hrecordEq : R.get j =
                  (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).get kt :=
                Option.some.inj (hgetJ.symm.trans hgetOption)
              exact hrecordEq.symm ▸ ⟨selectedAt, hselectedAt, hpayloadAt⟩
          have hnoAt : ∀ j : Fin R.length, v ≤ j.val → j.val < N →
              ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i (R.get j) := by
            intro j hjlow hjhigh hreset
            obtain ⟨selectedAt, hselectedAt, hselectedPayload⟩ := hselectedAt j hjlow hjhigh
            obtain ⟨resetCut, hresetDown, resetBefore, resetAfter, resetRaw,
              resetMsg, resetScan, resetRegisters, resetLastService, hresetAccepted⟩ := hreset
            obtain ⟨resetChoice, resetMemory, resetLogged, hresetPrepared, hresetStatus,
              hresetLogging, hresetInput, hresetCut⟩ :=
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
                  .accepted resetBefore resetAfter resetRaw resetMsg resetScan resetRegisters resetLastService := by
              rw [← hresetCut]
              exact hresetAccepted
            have hbeforeEq := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_before_eq
              (R.get j).output.preparation.coordinator.downView
              ((R.get j).output.preparation.followers.followers i).follower
              ((R.get j).output.preparation.followers.followers i).row
              ((R.get j).output.preparation.followers.followers i).time
              ((R.get j).output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))
              resetLogged resetBefore resetAfter resetRaw resetMsg resetScan resetRegisters
              resetLastService hresetRef
            subst resetBefore
            have hdownView :
                (R.get j).output.preparation.coordinator.downView = some selectedAt.view := by
              change (R.get j).output.preparation.coordinator.selection.map
                ReferenceActivePhysicalStep.Selection.view = some selectedAt.view
              simp only [hselectedAt, Option.map_some]
            have hresetIndex := (R.get j).output.preparation.follower_alignment i |>.2.1
            have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields
              selectedAt.view ((R.get j).output.preparation.followers.followers i).follower
              ((R.get j).output.preparation.followers.followers i).row
              ((R.get j).output.preparation.followers.followers i).time
              ((R.get j).output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))
              resetLogged resetLogged resetAfter resetRaw resetMsg resetScan resetRegisters
              resetLastService (by
                rw [← hdownView]
                exact hresetRef)
            have hresetMsgSigma : resetMsg.val.sigma =
                selectedAt.view.payload.sigma.val + 1 := by
              rw [hfields.1, hresetIndex, selectedAt.view.payload.downRecord_fields i]
            have hresetPayloadSigma : selectedAt.view.payload.sigma.val =
                installed.registers.payload.sigma.val :=
              congrArg (fun payload : AssignmentStartPayload.Input p rate.eta =>
                payload.sigma.val) hselectedPayload
            have hresetSigma : resetMsg.val.sigma = msg.val.sigma := by
              rw [hresetMsgSigma, hresetPayloadSigma, hgeometry.1, hbirthTime, hmsgSigma]
            have hinputAtN :
                (R[N]'hindexBound).input.state.followers i =
                  .ordinary incoming incomingMemory := by
              change (R.get ⟨N, hindexBound⟩).input.state.followers i = _
              rw [hcurrentGet]
              exact hinputOrdinary
            have hprefixConnected := ReferenceFollowerReplyChronology.connected_take_to_input
              hconnected N hindexBound
            have hjTake : j.val < (R.take N).length := by
              rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hindexBound)]
              exact hjhigh
            obtain ⟨next, nextMemory, hnext, hnextBound⟩ :=
              ReferenceFollowerReplyChronology.connected_output_chronology hprefixConnected i
                incoming incomingMemory hinputAtN j.val hjTake
            have hnextRecord : (R.get j).output.next.followers i = .ordinary next nextMemory := by
              have htake := List.getElem_take' j.isLt hjhigh
              rw [← htake] at hnext
              simpa only [List.get_eq_getElem] using hnext
            have happlied : ReferenceFollowerReplyChronology.appliedDown (R.get j) i
                resetMsg.val.sigma :=
              ⟨resetLogged, resetCut, resetAfter, resetRaw, resetMsg, resetScan,
                resetRegisters, resetLastService, hresetInput, hresetDown, hresetAccepted, rfl⟩
            obtain ⟨_, _, _, hresetStrict, hresetStart⟩ :=
              ReferenceFollowerReplyChronology.record_appliedDown_strict
                (R.get j) i resetMsg.val.sigma happlied next nextMemory hnextRecord
            omega
          have hintervalResetFree : ∀ record ∈ (R.drop v).take (N - v),
              ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i record := by
            intro record hrecord hreset
            obtain ⟨q, hq, hrecordEq⟩ := List.mem_iff_getElem.mp hrecord
            have hqBound : q < N - v := by
              simp only [List.length_take] at hq
              omega
            have hjBound : v + q < N := by omega
            have hjR : v + q < R.length := by omega
            let j : Fin R.length := ⟨v + q, hjR⟩
            have hrecordAt : ((R.drop v).take (N - v))[q] = R[j.val] := by
              simp only [List.getElem_take, List.getElem_drop]
              simp only [j]
            have hrecordEq' : record = R.get j := by
              calc
                record = ((R.drop v).take (N - v))[q] := hrecordEq.symm
                _ = R[j.val] := hrecordAt
                _ = R.get j := by simp only [List.get_eq_getElem]
            rw [hrecordEq'] at hreset
            exact hnoAt j (by simp [j]) (by simp [j]; omega) hreset
          have hsplitTake : R.take N = R.take v ++ (R.drop v).take (N - v) := by
            calc
              R.take N = R.take (v + (N - v)) := by congr 1; omega
              _ = R.take v ++ (R.drop v).take (N - v) := List.take_add
          have htakeAll : R.take (N + 1) = R.take N ++ [r] := by
            rw [List.take_succ_eq_append_getElem hindexBound]
            have hcurrentElem : R[N]'hindexBound = r := hcurrentGet
            rw [hcurrentElem]
          have hallSplit : R.take (N + 1) =
              R.take v ++ (R.drop v).take (N - v) ++ [r] := by
            rw [htakeAll, hsplitTake]
          have hRlen : R.length = p.T - s0 := by
            simpa [R, s0] using
              ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate source rewards C_star C_h
          have hspanTotal : s0 + (p.T - s0) ≤ p.T := by omega
          have hNtotal : N < p.T - s0 := by rw [← hRlen]; exact hindexBound
          have hspanN : s0 + N ≤ p.T := by omega
          have hspanNNext : s0 + (N + 1) ≤ p.T := by omega
          have hspanV : s0 + v ≤ p.T := by omega
          have hprefixN :
              (ReferenceActivePhysicalHorizon.run active source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s0 N
                hspanN seed.activeAtStart).records = R.take N := by
            calc
              (ReferenceActivePhysicalHorizon.run active source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s0 N
                hspanN seed.activeAtStart).records =
                  (ReferenceActivePhysicalHorizon.run active source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s0
                    (p.T - s0) hspanTotal hactiveMode).records.take N := by
                      symm
                      exact run_records_take active source.1.2
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
                        s0 (p.T - s0) hspanTotal hactiveMode N (by rw [← hRlen]; omega)
              _ = R.take N := by rw [← hcompleteRecords]
          have hprefixV :
              (ReferenceActivePhysicalHorizon.run active source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s0 v
                hspanV seed.activeAtStart).records = R.take v := by
            calc
              (ReferenceActivePhysicalHorizon.run active source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s0 v
                hspanV seed.activeAtStart).records =
                  (ReferenceActivePhysicalHorizon.run active source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s0
                    (p.T - s0) hspanTotal hactiveMode).records.take v := by
                      symm
                      exact run_records_take active source.1.2
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
                        s0 (p.T - s0) hspanTotal hactiveMode v (by rw [← hRlen]; omega)
              _ = R.take v := by rw [← hcompleteRecords]
          have hseedConfig : active.followers i =
              .ordinary (seed.followers i) (seed.memory i) := by
            change (ReferenceFirstLaunchNumericalCell.launchState
              rate source rewards C_star C_h hcSource).followers i = _
            exact seed.configuration i
          have hseedValid : localBufferValid (seed.followers i) := seed.bufferValid i
          have hseedPair : (seed.followers i).buffer.Pairwise
              (fun a b => a.calendarRound < b.calendarRound) := by
            exact seed.chronologicalBuffer i
          have hseedStamps : ∀ saved ∈ (seed.followers i).buffer,
              saved.calendarRound ≤ s0 := by
            simpa only [s0, ReferenceCompletePhysicalHistory.physicalStart,
              ReferenceCompletePhysicalHistory.generatedBoundary,
              ReferenceCompletePhysicalHistory.generatedInput] using seed.bufferStamps i
          obtain ⟨hcN, hspanCanonicalN, hcanonicalN⟩ :=
            ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h source
              ⟨N, hindexBound⟩
          have hcanonicalRecord :
              ReferenceAssignmentPayloadChronology.actualRunRecordAt active source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s0 N
                hspanNNext seed.activeAtStart = r := by
            have hindexed : R.get ⟨N, hindexBound⟩ =
                ReferenceAssignmentPayloadChronology.actualRunRecordAt
                  active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                  rewards s0 N hspanNNext seed.activeAtStart := by
              simpa [active, seed] using hcanonicalN
            exact hindexed.symm.trans hcurrentGet
          have hcanonicalPrepared :
              ((ReferenceAssignmentPayloadChronology.actualRunRecordAt active source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s0 N
                hspanNNext seed.activeAtStart).output.preparation.followers.followers i).configuration =
                .ordinary choice choiceMemory := hcanonicalRecord.symm ▸ hprepared
          have hrunLogging := ReferenceFollowerBufferProvenance.run_logging_ne_error
            i active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards s0 N hspanNNext seed.activeAtStart (seed.followers i) (seed.memory i)
            hseedConfig hseedValid hseedPair hseedStamps choice choiceMemory
            hcanonicalPrepared hstatus
          rcases hrunLogging.1 with ⟨loggedRun, hrunInput, hrunBuffer, _⟩
          have hrunInputCanon :
              ((ReferenceAssignmentPayloadChronology.actualRunRecordAt active source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s0 N
                hspanNNext seed.activeAtStart).output.followers i).downInput = some loggedRun := by
            change _ at hrunInput
            exact hrunInput
          have hrunInput' : (r.output.followers i).downInput = some loggedRun := by
            rw [← hcanonicalRecord]
            exact hrunInputCanon
          have hloggedRunEq : loggedRun = logged := Option.some.inj (hrunInput'.symm.trans hinput)
          have hloggedBuffer : logged.buffer =
              ReferenceFollowerBufferProvenance.bufferFold i (seed.followers i).buffer
                (R.take N) ++ ReferenceFollowerBufferProvenance.logEmission i r := by
            change loggedRun.buffer =
              ReferenceFollowerBufferProvenance.bufferFold i (seed.followers i).buffer
                (ReferenceActivePhysicalHorizon.run active source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s0 N
                  hspanN seed.activeAtStart).records ++
              ReferenceFollowerBufferProvenance.logEmission i
                (ReferenceAssignmentPayloadChronology.actualRunRecordAt active source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s0 N
                  hspanNNext seed.activeAtStart) at hrunBuffer
            rw [hloggedRunEq, hcanonicalRecord, hprefixN] at hrunBuffer
            exact hrunBuffer
          let prefixFold := ReferenceFollowerBufferProvenance.bufferFold i (seed.followers i).buffer
            (R.take v)
          have hfoldSplit : ReferenceFollowerBufferProvenance.bufferFold i (seed.followers i).buffer
                (R.take N) = prefixFold ++
                  ((R.drop v).take (N - v)).flatMap
                    (ReferenceFollowerBufferProvenance.logEmission i) := by
            calc
              ReferenceFollowerBufferProvenance.bufferFold i (seed.followers i).buffer (R.take N) =
                  ReferenceFollowerBufferProvenance.bufferFold i (seed.followers i).buffer
                    (R.take v ++ (R.drop v).take (N - v)) := by rw [hsplitTake]
              _ = ReferenceFollowerBufferProvenance.bufferFold i
                    (ReferenceFollowerBufferProvenance.bufferFold i (seed.followers i).buffer (R.take v))
                    ((R.drop v).take (N - v)) := by
                      simp [ReferenceFollowerBufferProvenance.bufferFold, List.foldl_append]
              _ = prefixFold ++ ((R.drop v).take (N - v)).flatMap
                    (ReferenceFollowerBufferProvenance.logEmission i) :=
                ReferenceFollowerSparseEmissionRecovery.bufferFold_eq_seed_append_emissions_of_no_reset
                  i prefixFold ((R.drop v).take (N - v)) hintervalResetFree
          have hloggedBuffer' : logged.buffer =
              (prefixFold ++ ((R.drop v).take (N - v)).flatMap
                (ReferenceFollowerBufferProvenance.logEmission i)) ++
                ReferenceFollowerBufferProvenance.logEmission i r := by
            rw [hloggedBuffer, hfoldSplit]
          have hprefixFoldBound : ∀ saved ∈ prefixFold, saved.calendarRound ≤ s0 + v := by
            have hsafety := ReferenceFollowerBufferProvenance.run_bufferFold_safety i
              (seed.followers i) active source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
              s0 v hspanV seed.activeAtStart hseedValid hseedPair hseedStamps
            have hsafety' := hsafety.2.2
            rw [hprefixV] at hsafety'
            intro saved hsaved
            exact hsafety' saved hsaved
          have hprefixBufferZero (date : ℕ) (hdate : s0 + v < date) :
              SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg) date
                prefixFold = 0 := by
            apply ReferenceFollowerSparseEmissionRecovery.sparseBufferContribution_zero_of_no_matching_round
            intro saved hsaved heq
            have hstamp := hprefixFoldBound saved hsaved
            omega
          have hinputBefore : (r.output.followers i).downInput = some before := by
            rw [hbeforeCurrent]
            exact hinput
          refine ⟨hgeometryPayload, hinputBefore, hnoAt, ?_⟩
          intro date hdateStart hdateStop
          have houtcomeLogged : cut.outcome =
              .accepted logged after raw msg scan registers lastService := by
            simpa [hbeforeCurrent] using houtcome
          have hactualAccepted :=
            ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
              r i logged cut after raw msg scan registers lastService hinput hdown houtcomeLogged
          have hchecked := ActiveFollowerDownAcceptance.downTransition_accepted_checked p
            (r.output.preparation.followers.followers i).follower
            (r.output.preparation.followers.followers i).row
            (r.output.preparation.followers.followers i).time
            (r.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged after raw msg
            scan registers lastService hactualAccepted
          have hendpoint := hchecked.2.2.2.1
          have hpreparedTime := r.output.preparation.follower_alignment i
          have hlocalTime : (r.output.preparation.followers.followers i).time = r.input.time :=
            hpreparedTime.2.2.1
          have hendpointInput : scan.endpoint ≤ r.input.time.val + 2 := by
            rw [← hlocalTime]
            exact hendpoint
          have hcurrentTimeAbs : r.input.time.val = s0 + N := by
            rw [hcurrentTime, hbirthTime]
            omega
          have hdateUpper : date ≤ s0 + N + 1 := by
            have hbound : date < r.input.time.val + 2 :=
              lt_of_lt_of_le hdateStop hendpointInput
            rw [hcurrentTimeAbs] at hbound
            omega
          have hdateIndex : v ≤ date - s0 - 1 ∧ date - s0 - 1 ≤ N := by
            rw [hmsgSigma] at hdateStart
            omega
          let d := date - s0 - 1
          have hdlt : d < (R.take (N + 1)).length := by
            simp only [List.length_take]
            omega
          have hdR : d < R.length := by omega
          let j : Fin R.length := ⟨d, hdR⟩
          have hdateEq : s0 + d + 1 = date := by
            dsimp [d]
            omega
          have htimesAll : ∀ q (hq : q < (R.take (N + 1)).length),
              ((R.take (N + 1))[q]'hq).input.time.val = s0 + q := by
            intro q hq
            have hqTake : q < N + 1 := by
              simp only [List.length_take] at hq
              omega
            have hqR : q < R.length := by omega
            rw [List.getElem_take]
            exact htimeAt ⟨q, hqR⟩
          have hpreEmissionZero :
              SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg) date
                ((R.take v).flatMap (ReferenceFollowerBufferProvenance.logEmission i)) = 0 := by
            exact ReferenceFollowerSparseEmissionRecovery.emissionFlatMapContribution_zero_of_source_round_ne
              msg i date (R.take v) (by
                intro record hrecord
                obtain ⟨q, hq, hrecordEq⟩ := List.mem_iff_getElem.mp hrecord
                have hqBound : q < v := by
                  simp only [List.length_take] at hq
                  omega
                have hqR : q < R.length := by omega
                have hrecordTime : record.input.time.val = s0 + q := by
                  have htake : (R.take v)[q]'hq = R[q]'hqR :=
                    (List.getElem_take' hqR hqBound).symm
                  rw [← hrecordEq, htake]
                  simpa only [List.get_eq_getElem] using htimeAt ⟨q, hqR⟩
                omega)
          have hprefixFoldZero := hprefixBufferZero date (by rw [hmsgSigma] at hdateStart; omega)
          have hflatDecomposition :
              (R.take (N + 1)).flatMap (ReferenceFollowerBufferProvenance.logEmission i) =
                (R.take v).flatMap (ReferenceFollowerBufferProvenance.logEmission i) ++
                  ((R.drop v).take (N - v)).flatMap
                    (ReferenceFollowerBufferProvenance.logEmission i) ++
                  ReferenceFollowerBufferProvenance.logEmission i r := by
            rw [hallSplit, List.flatMap_append, List.flatMap_append]
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          have hbufferFlat :
              ActiveFollowerDownAcceptance.bufferArrivalAt p rate msg logged date =
                SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                  rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg) date
                  ((R.take (N + 1)).flatMap (ReferenceFollowerBufferProvenance.logEmission i)) := by
            change SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
              rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg) date logged.buffer = _
            rw [hloggedBuffer']
            calc
              SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                  rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg) date
                  ((prefixFold ++ ((R.drop v).take (N - v)).flatMap
                    (ReferenceFollowerBufferProvenance.logEmission i)) ++
                    ReferenceFollowerBufferProvenance.logEmission i r) =
                SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                  rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg) date
                  (((R.take v).flatMap (ReferenceFollowerBufferProvenance.logEmission i) ++
                    ((R.drop v).take (N - v)).flatMap
                      (ReferenceFollowerBufferProvenance.logEmission i)) ++
                    ReferenceFollowerBufferProvenance.logEmission i r) := by
                      rw [SparseCalendarReplay.sparseBufferContribution_append,
                        SparseCalendarReplay.sparseBufferContribution_append,
                        SparseCalendarReplay.sparseBufferContribution_append,
                        SparseCalendarReplay.sparseBufferContribution_append,
                        hprefixFoldZero, hpreEmissionZero]
              _ = SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                  rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg) date
                  ((R.take (N + 1)).flatMap (ReferenceFollowerBufferProvenance.logEmission i)) := by
                    rw [hflatDecomposition]
          have hsumAll := (sparseBufferContribution_flatMap_sum msg i date
            (R.take (N + 1))).symm
          have hbufferSum :
              ActiveFollowerDownAcceptance.bufferArrivalAt p rate msg logged date =
                ((R.take (N + 1)).map (fun x =>
                  SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                    rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg) date
                    (ReferenceFollowerBufferProvenance.logEmission i x))).sum :=
            hbufferFlat.trans hsumAll.symm
          have hcontribution := ReferenceFollowerSparseEmissionRecovery.emissionFlatMapContribution_getElem
            msg i s0 (R.take (N + 1)) d hdlt htimesAll
          rw [hdateEq] at hcontribution
          have hgetTake : (R.take (N + 1)).get ⟨d, hdlt⟩ = R.get j := by
            have hdltN : d < N + 1 := by
              dsimp [d]
              omega
            have htake : (R.take (N + 1))[d]'hdlt = R[d]'hdR :=
              (List.getElem_take' hdR hdltN).symm
            simpa only [List.get_eq_getElem] using htake
          have hbufferEmission :
              ActiveFollowerDownAcceptance.bufferArrivalAt p rate msg logged date =
                ReferenceFollowerSparseEmissionRecovery.emissionContribution msg i (R.get j) := by
            calc
              ActiveFollowerDownAcceptance.bufferArrivalAt p rate msg logged date =
                  SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
                    rate.eta.val msg.val.h (PrelaunchBufferRecovery.downArm rate.eta msg) date
                    ((R.take (N + 1)).flatMap (ReferenceFollowerBufferProvenance.logEmission i)) := hbufferFlat
              _ = ReferenceFollowerSparseEmissionRecovery.emissionContribution msg i
                    ((R.take (N + 1)).get ⟨d, hdlt⟩) := hcontribution
              _ = ReferenceFollowerSparseEmissionRecovery.emissionContribution msg i (R.get j) := by
                    rw [hgetTake]
          refine ⟨?_, ⟨j, ?_, ?_⟩⟩
          · rw [hbeforeCurrent]
            exact hbufferSum
          · simp only [j, d]
          · rw [hbeforeCurrent]
            exact hbufferEmission

end Bandits.Support.ReferenceFirstReplacementAcceptedSparseEmissions

end
