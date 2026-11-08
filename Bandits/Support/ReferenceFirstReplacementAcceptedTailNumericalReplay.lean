/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementNumericalSourceRecovery

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeDrop

/-!
# Accepted DOWN replay in the first replacement's continuing tail

Sources: `sources/zip4/manuscript/06_interruptions.tex:193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This internal result concerns each actual accepted DOWN in the original
continuing tail. Replay starts from the transmitted, possibly nonzero queue.
The endpoint includes both the birth record and the current tail record.
The actual checked recovery supplies all prefix checks; no numerical
predecessor, successful trace, or global interpretation of the initial queue
is an input. Birth initialization, later online induction, cutoff fields,
offered UP truth, and manuscript closure are separate obligations.
-/

@[expose] public section
noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceFirstReplacementLiveFollowerPrefix
open ActiveFollowerDownAcceptance

namespace Bandits.Support.ReferenceFirstReplacementAcceptedTailNumericalReplay

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem first_replacement_stream_eq_cons
    (records : List (RoundRecord (p := p) (rate := rate))) (v : ℕ)
    (birth : RoundRecord (p := p) (rate := rate))
    (hbirth : records[v]? = some birth) :
    (records.drop v).take (1 + (continuingTail records v).length) =
      birth :: continuingTail records v := by
  have hv := (List.getElem?_eq_some_iff.mp hbirth).1
  have hvalue := (List.getElem?_eq_some_iff.mp hbirth).2
  have hdrop : records.drop v = birth :: records.drop (v + 1) := by
    rw [List.drop_eq_getElem_cons hv, hvalue]
  have hprefix : continuingTail records v <+: records.drop (v + 1) :=
    List.takeWhile_prefix _
  have htake := (List.prefix_iff_eq_take.mp hprefix).symm
  rw [hdrop, Nat.one_add, List.take_succ_cons, htake]

/-- The literal cutoff minimum on a live interval. The two inputs describe
the actual grid and earlier public bits, not a proposed scan endpoint. -/
private theorem scan_live_endpoint
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hstart : (downStart p rate M).val ≤ t.val)
    (hgrid : t.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val (downStart p rate M))
    (hbits : ∀ j : Fin p.T, (downStart p rate M).val ≤ j.val → j.val < t.val →
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val row j = false) :
    (acceptedCutoffScan p rate M t hstart row).endpoint = t.val + 2 := by
  classical
  rw [acceptedCutoffScan, FollowerCutoffScan.completeRowCutoffScan,
    FollowerCutoffScan.followerCutoffScan_endpoint_eq_knownCutoff]
  have hempty : FollowerCutoffScan.trueProposalEndpoints
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)
      (FollowerCutoffScan.pastProposalCoordinates p (downStart p rate M) t) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨j, hj, _⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_filter, FollowerCutoffScan.pastProposalCoordinates,
      FollowerCutoffScan.proposalCoordinates, Finset.mem_univ, true_and] at hj
    have hf := hbits j hj.1.1.1 hj.1.2
    rw [hf] at hj
    cases hj.2
  unfold FollowerCutoffScan.knownCutoff FollowerCutoffScan.knownCutoffCarrier
  simp only [hempty]
  apply le_antisymm
  · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  · apply Finset.le_min'
    intro x hx
    simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hx
    rcases hx with rfl | rfl
    · exact le_rfl
    · exact hgrid

/-- Invert the actual ordinary acceptance to identify its scan. No scan
identity or successful recovery is assumed. -/
private theorem accepted_live_endpoint
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (hactual : downTransition p i row t observation rate before =
      .accepted before after raw M scan registers lastService)
    (hgrid : t.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val (downStart p rate M))
    (hbits : ∀ j : Fin p.T, (downStart p rate M).val ≤ j.val → j.val < t.val →
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val row j = false) :
    scan.endpoint = t.val + 2 := by
  unfold downTransition at hactual
  split at hactual
  next hselected =>
    split at hactual
    next hstatus =>
      split at hactual
      next hregisters =>
        split at hactual
        next hbatch =>
          split at hactual
          next hbuffer =>
            dsimp only at hactual
            split at hactual
            next hparsed => cases hactual
            next reply hparsed =>
              split at hactual
              next haccepted =>
                split at hactual
                next failure hfailed => cases hactual
                next recovered hchecked =>
                  cases hactual
                  exact scan_live_endpoint row t M
                    (acceptedDownStartLE p rate M t before haccepted) hgrid hbits
              next hnotaccepted => cases hactual
          next hbuffer => cases hactual
        next hbatch => cases hactual
      next hregisters => cases hactual
    next hstatus => cases hactual
  next hselected => cases hactual

/-- A checked replay of a nonempty prefix gives the precise last service
and retains successful checks on every prefix, including prefix zero.
The sole logical input is the computed checked success on this record list. -/
theorem checkedReplay_take_last_service
    (capacity boundArrival boundQueue : ℕ) (initial : ℕ × ℕ)
    (records : List (Bool × ℕ)) (n : ℕ) (hn : n < records.length)
    (final : ReplayRegisters)
    (hchecked : checkedReplay boundArrival boundQueue capacity 0 ⟨initial, 0⟩
      (records.take (n + 1)) = .ok final) :
    final.registers = QueueReplay.replay capacity initial (records.take (n + 1)) ∧
    final.lastService =
      (QueueReplay.replay capacity initial (records.take (n + 1))).1 -
        (QueueReplay.replay capacity initial (records.take n)).1 ∧
    ∀ b, ∃ middle,
      checkedReplay boundArrival boundQueue capacity 0 ⟨initial, 0⟩
        ((records.take (n + 1)).take b) = .ok middle ∧
      replay_register_domain boundArrival boundQueue middle ∧
      middle.registers = QueueReplay.replay capacity initial
        ((records.take (n + 1)).take b) := by
  have hregisters := (checkedReplay_success boundArrival boundQueue capacity 0
    ⟨initial, 0⟩ final _ hchecked).2.1
  have happend := List.take_concat_get' records n hn
  have hcheckedLast := hchecked
  rw [← happend] at hcheckedLast
  have hservice := checkedReplay_success_last_service boundArrival boundQueue capacity 0
    ⟨initial, 0⟩ final (records.take n) records[n] hcheckedLast
  have hstep : QueueReplay.replay capacity initial (records.take (n + 1)) =
      QueueReplay.transition capacity (QueueReplay.replay capacity initial (records.take n))
        records[n] := by
    rw [← happend, QueueReplay.replay_append]
    rfl
  refine ⟨hregisters, ?_, ?_⟩
  · rw [hstep, hservice]
    cases hbit : records[n].1 <;> simp [QueueReplay.transition, hbit]
  · exact fun b => checkedReplay_success_prefix boundArrival boundQueue capacity 0
      ⟨initial, 0⟩ final _ hchecked b

/-- The before-state in an actual accepted diagnostic is its actual logged
input, even though the diagnostic constructor itself carries both fields. -/
private theorem actual_accepted_downInput
    (record : RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (hdown : (record.output.followers i).down = some cut)
    (haccepted : cut.outcome = .accepted before after raw M scan registers lastService) :
    (record.output.followers i).downInput = some before := by
  obtain ⟨_choice, _memory, logged, _hprepare, _hstatus, _hlogging, hinput, hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i cut hdown
  have haccepted' := haccepted
  rw [hcut] at haccepted'
  have hbefore := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_before_eq
    record.output.preparation.coordinator.downView
    (record.output.preparation.followers.followers i).follower
    (record.output.preparation.followers.followers i).row
    (record.output.preparation.followers.followers i).time
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    logged before after raw M scan registers lastService haccepted'
  rw [hbefore]
  exact hinput

/-- The retained ordinary output comes from the same accepted diagnostic.
The input describes the actual output configuration, not its numerical fields.
Release and finish keep the exact reply fields and the unoccupied-choice
status of the accepted branch. -/
private theorem actual_accepted_finish_frame
    (record : RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (before after next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (hinput : (record.output.followers i).downInput = some before)
    (hdown : (record.output.followers i).down = some cut)
    (haccepted : cut.outcome = .accepted before after raw M scan registers lastService)
    (houtput : (record.output.followers i).configuration = .ordinary next nextMemory) :
    ReferenceFollowerReplyChronology.reply next = ReferenceFollowerReplyChronology.reply after ∧
      next.status = after.status := by
  obtain ⟨choice, memory, logged, hprepare, hstatus, hlogging, hloggedInput, hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i cut hdown
  have hlogged : logged = before := Option.some.inj (hloggedInput.symm.trans hinput)
  subst logged
  let prepared := record.output.preparation.followers.followers i
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hfinish : (finishFollower record.output.preparation.coordinator.downView
      prepared observation).configuration = .ordinary next nextMemory := by
    rw [← ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i record]
    exact houtput
  obtain ⟨choice', memory', post, hprepare', hrecord, hrelease, _, _⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      record.output.preparation.coordinator.downView prepared observation next nextMemory hfinish
  have hchoices := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hprepare'.symm.trans hprepare)
  have hchoiceEq := hchoices.1
  have hmemoryEq := hchoices.2
  subst choice'
  subst memory'
  have hrecordAfter : (recordFollower record.output.preparation.coordinator.downView
      prepared.follower prepared.row prepared.activation prepared.time prepared.active
      prepared.arm observation choice).result = .ok after := by
    dsimp only [prepared, observation]
    simp only [recordFollower, dite_eq_left hstatus, hlogging]
    rw [← hcut, haccepted]
    rfl
  have hpost : post = after := Except.ok.inj (hrecord.symm.trans hrecordAfter)
  subst post
  have hframe := ReferenceFollowerReplyChronology.releaseAndFinish_frame
    prepared.follower prepared.row prepared.time observation choice after next
    memory nextMemory hrelease
  exact ⟨hframe.1, hframe.2 hstatus⟩

/-- Every actual accepted DOWN in the first replacement's continuing tail
installs the replay of the original numerical source cells through that round.
There are no logical premises beyond the common execution parameters.
All nonaccepted diagnostic branches retain their literal, vacuous scope. -/
theorem complete_first_replacement_accepted_tail_numerical_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    match R[v]? with
    | none => True
    | some birth => match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        let tail := continuingTail R v
        let X := (R.drop v).take (1 + tail.length)
        let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
        ∀ k : Fin tail.length, let r := tail.get k
          ∀ i : Fin (p.m - 1),
          let M := payload.downRecord i
          let a := payload.assignment.assigned i
          let A := fun b => (C.take b).map (fun c =>
            (true, RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))
          let Q := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q) (A b)
          match (r.output.followers i).down with
          | none => True
          | some cut => match cut.outcome with
            | .accepted before after _raw msg scan registers lastService =>
              msg = M ∧ (r.output.followers i).downInput = some before ∧
              scan.endpoint = r.input.time.val + 2 ∧
              scan.endpoint - msg.val.sigma = k.val + 2 ∧
              registers = Q (k.val + 2) ∧
              lastService = (Q (k.val + 2)).1 - (Q (k.val + 1)).1 ∧
              after.lastDown = some M ∧ (after.S, after.backlog) = Q (k.val + 2) ∧
              after.delta = lastService ∧ after.buffer = [] ∧
              ∃ next nextMemory,
                (r.output.followers i).configuration = .ordinary next nextMemory ∧
                (r.output.followers i).failure = none ∧ next.status ≠ .unoccupied ∧
                next.lastDown = some M ∧ (next.S, next.backlog) = Q (k.val + 2) ∧
                next.delta = lastService ∧
                ReferenceAcceptedUpFollowerHistory.RetainedDown r i M
            | _ => True
      | _ => True := by
  classical
  have hsource :=
    ReferenceFirstReplacementNumericalSourceRecovery.complete_first_replacement_numerical_source_stream
      rate source rewards C_star C_h
  have hgeometry := complete_first_replacement_continuing_geometry
    rate source rewards C_star C_h
  have hboundary :=
    ReferenceFirstReplacementFollowerBoundary.complete_first_replacement_follower_boundary
      rate source rewards C_star C_h
  dsimp only at hsource hgeometry hboundary ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hsource hgeometry hboundary ⊢
    cases hc : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection old ledger clock cutoff outcome =>
      rw [hc] at hsource hgeometry hboundary
      cases outcome <;> try trivial
      rename_i core consistent started hs instruction hi output hcons clockData installed arm
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at *
      let tail := continuingTail R v
      let X := (R.drop v).take (1 + tail.length)
      let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
      obtain ⟨hlength, _hcells, hrecover⟩ := hsource
      have hstream : X = birth :: tail := first_replacement_stream_eq_cons R v birth hb
      have hClength : C.length = tail.length + 1 := by
        calc
          C.length = X.length := hlength
          _ = tail.length + 1 := by rw [hstream]; rfl
      intro k i
      let r := tail.get k
      let M := installed.registers.payload.downRecord i
      let a := installed.registers.payload.assignment.assigned i
      let records := C.map (fun c => (true, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))
      let Q := fun b => QueueReplay.replay (4 * rate.n) (0, M.val.q) (records.take b)
      have hrec : match (r.output.followers i).down with
          | none => True
          | some cut => match cut.outcome with
            | .accepted before _after _raw msg scan _registers _lastService =>
              msg = M ∧ recoveryQueueRecords p rate msg before scan.endpoint =
                (C.take (scan.endpoint - msg.val.sigma)).map (fun c =>
                  (true, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))
            | _ => True := hrecover k i
      cases hdown : (r.output.followers i).down with
      | none => trivial
      | some cut =>
        simp only [hdown] at hrec
        cases houtcome : cut.outcome with
        | skipped _ _ => simp only [houtcome]
        | inputFailure _ _ => simp only [houtcome]
        | decodeOrParseRejected _ _ _ => simp only [houtcome]
        | parsedButUnaccepted _ _ _ _ => simp only [houtcome]
        | outputFailure _ _ => simp only [houtcome]
        | accepted before after raw msg scan registers lastService =>
          simp only [houtcome] at hrec
          simp only [houtcome]
          obtain ⟨hmessage, hqueue⟩ := hrec
          have hinput := actual_accepted_downInput r i cut before after raw msg scan
            registers lastService hdown houtcome
          have hactual := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
            r i before cut after raw msg scan registers lastService hinput hdown houtcome
          have halign := r.output.preparation.follower_alignment i
          have hactual' : downTransition p i r.input.row r.input.time
              (r.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate before =
              .accepted before after raw msg scan registers lastService := by
            simpa only [halign.1, halign.2.1, halign.2.2.1] using hactual
          have hchecked := downTransition_accepted_checked p i r.input.row r.input.time
            (r.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            rate before after raw msg scan registers lastService hactual'
          obtain ⟨_, htime, _, _, _, _⟩ := hgeometry.2 k
          obtain ⟨_, _, _, _, selected, _hselection, _hpayload, _hlive, hgrid,
            hbits, hfollowers⟩ := hboundary k
          have hstart : downStart p rate msg = installed.registers.payload.sigma := by
            rw [hmessage]
            apply Fin.ext
            change installed.registers.payload.sigma.val + 1 - 1 =
              installed.registers.payload.sigma.val
            exact Nat.add_sub_cancel _ _
          have hendpoint : scan.endpoint = r.input.time.val + 2 :=
            accepted_live_endpoint i r.input.row r.input.time
              (r.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))
              before after raw msg scan registers lastService hactual'
              (by rw [hstart]; exact hgrid) (by rw [hstart]; exact hbits)
          have hsigma : msg.val.sigma = birth.input.time.val + 1 := by
            rw [hmessage]
            change installed.registers.payload.sigma.val + 1 = birth.input.time.val + 1
            rw [hgeometry.1]
          have hcount : scan.endpoint - msg.val.sigma = k.val + 2 := by
            rw [hendpoint, hsigma, htime]
            omega
          have hqueue' : recoveryQueueRecords p rate msg before scan.endpoint =
              records.take (k.val + 2) := by
            simpa only [hcount, records, a, List.map_take] using hqueue
          have hcheckedReplay : checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
              ⟨(0, msg.val.q), 0⟩ (records.take (k.val + 2)) =
              .ok ⟨registers, lastService⟩ := by
            have h := hchecked.2.1
            rw [checkedRecovery_eq_checkedReplay, hqueue'] at h
            exact h
          have hn : k.val + 1 < records.length := by
            simp only [records, List.length_map, hClength]
            have hk : k.val < tail.length := k.isLt
            omega
          obtain ⟨hregisters, hservice, _hprefixChecks⟩ :=
            checkedReplay_take_last_service (4 * rate.n) (D p) (p.T * D p)
              (0, msg.val.q) records (k.val + 1) hn ⟨registers, lastService⟩ hcheckedReplay
          have hregistersQ : registers = Q (k.val + 2) := by
            simpa only [Q, M, ← hmessage] using hregisters
          have hserviceQ : lastService = (Q (k.val + 2)).1 - (Q (k.val + 1)).1 := by
            simpa only [Q, M, ← hmessage] using hservice
          have hafter := hchecked.2.2.2.2.2.2
          have hafterLast : after.lastDown = some M := by rw [hafter, hmessage]; rfl
          have hafterPair : (after.S, after.backlog) = Q (k.val + 2) := by
            rw [hafter]
            exact hregistersQ
          have hafterDelta : after.delta = lastService := by rw [hafter]
          have hafterBuffer : after.buffer = [] := by rw [hafter]
          have hafterStatus : after.status = .pending := by
            rw [hafter]
            simp only [hendpoint, ite_true]
          obtain ⟨_state, _memory, next, nextMemory, _hinputState, _hdomain, _hmass,
            _hzero, _hstrict, _hbusy, _hpair, _hbefore, _hstamp, _hstart, _hcredit,
            _hdecision, _hprepare, houtput, hfailure, _hflag, _hnextDomain,
            _hnextMass, _hnextDelta, _hnextZero, _hnextStrict, _hnextBusy,
            _hpersist⟩ := hfollowers i
          have hframe := actual_accepted_finish_frame r i cut before after next nextMemory
            raw msg scan registers lastService hinput hdown houtcome houtput
          have hfields := hframe.1
          simp only [ReferenceFollowerReplyChronology.reply, Prod.mk.injEq] at hfields
          have hnextLast : next.lastDown = some M := hfields.1.trans hafterLast
          have hnextPair : (next.S, next.backlog) = Q (k.val + 2) := by
            rw [hfields.2.1, hfields.2.2.2]
            exact hafterPair
          have hnextDelta : next.delta = lastService := hfields.2.2.1.trans hafterDelta
          have hnextBusy : next.status ≠ .unoccupied := by
            rw [hframe.2, hafterStatus]
            intro h
            cases h
          have hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown r i M := by
            refine ⟨before, cut, after, raw, scan, registers, lastService, hinput, hdown, ?_⟩
            simpa only [M, ← hmessage] using houtcome
          change msg = M ∧ _
          refine ⟨hmessage, hinput, hendpoint, hcount, ?_, ?_, hafterLast, ?_,
            hafterDelta, hafterBuffer, next, nextMemory, houtput, hfailure,
            hnextBusy, hnextLast, ?_, hnextDelta, hretained⟩
          · simpa only [ReferenceActivePhysicalStep.collectionInput, Q, records, M, a, C, X, tail,
              List.map_take] using hregistersQ
          · simpa only [ReferenceActivePhysicalStep.collectionInput, Q, records, M, a, C, X, tail,
              List.map_take] using hserviceQ
          · simpa only [ReferenceActivePhysicalStep.collectionInput, Q, records, M, a, C, X, tail,
              List.map_take] using hafterPair
          · simpa only [ReferenceActivePhysicalStep.collectionInput, Q, records, M, a, C, X, tail,
              List.map_take] using hnextPair

end Bandits.Support.ReferenceFirstReplacementAcceptedTailNumericalReplay
end
