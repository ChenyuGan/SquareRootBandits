/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceAcceptedUpFollowerHistory
public import Bandits.Support.ReferenceSelectedPayloadChronology
public import Bandits.Support.ReferenceActiveDataOwnership

/-!
# Prior DOWN records for an actual retained collection

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:94-108`,
`sources/zip4/manuscript/06_interruptions.tex:270-284,327-348`, and
`sources/zip4/manuscript/05_binary_transport.tex:87-124`.

For a missing pending label in an actual retained collection, the computed
collection history gives a real accepted UP. The accepted-UP chronology
provider then gives its earlier applied DOWN. The continuation below relates
that history to the actual next physical choice and the actual continuing
collection dispatch. No supplied trace, sender word, or selected payload is
used as an input.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferencePrelaunchFollower
open DeclaredFollowerLocalRound
open ReferenceActivePhysicalHorizon
open ReferenceActivePhysicalStep

namespace Bandits.Support.ReferenceCollectionPriorDownHistory

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev Label (p : Parameters) := Fin (p.m - 1)
abbrev Record {p : Parameters} {rate : RateInput p} :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev DownRecord {p : Parameters} {rate : RateInput p} :=
  OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

variable {p : Parameters} {rate : RateInput p}

/-- The actual chronological witnesses and logged-choice conclusion for a
missing-pending label in a continuing collection dispatch. -/
def ContinuingPriorDownGuard
    (initial : ReferenceActivePhysicalStep.State p rate)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (whole : ReferenceActivePhysicalHorizon.Run initial)
    (count : ℕ)
    (i : Label p) (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (current : ReferencePrelaunchFollower.State p rate.eta) : Prop :=
  ∃ (j k : ℕ)
    (hjRun : j < whole.records.length)
    (hkRun : k < whole.records.length)
    (message : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (prior : DownRecord)
    (sender : DeclaredFollowerLocalRound.PreparedRound p rate)
    (upState : ReferencePrelaunchFollower.State p rate.eta)
    (upMemory : ActiveFollowerLifecycle.LocalMemory p),
    j < k ∧ k < count ∧
    ReferenceCollectionPhaseHistory.AcceptedUp (whole.records[k]'hkRun).input i message ∧
    ReferenceAcceptedUpFollowerHistory.RetainedDown (whole.records[j]'hjRun) i prior ∧
    ReferenceFollowerReplyChronology.appliedDown
      (whole.records[j]'hjRun) i prior.val.sigma ∧
    prior.val.sigma = message.val.sigma ∧ message.val.sigma = ledger.sigma ∧
    sender = ReferenceFollowerFixedReply.actualChoice (whole.records[k]'hkRun) i ∧
    sender.configuration = .ordinary upState upMemory ∧ upState.status = .unoccupied ∧
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta sender.follower sender.row
      sender.activation sender.time upState = .offer message ∧
    message.val.sigma = ReferencePrelaunchFollower.acceptedStart upState ∧
    upState.lastDown = some prior ∧ 0 < message.val.sigma ∧
    prior = payload.downRecord i ∧
    ledger.sigma = CoordinatorRecorderComplementBridge.sourceStart payload ∧
    payload.sigma.val + 1 ≤ ReferencePrelaunchFollower.acceptedStart current ∧
    ∀ (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
      ((ReferenceActivePhysicalStep.step x).followers i).downInput = some logged →
      ((ReferenceActivePhysicalStep.step x).followers i).down = some cut →
      ReferencePrelaunchFollower.acceptedStart logged =
        ReferencePrelaunchFollower.acceptedStart current ∧
      cut = ReferenceDownReception.referenceDownCut p
        (ReferenceActivePhysicalStep.prepare x).coordinator.downView i x.row
        ((ReferenceActivePhysicalStep.prepare x).followers.followers i).time
        ((ReferenceActivePhysicalStep.prepare x).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
      ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
        ((ReferenceActivePhysicalStep.prepare x).followers.followers i).time logged
        (some (payload.downRecord i)) = False

private theorem missing_pending_has_acceptedUp
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hcollection : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).finalState.coordinator = .collection payload ledger proposal)
    (i : Label p) (hmissing : i ∉ ledger.pending) :
    ∃ (k : ℕ) (hkRun : k <
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start count hspan hmode).records.length),
      k < count ∧
      ∃ message : ReferenceCollectionPhaseHistory.UpRecord p rate,
        ReferenceCollectionPhaseHistory.AcceptedUp
          ((ReferenceActivePhysicalHorizon.run initial rows selected rewards
            start count hspan hmode).records[k]'hkRun).input i message ∧
        message.val.sigma = ledger.sigma := by
  obtain ⟨before, cutoff, during, hrecords, hbefore, hcutoff, hwindow,
      hpending, hnodup, hlabels⟩ :=
    ReferenceCollectionPhaseHistory.run_collection_pending_exact
      initial rows selected rewards start count hspan hmode hfirst
      payload ledger proposal hcollection
  have hlabelFin : i ∈ (ReferenceCollectionPhaseHistory.acceptedLabels
      (cutoff :: during)).toFinset := by
    by_contra hnot
    apply hmissing
    rw [hpending]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hnot⟩
  have hlabelList : i ∈ ReferenceCollectionPhaseHistory.acceptedLabels
      (cutoff :: during) := List.mem_toFinset.mp hlabelFin
  have hlabelMap : i ∈ (cutoff :: during).filterMap
      (fun record => ReferenceCollectionPhaseHistory.acceptedLabel record.input) := by
    simpa only [ReferenceCollectionPhaseHistory.acceptedLabels] using hlabelList
  obtain ⟨oldRecord, holdRecord, hacceptedLabel⟩ := List.mem_filterMap.mp hlabelMap
  obtain ⟨message, haccepted, hmessageSigma⟩ :=
    hlabels oldRecord holdRecord i hacceptedLabel
  obtain ⟨offset, hoffset, hget⟩ := List.mem_iff_getElem.mp holdRecord
  have hlength := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start count hspan hmode
  rw [hrecords, List.length_append, List.length_cons] at hlength
  have hcountEq : before.length + (during.length + 1) = count := by
    simpa only [List.length_append, List.length_cons] using hlength
  have hoffsetLe : offset ≤ during.length := by
    simp only [List.length_cons] at hoffset
    omega
  have hk : before.length + offset < count := by omega
  have hkRun : before.length + offset <
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).records.length := by
    rw [hrecords, List.length_append, List.length_cons]
    omega
  have hgetRecord? : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records[before.length + offset]? = some oldRecord := by
    rw [hrecords, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hoffset, hget]
  have hrunGet? := List.getElem?_eq_getElem hkRun
  rw [hgetRecord?] at hrunGet?
  have hgetRecord : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records[before.length + offset] = oldRecord :=
    Option.some.inj hrunGet?.symm
  have hacceptedAt : ReferenceCollectionPhaseHistory.AcceptedUp
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).records[before.length + offset]'hkRun |>.input) i message := by
    rw [hgetRecord]
    exact haccepted
  exact ⟨before.length + offset, hkRun, hk, message, hacceptedAt, hmessageSigma⟩

private theorem accepted_reference_cut_has_view
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Label p) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (input before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (message : DownRecord) (scan : FollowerCutoffScan.ScanResult p.T)
    (registers : ℕ × ℕ) (lastService : ℕ)
    (haccepted : (ReferenceDownReception.referenceDownCut p view i row t observation
      rate input).outcome = .accepted before after raw message scan registers lastService) :
    ∃ selected, view = some selected := by
  cases view with
  | some selected => exact ⟨selected, rfl⟩
  | none =>
      by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i row t
      · by_cases hstatus : input.status = .unoccupied
        · by_cases hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate input
          · by_cases hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p input.downBatch
            · by_cases hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p input.buffer
              · let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
                  p i row t observation rate input
                have hcut : (ReferenceDownReception.referenceDownCut p
                    (none : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)) i row t
                    observation rate input).outcome =
                    .decodeOrParseRejected input { input with downBatch := decoded.1 } decoded.2 := by
                  cases hraw : decoded.2 <;>
                    simp [ReferenceDownReception.referenceDownCut,
                      ReferenceDownReception.expectedDownFlatWord,
                      ReferenceDownReception.ordinaryParse,
                      OrdinaryMessageCodec.parseDown, Option.map, hselected, hstatus,
                      hregisters, hbatch, hbuffer, decoded, hraw]
                rw [hcut] at haccepted
                cases haccepted
              · have hcut : (ReferenceDownReception.referenceDownCut p
                    (none : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)) i row t
                    observation rate input).outcome = .inputFailure input .sparseBuffer := by
                  simp [ReferenceDownReception.referenceDownCut,
                    ReferenceDownReception.expectedDownFlatWord, hselected, hstatus,
                    hregisters, hbatch, hbuffer]
                rw [hcut] at haccepted
                cases haccepted
            · have hcut : (ReferenceDownReception.referenceDownCut p
                  (none : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)) i row t
                  observation rate input).outcome = .inputFailure input .decoderBatch := by
                simp [ReferenceDownReception.referenceDownCut,
                  ReferenceDownReception.expectedDownFlatWord, hselected, hstatus,
                  hregisters, hbatch]
              rw [hcut] at haccepted
              cases haccepted
          · have hcut : (ReferenceDownReception.referenceDownCut p
                (none : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)) i row t
                observation rate input).outcome = .inputFailure input .registers := by
              simp [ReferenceDownReception.referenceDownCut,
                ReferenceDownReception.expectedDownFlatWord, hselected, hstatus,
                hregisters]
            rw [hcut] at haccepted
            cases haccepted
        · have hcut : (ReferenceDownReception.referenceDownCut p
              (none : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)) i row t
              observation rate input).outcome = .skipped input .occupiedAtChoice := by
            simp [ReferenceDownReception.referenceDownCut,
              ReferenceDownReception.expectedDownFlatWord, hselected, hstatus]
          rw [hcut] at haccepted
          cases haccepted
      · have hcut : (ReferenceDownReception.referenceDownCut p
            (none : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)) i row t
            observation rate input).outcome = .skipped input .notSelectedDown := by
          simp [ReferenceDownReception.referenceDownCut,
            ReferenceDownReception.expectedDownFlatWord, hselected]
        rw [hcut] at haccepted
        cases haccepted

private theorem finishFollower_record_fields
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary state memory) :
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput =
        (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation state).downInput ∧
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).down =
        (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation state).down := by
  cases hresult : (ReferenceActivePhysicalStep.recordFollower view prepared.follower
      prepared.row prepared.activation prepared.time prepared.active prepared.arm
      observation state).result with
  | error failure => simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hresult]
  | ok post =>
      cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
          prepared.row prepared.time observation state memory post with
      | error failure => simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hresult, hfinish]
      | ok pair => simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hresult, hfinish]

private theorem actual_logged_down_source
    (record : Record) (i : Label p)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hinput : (record.output.followers i).downInput = some logged)
    (hdown : (record.output.followers i).down = some cut) :
    ∃ choice memory,
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
        .ordinary choice memory ∧
      choice.status = .unoccupied ∧
      ActiveFollowerLogging.checkedLogging i record.input.row
        ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).activation
        ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).time
        (((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).arm,
          (ReferenceActivePhysicalStep.prepare record.input).feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice = .ok logged ∧
      cut = ReferenceDownReception.referenceDownCut p
        (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView i
        record.input.row ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).time
        ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged := by
  rcases record with ⟨input, output, houtput⟩
  cases houtput
  let prepared := ReferenceActivePhysicalStep.prepare input
  let follower := prepared.followers.followers i
  let observation := prepared.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hfinishInput :
      (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView follower
        observation).downInput = some logged := by
    simpa only [ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower, prepared, follower,
      observation] using hinput
  have hfinishDown :
      (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView follower
        observation).down = some cut := by
    simpa only [ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.PreparedRound.observeFollower, prepared, follower,
      observation] using hdown
  cases hconfiguration : follower.configuration with
  | dagger => simp [ReferenceActivePhysicalStep.finishFollower, hconfiguration] at hfinishInput
  | ordinary choice memory =>
    have hfields := finishFollower_record_fields prepared.coordinator.downView follower
      observation choice memory hconfiguration
    have hrecordInput :
        (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView follower.follower
          follower.row follower.activation follower.time follower.active follower.arm observation
          choice).downInput = some logged := hfields.1.symm.trans hfinishInput
    have hrecordDown :
        (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView follower.follower
          follower.row follower.activation follower.time follower.active follower.arm observation
          choice).down = some cut := hfields.2.symm.trans hfinishDown
    have halignment := prepared.follower_alignment i
    have hrecordInput' :
        (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView i input.row
          follower.activation follower.time follower.active follower.arm observation
          choice).downInput = some logged := by
      simpa only [prepared, follower, halignment.1, halignment.2.1] using hrecordInput
    have hrecordDown' :
        (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView i input.row
          follower.activation follower.time follower.active follower.arm observation
          choice).down = some cut := by
      simpa only [prepared, follower, halignment.1, halignment.2.1] using hrecordDown
    by_cases hstatus : choice.status = .unoccupied
    · cases hlogging : ActiveFollowerLogging.checkedLogging i input.row follower.activation
        follower.time (follower.arm, observation) choice with
      | error failure =>
          simp [ReferenceActivePhysicalStep.recordFollower, hstatus, hlogging] at hrecordInput'
      | ok actualLogged =>
          have hlogged : actualLogged = logged := by
            have h := hrecordInput'
            simpa [ReferenceActivePhysicalStep.recordFollower, hstatus, hlogging] using h
          subst actualLogged
          have hcut : ReferenceDownReception.referenceDownCut p prepared.coordinator.downView i
              input.row follower.time observation rate logged = cut := by
            simpa [ReferenceActivePhysicalStep.recordFollower, hstatus, hlogging] using hrecordDown'
          exact ⟨choice, memory, rfl, hstatus, hlogging, hcut.symm⟩
    · simp [ReferenceActivePhysicalStep.recordFollower, hstatus] at hrecordInput'

/-- A missing label in the actual final collection ledger has a real
strictly-earlier applied DOWN and an actual accepted-UP sender choice in the
same computed prefix. The initial hypothesis concerns only this follower.
-/
theorem run_collection_missing_pending_prior_down
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (i : Label p)
    (first : ReferencePrelaunchFollower.State p rate.eta)
    (firstMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfirstFollower : initial.followers i = .ordinary first firstMemory)
    (hfirstNoDown : first.lastDown = none)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hcollection : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).finalState.coordinator = .collection payload ledger proposal)
    (hmissing : i ∉ ledger.pending) :
    ∃ (j k : ℕ)
      (hjRun : j < (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).records.length)
      (hkRun : k < (ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).records.length)
      (message : ReferenceCollectionPhaseHistory.UpRecord p rate)
      (prior : DownRecord) (sender : DeclaredFollowerLocalRound.PreparedRound p rate)
      (upState : ReferencePrelaunchFollower.State p rate.eta)
      (upMemory : ActiveFollowerLifecycle.LocalMemory p),
      j < k ∧ k < count ∧
      ReferenceCollectionPhaseHistory.AcceptedUp
        (((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
          hspan hmode).records[k]'hkRun).input) i message ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
          hspan hmode).records[j]'hjRun) i prior ∧
      ReferenceFollowerReplyChronology.appliedDown
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
          hspan hmode).records[j]'hjRun) i prior.val.sigma ∧
      prior.val.sigma = message.val.sigma ∧ message.val.sigma = ledger.sigma ∧
      sender = ReferenceFollowerFixedReply.actualChoice
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
          hspan hmode).records[k]'hkRun) i ∧
      sender.configuration = .ordinary upState upMemory ∧
      upState.status = .unoccupied ∧
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta sender.follower sender.row
        sender.activation sender.time upState = .offer message ∧
      message.val.sigma = ReferencePrelaunchFollower.acceptedStart upState ∧
      upState.lastDown = some prior ∧
      0 < message.val.sigma := by
  obtain ⟨k, hkRun, hk, message, haccepted, hmessageSigma⟩ :=
    missing_pending_has_acceptedUp initial rows selected rewards start count hspan hmode
      hfirst payload ledger proposal hcollection i hmissing
  let kFin : Fin (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records.length := ⟨k, hkRun⟩
  obtain ⟨j, hjk, prior, hretained, happlied, hpriorSigma,
      sender, upState, upMemory, hsender, hconfiguration, hunoccupied, hoff,
      hstart, hstarted, hS, hdelta, hbacklog, hlast, hlastSigma, hpositive⟩ :=
    ReferenceAcceptedUpFollowerHistory.run_acceptedUp_prior_down
      initial rows selected rewards start count hspan hmode i first firstMemory
      hfirstFollower hfirstNoDown kFin message haccepted
  have hjRun : j.val < (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records.length := j.isLt
  have hjkNat : j.val < k := by simpa only [kFin, Fin.val_mk] using hjk
  exact ⟨j.val, k, hjRun, hkRun, message, prior, sender, upState, upMemory,
    hjkNat, hk,
    haccepted, hretained, happlied, hpriorSigma, hmessageSigma,
    hsender, hconfiguration, hunoccupied, hoff, hstart, hlast, hpositive⟩

/-- Extending the actual retained-collection prefix by its actual next round
preserves the accepted-UP and earlier applied-DOWN indices and compares that
sender's accepted start with this follower's current prepared ordinary choice.
-/
theorem run_collection_missing_pending_current_start_mono
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (i : Label p)
    (first : ReferencePrelaunchFollower.State p rate.eta)
    (firstMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfirstFollower : initial.followers i = .ordinary first firstMemory)
    (hfirstNoDown : first.lastDown = none)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hcollection : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count (by omega) hmode).finalState.coordinator = .collection payload ledger proposal)
    (hmissing : i ∉ ledger.pending)
    (current : ReferencePrelaunchFollower.State p rate.eta)
    (currentMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hcurrent : ((ReferenceActivePhysicalStep.prepare
      (ReferenceCollectionPhaseHistory.nextInput initial rows selected rewards start count
        hspan hmode)).followers.followers i).configuration = .ordinary current currentMemory) :
    ∃ (j k : ℕ)
      (hjRun : j < (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        (count + 1) hspan hmode).records.length)
      (hkRun : k < (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        (count + 1) hspan hmode).records.length)
      (message : ReferenceCollectionPhaseHistory.UpRecord p rate)
      (prior : DownRecord) (sender : DeclaredFollowerLocalRound.PreparedRound p rate)
      (upState : ReferencePrelaunchFollower.State p rate.eta)
      (upMemory : ActiveFollowerLifecycle.LocalMemory p),
      j < k ∧ k < count ∧
      ReferenceCollectionPhaseHistory.AcceptedUp
        (((ReferenceActivePhysicalHorizon.run initial rows selected rewards start
          (count + 1) hspan hmode).records[k]'hkRun).input) i message ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start
          (count + 1) hspan hmode).records[j]'hjRun) i prior ∧
      ReferenceFollowerReplyChronology.appliedDown
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start
          (count + 1) hspan hmode).records[j]'hjRun) i prior.val.sigma ∧
      prior.val.sigma = message.val.sigma ∧ message.val.sigma = ledger.sigma ∧
      sender = ReferenceFollowerFixedReply.actualChoice
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start
          (count + 1) hspan hmode).records[k]'hkRun) i ∧
      sender.configuration = .ordinary upState upMemory ∧
      upState.status = .unoccupied ∧
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta sender.follower sender.row
        sender.activation sender.time upState = .offer message ∧
      message.val.sigma = ReferencePrelaunchFollower.acceptedStart upState ∧
      upState.lastDown = some prior ∧
      0 < message.val.sigma ∧
      ledger.sigma ≤ ReferencePrelaunchFollower.acceptedStart current := by
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
    (by omega) hmode
  let whole := ReferenceActivePhysicalHorizon.run initial rows selected rewards start
    (count + 1) hspan hmode
  let x := ReferenceCollectionPhaseHistory.nextInput initial rows selected rewards start count
    hspan hmode
  have hprefixCollection : prefixRun.finalState.coordinator = .collection payload ledger proposal := by
    simpa [prefixRun] using hcollection
  have hprefixSpan : start + count ≤ p.T := by omega
  obtain ⟨j₀, k₀, hj₀Run, hk₀Run, message, prior, sender, upState, upMemory,
      hjk, hkcount,
      haccepted, hretained, happlied, hpriorSigma, hmessageSigma,
      hsender, hconfiguration, hunoccupied, hoff, hstart, hlast, hpositive⟩ :=
    run_collection_missing_pending_prior_down initial rows selected rewards start count
      hprefixSpan hmode hfirst i first firstMemory hfirstFollower hfirstNoDown
      payload ledger proposal hprefixCollection hmissing
  have hQprefix := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start count 1 hspan hmode
  obtain ⟨suffix, hQprefix⟩ := hQprefix
  have hwholeLength := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start (count + 1) hspan hmode
  have hj₀count : j₀ < count := Nat.lt_trans hjk hkcount
  let kFin : Fin whole.records.length := ⟨k₀, by rw [hwholeLength]; omega⟩
  let last : Fin whole.records.length := ⟨count, by rw [hwholeLength]; omega⟩
  have hprefixLength := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start count (by omega) hmode
  have hj₀Prefix : j₀ < prefixRun.records.length := by
    rw [hprefixLength]
    exact Nat.lt_trans hjk hkcount
  have hk₀Prefix : k₀ < prefixRun.records.length := by
    rw [hprefixLength]
    exact hkcount
  have hj₀Whole : j₀ < whole.records.length := by rw [hwholeLength]; omega
  have hk₀Whole : k₀ < whole.records.length := by rw [hwholeLength]; omega
  have hrecordPrefix (n : ℕ) (hn : n < prefixRun.records.length)
      (hnWhole : n < whole.records.length) :
      whole.records[n]'hnWhole = prefixRun.records[n]'hn := by
    have hopt : whole.records[n]? = some (prefixRun.records[n]'hn) := by
      rw [hQprefix, List.getElem?_append_left hn, List.getElem?_eq_getElem hn]
    rw [List.getElem?_eq_getElem hnWhole] at hopt
    exact Option.some.inj hopt
  have hrecordJ : whole.records[j₀]'hj₀Whole = prefixRun.records[j₀]'hj₀Prefix :=
    hrecordPrefix j₀ hj₀Prefix hj₀Whole
  have hrecordK : whole.records[k₀]'hk₀Whole = prefixRun.records[k₀]'hk₀Prefix :=
    hrecordPrefix k₀ hk₀Prefix hk₀Whole
  have hRStep := ReferenceActivePhysicalHorizon.run_successor_step
    initial rows selected rewards start count hspan hmode
  let currentRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
    ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩
  have hcurrentRecord : whole.records[count]'last.isLt = currentRecord := by
    have hrecords := congrArg ReferenceActivePhysicalHorizon.Run.records hRStep
    have hopt : whole.records[count]? = some currentRecord := by
      rw [hrecords]
      simp only [ReferenceActivePhysicalHorizon.foldRound]
      rw [List.getElem?_append_right (by rw [hprefixLength])]
      rw [hprefixLength]
      simp [currentRecord, x, ReferenceCollectionPhaseHistory.nextInput]
    have hwholeOpt := List.getElem?_eq_getElem last.isLt
    rw [hwholeOpt] at hopt
    exact Option.some.inj hopt
  have hacceptedWhole : ReferenceCollectionPhaseHistory.AcceptedUp
      (whole.records[k₀]'hk₀Whole).input i message := by
    rw [hrecordK]
    exact haccepted
  have hretainedWhole : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (whole.records[j₀]'hj₀Whole) i prior := by
    rw [hrecordJ]
    exact hretained
  have happliedWhole : ReferenceFollowerReplyChronology.appliedDown
      (whole.records[j₀]'hj₀Whole) i prior.val.sigma := by
    rw [hrecordJ]
    exact happlied
  have hsenderWhole : sender = ReferenceFollowerFixedReply.actualChoice
      (whole.records[k₀]'hk₀Whole) i := by
    rw [hrecordK]
    exact hsender
  have hleftChoice : (ReferenceFollowerFixedReply.actualChoice
      (whole.records[k₀]'hk₀Whole) i).configuration =
      .ordinary upState upMemory := by
    rw [← hsenderWhole]
    exact hconfiguration
  have hrightChoice : (ReferenceFollowerFixedReply.actualChoice
      (whole.records[count]'last.isLt) i).configuration =
      .ordinary current currentMemory := by
    rw [hcurrentRecord]
    simp only [ReferenceFollowerFixedReply.actualChoice, currentRecord,
      ReferenceActivePhysicalStep.step]
    exact hcurrent
  have hmono := ReferenceFollowerReplyChronology.run_acceptedStart_mono
    initial rows selected rewards start (count + 1) hspan hmode i kFin last
    (Nat.le_of_lt hkcount)
    upState current upMemory currentMemory hleftChoice hrightChoice
  have hledgerLe : ledger.sigma ≤ ReferencePrelaunchFollower.acceptedStart current := by
    rw [← hmessageSigma, hstart]
    exact hmono.1
  exact ⟨j₀, k₀, hj₀Whole, hk₀Whole, message, prior, sender, upState, upMemory,
    hjk, hkcount,
    hacceptedWhole, hretainedWhole, happliedWhole, hpriorSigma, hmessageSigma,
    hsenderWhole, hconfiguration, hunoccupied, hoff, hstart, hlast, hpositive,
    hledgerLe⟩

/-- In the actual continuing collection-dispatch branch, the earlier retained
DOWN record is the whole current payload record. Its start is therefore no
newer than this follower's current accepted start, and the actual logged
receiver's local start guard rejects that candidate. The dispatcher branch
is an equality to `prepare`'s computed coordinator result, not a supplied core
snapshot. -/
theorem run_collection_continuing_dispatch_prior_down_guard
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (i : Label p)
    (first : ReferencePrelaunchFollower.State p rate.eta)
    (firstMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfirstFollower : initial.followers i = .ordinary first firstMemory)
    (hfirstNoDown : first.lastDown = none)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hcollection : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      (by omega) hmode).finalState.coordinator = .collection payload ledger proposal)
    (hmissing : i ∉ ledger.pending)
    (current : ReferencePrelaunchFollower.State p rate.eta)
    (currentMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hcurrent : ((ReferenceActivePhysicalStep.prepare
      (ReferenceCollectionPhaseHistory.nextInput initial rows selected rewards start count
        hspan hmode)).followers.followers i).configuration =
      .ordinary current currentMemory)
    (hcontinuing : ∃ (clock : CoordinatorPhaseClock.ClockRegisters p)
      (cutoff : Fin p.T)
      (core : CoordinatorRoundDispatch.CollectionCoreValid
        (ReferenceActivePhysicalStep.collectionInput
          (ReferenceCollectionPhaseHistory.nextInput initial rows selected rewards start count
            hspan hmode) payload ledger clock cutoff))
      (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
        (ReferenceActivePhysicalStep.collectionInput
          (ReferenceCollectionPhaseHistory.nextInput initial rows selected rewards start count
            hspan hmode) payload ledger clock cutoff))
      (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1)
      (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck
        (ReferenceActivePhysicalStep.collectionInput
          (ReferenceCollectionPhaseHistory.nextInput initial rows selected rewards start count
            hspan hmode) payload ledger clock cutoff) = true),
      (ReferenceActivePhysicalStep.prepare
        (ReferenceCollectionPhaseHistory.nextInput initial rows selected rewards start count
          hspan hmode)).coordinator =
        .collection payload ledger clock cutoff
          (.continuing core snapshot boundary scores)) :
    let x := ReferenceCollectionPhaseHistory.nextInput initial rows selected rewards start count
      hspan hmode
    let whole := ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (count + 1) hspan hmode
    ContinuingPriorDownGuard initial x whole count i payload ledger current := by
  let x := ReferenceCollectionPhaseHistory.nextInput initial rows selected rewards start count
    hspan hmode
  let whole := ReferenceActivePhysicalHorizon.run initial rows selected rewards start
    (count + 1) hspan hmode
  have hchronology := run_collection_missing_pending_current_start_mono
    initial rows selected rewards start count hspan hmode hfirst i first firstMemory
    hfirstFollower hfirstNoDown payload ledger proposal hcollection hmissing current
    currentMemory hcurrent
  obtain ⟨j, k, hjRun, hkRun, message, prior, sender, upState, upMemory,
      hjk, hkcount, haccepted, hretained, happlied, hpriorSigma, hmessageSigma,
      hsender, hsenderConfiguration, hunoccupied, hoff, hstart, hlast, hpositive,
      hledgerLe⟩ := hchronology
  have hretainedOriginal := hretained
  obtain ⟨clock, cutoff, core, snapshot, hboundary, hscores, hcontinuing⟩ := hcontinuing
  have hledgerSource : ledger.sigma =
      CoordinatorRecorderComplementBridge.sourceStart payload := core.ledger_sigma_eq
  have hledgerSourceNat : ledger.sigma = payload.sigma.val + 1 := by
    simpa [CoordinatorRecorderComplementBridge.sourceStart] using hledgerSource
  have hsourceLe : payload.sigma.val + 1 ≤
      ReferencePrelaunchFollower.acceptedStart current := by
    omega

  let oldRecord : Record := whole.records[j]'hjRun
  rcases hretained with ⟨oldLogged, oldCut, oldAfter, oldRaw, oldScan, oldRegisters,
    oldLastService, holdInput, holdDown, holdAccepted⟩
  obtain ⟨oldChoice, oldMemory, holdConfiguration, holdUnoccupied, holdLogging,
      holdCutEq⟩ := actual_logged_down_source oldRecord i oldLogged oldCut holdInput holdDown
  let oldPrepared := ReferenceActivePhysicalStep.prepare oldRecord.input
  let oldFollower := oldPrepared.followers.followers i
  let oldObservation := oldPrepared.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hacceptedOldView :
      (ReferenceDownReception.referenceDownCut p oldPrepared.coordinator.downView i
        oldRecord.input.row oldFollower.time oldObservation rate oldLogged).outcome =
        .accepted oldLogged oldAfter oldRaw prior oldScan oldRegisters oldLastService := by
    have h := holdAccepted
    rw [holdCutEq] at h
    exact h
  obtain ⟨someOldView, hsomeOldView⟩ := accepted_reference_cut_has_view
    oldPrepared.coordinator.downView i oldRecord.input.row oldFollower.time oldObservation
    oldLogged oldLogged oldAfter oldRaw prior oldScan oldRegisters oldLastService hacceptedOldView
  have holdSelectionExists :
      ∃ oldSelected : ReferenceActivePhysicalStep.Selection oldRecord.input,
        oldRecord.output.preparation.coordinator.selection = some oldSelected := by
    cases hsel : oldRecord.output.preparation.coordinator.selection with
    | none =>
        have hnone : oldRecord.output.preparation.coordinator.downView = none := by
          change oldRecord.output.preparation.coordinator.selection.map
            ReferenceActivePhysicalStep.Selection.view = none
          simp [hsel]
        have hnone' : oldPrepared.coordinator.downView = none := by
          have hprep : oldRecord.output.preparation = oldPrepared := by
            rw [oldRecord.output_eq]
            rfl
          rw [← hprep]
          exact hnone
        rw [hnone'] at hsomeOldView
        cases hsomeOldView
    | some oldSelected => exact ⟨oldSelected, rfl⟩
  obtain ⟨oldSelected, holdSelection⟩ := holdSelectionExists
  have holdDownView : oldPrepared.coordinator.downView = some oldSelected.view := by
    have hview : oldRecord.output.preparation.coordinator.downView = some oldSelected.view := by
      change oldRecord.output.preparation.coordinator.selection.map
        ReferenceActivePhysicalStep.Selection.view = some oldSelected.view
      rw [holdSelection]
      rfl
    have hprep : oldRecord.output.preparation = oldPrepared := by
      rw [oldRecord.output_eq]
      rfl
    rw [← hprep]
    exact hview
  have hacceptedSelectedView :
      (ReferenceDownReception.referenceDownCut p (some oldSelected.view) i
        oldRecord.input.row oldFollower.time oldObservation rate oldLogged).outcome =
        .accepted oldLogged oldAfter oldRaw prior oldScan oldRegisters oldLastService := by
    rw [← holdDownView]
    exact hacceptedOldView
  have holdFields := ReferenceActiveDataOwnership.referenceDown_accepted_fields
    oldSelected.view i oldRecord.input.row oldFollower.time oldObservation oldLogged
    oldLogged oldAfter oldRaw prior oldScan oldRegisters oldLastService hacceptedSelectedView
  have holdSigmaField : prior.val.sigma = oldSelected.view.payload.sigma.val + 1 := by
    have h := congrArg (fun record : DownRecord => record.val.sigma) holdFields.1
    change prior.val.sigma = oldSelected.view.payload.sigma.val + 1 at h
    exact h

  have hcurrentSelectionExists :
      ∃ currentSelected : ReferenceActivePhysicalStep.Selection x,
        (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some currentSelected := by
    have hselectionNe : (ReferenceActivePhysicalStep.prepare x).coordinator.selection ≠ none := by
      rw [hcontinuing]
      simp [ReferenceActivePhysicalStep.DispatchCut.selection]
    cases hsel : (ReferenceActivePhysicalStep.prepare x).coordinator.selection with
    | none => exact (hselectionNe hsel).elim
    | some currentSelected => exact ⟨currentSelected, rfl⟩
  obtain ⟨currentSelected, hcurrentSelection⟩ := hcurrentSelectionExists
  have hcurrentPayload : currentSelected.view.payload = payload := by
    have hmap : ((ReferenceActivePhysicalStep.prepare x).coordinator.selection.map
        (fun selected => selected.view.payload)) = some payload := by
      rw [hcontinuing]
      simp [ReferenceActivePhysicalStep.DispatchCut.selection]
    rw [hcurrentSelection] at hmap
    exact Option.some.inj hmap

  have hwholeLength := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start (count + 1) hspan hmode
  let last : Fin whole.records.length := ⟨count, by rw [hwholeLength]; omega⟩
  have hprefixLength := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start count (by omega) hmode
  have hsuccessor := ReferenceActivePhysicalHorizon.run_successor_step
    initial rows selected rewards start count hspan hmode
  let currentRecord : Record := ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩
  have hcurrentRecord : whole.records[count]'last.isLt = currentRecord := by
    have hrecords := congrArg ReferenceActivePhysicalHorizon.Run.records hsuccessor
    have hopt : whole.records[count]? = some currentRecord := by
      rw [hrecords]
      simp only [ReferenceActivePhysicalHorizon.foldRound]
      rw [List.getElem?_append_right (by rw [hprefixLength])]
      rw [hprefixLength]
      simp [currentRecord, x, ReferenceCollectionPhaseHistory.nextInput]
    have hwholeOpt := List.getElem?_eq_getElem last.isLt
    rw [hwholeOpt] at hopt
    exact Option.some.inj hopt
  have hcurrentRecordMem : currentRecord ∈ whole.records := by
    rw [← hcurrentRecord]
    exact List.getElem_mem last.isLt
  have hcurrentSelectionRecord :
      currentRecord.output.preparation.coordinator.selection = some currentSelected := by
    have hprep : currentRecord.output.preparation = ReferenceActivePhysicalStep.prepare x := by
      dsimp [currentRecord]
      rfl
    rw [hprep]
    exact hcurrentSelection
  have hsameSigma : oldSelected.view.payload.sigma.val =
      currentSelected.view.payload.sigma.val := by
    have hplus : oldSelected.view.payload.sigma.val + 1 =
        currentSelected.view.payload.sigma.val + 1 := by
      calc
        oldSelected.view.payload.sigma.val + 1 = prior.val.sigma := holdSigmaField.symm
        _ = message.val.sigma := hpriorSigma
        _ = ledger.sigma := hmessageSigma
        _ = payload.sigma.val + 1 := hledgerSourceNat
        _ = currentSelected.view.payload.sigma.val + 1 := by rw [hcurrentPayload]
    omega
  have hdownEq := ReferenceSelectedPayloadChronology.run_two_actualSelectedPayloads_downRecord_eq_of_equal_sigma
    initial rows selected rewards start (count + 1) hspan hmode hfirst oldRecord currentRecord
    oldSelected currentSelected (List.getElem_mem hjRun) hcurrentRecordMem
    holdSelection hcurrentSelectionRecord hsameSigma i
  have hpriorPayload : prior = payload.downRecord i := by
    calc
      prior = oldSelected.view.payload.downRecord i := holdFields.1
      _ = currentSelected.view.payload.downRecord i := hdownEq
      _ = payload.downRecord i := by rw [hcurrentPayload]

  refine ⟨j, k, hjRun, hkRun, message, prior, sender, upState, upMemory,
    hjk, hkcount, haccepted, hretainedOriginal, happlied, hpriorSigma, hmessageSigma,
    hsender, hsenderConfiguration, hunoccupied, hoff, hstart, hlast, hpositive,
    hpriorPayload, hledgerSource, hsourceLe, ?_⟩
  intro logged cut hloggedInput hloggedCut
  obtain ⟨loggedChoice, loggedMemory, hloggedConfiguration, hloggedUnoccupied,
      hlogging, hcutEq⟩ := actual_logged_down_source currentRecord i logged cut
    (by simpa [currentRecord] using hloggedInput)
    (by simpa [currentRecord] using hloggedCut)
  have hstates : loggedChoice = current ∧ loggedMemory = currentMemory :=
    LocalConfiguration.ordinary.inj (hloggedConfiguration.symm.trans hcurrent)
  let currentPrepared := (ReferenceActivePhysicalStep.prepare x).followers.followers i
  let currentObservation := (ReferenceActivePhysicalStep.prepare x).feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hloggingFrame := ActiveFollowerLogging.checkedLogging_success_frame i x.row
    currentPrepared.activation currentPrepared.time (currentPrepared.arm, currentObservation)
    loggedChoice logged hlogging
  have hloggedStart : ReferencePrelaunchFollower.acceptedStart logged =
      ReferencePrelaunchFollower.acceptedStart loggedChoice := by
    unfold ReferencePrelaunchFollower.acceptedStart
    rw [hloggingFrame.1]
  have hstartFrame : ReferencePrelaunchFollower.acceptedStart logged =
      ReferencePrelaunchFollower.acceptedStart current := by
    simpa [hstates.1] using hloggedStart
  have hguardFalse : ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
      currentPrepared.time logged (some (payload.downRecord i)) = False := by
    have hnot : ¬ OrdinaryMessageCodec.acceptDown
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        (ReferencePrelaunchFollower.acceptedStart logged) (currentPrepared.time.val + 1)
        (payload.downRecord i) := by
      intro hacceptDown
      have hstrict : ReferencePrelaunchFollower.acceptedStart current <
          (payload.downRecord i).val.sigma := by
        simpa only [hstartFrame] using hacceptDown.1
      have hfield : (payload.downRecord i).val.sigma = payload.sigma.val + 1 := rfl
      omega
    simpa [ReferenceDownReception.ordinaryLocalAcceptanceTest] using hnot
  exact ⟨hstartFrame, hcutEq, hguardFalse⟩

/-- Launch-boundary specialization. The original initialization inputs and the
conditional `hr`, `hdown`, and `hclean` obligations remain explicit. Only the
selected follower's replay seed is used; the actual first coordinator mode
and all-active launch mode are derived from `ofActualLaunchedBoundary`. -/
theorem ofActualLaunchedBoundary_run_collection_continuing_dispatch_prior_down_guard
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) + (count + 1) ≤ p.T)
    (i : Label p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (current : ReferencePrelaunchFollower.State p rate.eta)
    (currentMemory : ActiveFollowerLifecycle.LocalMemory p) :
    (let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched;
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h);
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun player => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
        hlaunched player;
    let prefixRun := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count
      (by omega) hmode;
    let x := ReferenceCollectionPhaseHistory.nextInput initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode;
    let wholeRun := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (count + 1)
      hspan hmode;
    initial.coordinator = .first ∧ ReferenceActivePhysicalHorizon.allActiveAtStart initial start ∧
      ∀ (hcollection : prefixRun.finalState.coordinator = .collection payload ledger proposal)
        (hmissing : i ∉ ledger.pending)
        (hcurrent : ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
          .ordinary current currentMemory)
        (hcontinuing : ∃ (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
          (core : CoordinatorRoundDispatch.CollectionCoreValid
            (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
          (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
            (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
          (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1)
          (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck
            (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff) = true),
          (ReferenceActivePhysicalStep.prepare x).coordinator =
            .collection payload ledger clock cutoff
              (.continuing core snapshot boundary scores)),
        ∃ (first : ReferencePrelaunchFollower.State p rate.eta)
          (firstMemory : ActiveFollowerLifecycle.LocalMemory p),
          initial.followers i = .ordinary first firstMemory ∧ first.lastDown = none ∧
          ContinuingPriorDownGuard initial x wholeRun count i payload ledger current) := by
  let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
    C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
  let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := by
    intro player
    exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched player
  have hfirst : initial.coordinator = .first :=
    ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  change initial.coordinator = .first ∧
    ReferenceActivePhysicalHorizon.allActiveAtStart initial start ∧ _
  refine ⟨hfirst, hmode, ?_⟩
  let prefixRun := ReferenceActivePhysicalHorizon.run initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count
    (by omega) hmode
  let x := ReferenceCollectionPhaseHistory.nextInput initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
  let wholeRun := ReferenceActivePhysicalHorizon.run initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (count + 1)
    hspan hmode
  intro hcollection hmissing hcurrent hcontinuing
  rcases ActualInitializationLaunchState.ofActualLaunchedBoundary_follower_replay
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch
      learnerSeed hlaunched i with
    ⟨first, firstMemory, hconfiguration, _, hfirstNoDown, _, _, _, _, _, _⟩
  refine ⟨first, firstMemory, hconfiguration, hfirstNoDown, ?_⟩
  exact run_collection_continuing_dispatch_prior_down_guard initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count
    hspan hmode (by simpa [initial] using hfirst) i first firstMemory hconfiguration
    hfirstNoDown payload ledger proposal hcollection hmissing current currentMemory hcurrent
    hcontinuing

/-- At the clipped terminal endpoint there is no physical `Fin T` record at
the next coordinate. In particular, when `blockStop = T` and `count = 0`, no
current choice or dispatcher branch is formed. -/
theorem ofActualLaunchedBoundary_no_next_record_at_terminal
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p) (count : ℕ)
    (hterminal : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) + count = p.T) :
    ¬ ∃ time : Fin p.T,
      time.val = BootstrapObservedFollower.blockStop p
        (ReferenceInitializationRun.nextBlock b h) + count := by
  rintro ⟨time, htime⟩
  have hlt := time.isLt
  omega

end Bandits.Support.ReferenceCollectionPriorDownHistory

end
