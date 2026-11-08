/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteFollowerContinuationKernel
import Bandits.Support.ReferenceCompleteFollowerRecoveryCalendarJoin

import Lean.Elab.Tactic.Omega

/-!
# Terminal reply assembly on the original complete history

Sources: `sources/zip4/manuscript/05_binary_transport.tex:60-88,354-431`,
`sources/zip4/manuscript/06_interruptions.tex:110-121,192-233,246-349`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-187`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-84`.

The accepted-UP hypothesis produces one recovery/calendar witness package.
The same diagnostic initializes the actual continuation, and the same literal
calendar list supplies the service tail. Connected ordinary chronology fixes
the reply fields through the actual accepted offer. Early, boundary and late
DOWN acceptance retain their distinct StartRound behavior.

This is a payload-relative internal result for
`ReferenceCompleteFollowerTerminalUpNumericalReplay`. The initial payload queue
is not identified here with a global logical queue. No manuscript closure is
asserted.
-/
@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteFollowerTerminalReplyAssembly

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence ReferenceFollowerReplyChronology

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem connected_next
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (chain : Connected initial records final)
    (n : ℕ) (hn : n + 1 < records.length) :
    records[n + 1].input.state = records[n].output.next := by
  have hs := connected_drop_from_output chain n (by omega)
  have ht := connected_take_to_input hs 0 (by simp only [List.length_drop]; omega)
  simpa only [List.take_zero, Connected, List.getElem_drop, Nat.add_zero] using ht

/-- The accepted offer itself produces the actual ordinary unoccupied CHOICE
and its literal four reply fields. No truth assertion about the reply is an
input. -/
private theorem accepted_up_actual_choice
    (r : RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp r.input i U) :
    ∃ state memory,
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory ∧
      state.status = .unoccupied ∧
      U.val.sigma = ReferencePrelaunchFollower.acceptedStart state ∧
      U.val.S = state.S ∧ U.val.delta = state.delta ∧ U.val.q = state.backlog := by
  obtain ⟨sender, state, memory, hsender, hindex, hconfiguration, hstatus,
    _, hsigma, _, hS, hdelta, hq, _⟩ :=
    ReferenceAcceptedUpFollowerHistory.acceptedUp_current_choice hacc
  refine ⟨state, memory, ?_, hstatus, hsigma, hS, hdelta, hq⟩
  change (r.output.preparation.followers.followers i).configuration = _
  have hp : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  rw [hp, hindex, ← hsender]
  exact hconfiguration

/-- Calendar index arithmetic, independent of all numerical cell terms. -/
private theorem calendar_dates
    (start birth accepted offered sigma cutoff endpoint total recovered length : ℕ)
    (hsigma : sigma = start + birth + 1)
    (htotal : sigma + total = cutoff) (hrecovered : sigma + recovered = endpoint)
    (hendpoint : endpoint = min cutoff (start + accepted + 2))
    (haccepted : accepted < offered)
    (hoff : offered < length) (hcutoff : cutoff ≤ start + offered + 1)
    (hle : recovered ≤ total) :
    max (birth + total) (accepted + 1) < length ∧
    max (birth + total) (accepted + 1) ≤ offered ∧
    (cutoff ≤ start + accepted + 2 →
      recovered = total ∧ max (birth + total) (accepted + 1) = accepted + 1) ∧
    (¬ cutoff ≤ start + accepted + 2 →
      birth + recovered = accepted + 1 ∧ recovered < total ∧
      max (birth + total) (accepted + 1) = birth + total) := by
  omega

/-- Choice injectivity aligns only the payload; the calendar and retained
indices from the metadata producers are not selected as new witnesses. -/
private theorem accepted_up_metadata
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hc : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input = some c) :
    U.val.sigma = c.payload.sigma.val + 1 ∧
    FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.time.val + 1 := by
  obtain ⟨cL, _, _, hcL, _, _, _, _, _, _, hule, _⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_up_live_calendar_interval
      (rate := rate) rewards C_star C_h source k i U hacc
  have hcL' : cL = c := Option.some.inj (hcL.symm.trans hc)
  have hbound : FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.time.val + 1 := by
    simpa only [hcL'] using hule
  obtain ⟨cS, _, _, _, _, hcS, _, _, _, _, _, _, hUsigmaS, _⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_up_selected_payload_interval
      (rate := rate) rewards C_star C_h source k i U hacc
  have hcS' : cS = c := Option.some.inj (hcS.symm.trans hc)
  exact ⟨by simpa only [hcS'] using hUsigmaS, hbound⟩

/-- Actual connected chronology excludes any newer applied DOWN between
this retained successor and the accepted offer. An unoccupied choice in this
interval consequently has the literal offered registers. -/
private theorem retained_terminal_reply_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hlast : after.lastDown = some M)
    (hnext : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[j.val].output.next.followers i =
        .ordinary after nextMemory)
    (hUsigma : U.val.sigma = M.val.sigma)
    (n : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hjz : j.val < n.val) (hnk : n.val ≤ k.val)
    (terminal : ReferencePrelaunchFollower.State p rate.eta)
    (terminalMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hterminalChoice : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[n.val] i).configuration =
          .ordinary terminal terminalMemory)
    (hterminalStatus : terminal.status = .unoccupied) :
    U.val.S = terminal.S ∧ U.val.delta = terminal.delta ∧ U.val.q = terminal.backlog := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let sigma := M.val.sigma
  have hnextBound : j.val + 1 < R.length := by
    have hn : n.val < R.length := n.isLt
    exact (Nat.succ_le_of_lt hjz).trans_lt hn
  obtain ⟨crossing, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source j
  have chain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate source rewards C_star C_h
    (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h crossing)
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source rewards C_star C_h crossing)
  obtain ⟨offered, offeredMemory, hoffered, _, hUstart, hUS, hUd, hUq⟩ :=
    accepted_up_actual_choice R[k.val] i U hacc
  have hoffStart : ReferencePrelaunchFollower.acceptedStart offered = sigma :=
    hUstart.symm.trans hUsigma
  let successor : Fin R.length := ⟨j.val + 1, hnextBound⟩
  obtain ⟨beforeA, memoryA, choiceA, hinputA, _, hstartA, hchoiceA, _, _⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h source successor i
  have haInput : R[successor.val].input.state.followers i = .ordinary after nextMemory := by
    have hadj := connected_next (records := R) chain j.val hnextBound
    exact (congrArg (fun st => st.followers i) hadj).trans hnext
  obtain ⟨heBefore, heMemory⟩ :=
    DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hinputA.symm.trans haInput)
  subst beforeA
  subst memoryA
  have haFrame := ActiveFollowerLifecycle.startRound_frame rate.eta _ _ _ _ _ hstartA
  have haDown : choiceA.lastDown = some M := haFrame.1.trans hlast
  have haStart : ReferencePrelaunchFollower.acceptedStart choiceA = sigma := by
    simp only [ReferencePrelaunchFollower.acceptedStart, haDown, sigma]
  have hstarts (n : Fin R.length) (hjn : j.val < n.val) (hnk : n.val ≤ k.val)
      (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (hchoice : (ReferenceFollowerFixedReply.actualChoice R[n.val] i).configuration =
        .ordinary state memory) : ReferencePrelaunchFollower.acceptedStart state = sigma := by
    have hlo := (connected_choice_chronology chain i successor.val n.val successor.isLt n.isLt
      (by dsimp only [successor]; omega) choiceA state nextMemory memory hchoiceA hchoice).1
    have hhi := (connected_choice_chronology chain i n.val k.val n.isLt k.isLt
      hnk state offered memory offeredMemory hchoice hoffered).1
    omega
  have hnoDown (n : Fin R.length) (hjn : j.val < n.val) (hnk : n.val < k.val)
      (start : ℕ) (happlied : appliedDown R[n.val] i start) : False := by
    obtain ⟨beforeK, beforeMemoryK, hinputK, hreplyK, _⟩ :=
      record_input_to_choice R[k.val] i offered offeredMemory hoffered
    have hbeforeStart := acceptedStart_eq_of_reply_eq hreplyK
    have hprefix := connected_take_to_input chain k.val k.isLt
    obtain ⟨out, outMemory, hout, hmono⟩ :=
      connected_output_chronology hprefix i beforeK beforeMemoryK hinputK n.val
        (by change n.val < (R.take k.val).length; rw [List.length_take]; omega)
    have hnTake : n.val < (R.take k.val).length := by rw [List.length_take]; omega
    have hrecord : (R.take k.val)[n.val]'hnTake = R[n.val] := List.getElem_take
    have hout' : R[n.val].output.next.followers i = .ordinary out outMemory := by
      rw [← hrecord]
      exact hout
    obtain ⟨choiceN, memoryN, hchoiceN, hstrict, houtStart⟩ :=
      record_appliedDown_strict R[n.val] i start happlied out outMemory hout'
    have hs := hstarts n hjn (by omega) choiceN memoryN hchoiceN
    omega
  have hchron := connected_choice_chronology chain i n.val k.val n.isLt k.isLt hnk
    terminal offered terminalMemory offeredMemory hterminalChoice hoffered
  have hequal : ReferencePrelaunchFollower.acceptedStart terminal =
      ReferencePrelaunchFollower.acceptedStart offered := by
    by_contra hne
    obtain ⟨n, hzn, hnk, start, happlied, _, _⟩ := hchron.2.2 hne
    exact hnoDown n (by omega) hnk start happlied
  have hreply := (hchron.2.1 hterminalStatus hequal).2
  have hUSterminal : U.val.S = terminal.S :=
    hUS.trans (congrArg (fun r => r.2.1) hreply)
  have hUdterminal : U.val.delta = terminal.delta :=
    hUd.trans (congrArg (fun r => r.2.2.1) hreply)
  have hUqterminal : U.val.q = terminal.backlog :=
    hUq.trans (congrArg (fun r => r.2.2.2) hreply)
  exact ⟨hUSterminal, hUdterminal, hUqterminal⟩

private theorem complete_record_row
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (q : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[q.val].input.row =
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
  obtain ⟨_, _, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source q
  change ((ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h).get q).input.row = _
  rw [hr]
  rfl

private theorem complete_next_input
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hbound : j.val + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[j.val + 1]'hbound).input.state =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[j.val].output.next := by
  obtain ⟨crossing, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source j
  have chain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate source rewards C_star C_h
    (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h crossing)
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source rewards C_star C_h crossing)
  exact connected_next chain j.val hbound

/-- Dates of the existing installation and retained acceptance locate the
first actual terminal choice, including the boundary and late cases. -/
private theorem complete_calendar_dates
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (P : Payload rate)
    (b j k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hjk : j.val < k.val)
    (hbirth : InstallationBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[b.val] P) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let sigma := P.sigma.val + 1
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
    let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
    let ell := min u (R[j.val].input.time.val + 2)
    let N := u - sigma
    let d := ell - sigma
    let z := max (b.val + N) (j.val + 1)
    0 < d → d ≤ N → u ≤ R[k.val].input.time.val + 1 →
    R[b.val].input.time.val = P.sigma.val ∧
    z < R.length ∧ z ≤ k.val ∧
    (u ≤ R[j.val].input.time.val + 2 → d = N ∧ z = j.val + 1) ∧
    (¬ u ≤ R[j.val].input.time.val + 2 →
      b.val + d = j.val + 1 ∧ d < N ∧ z = b.val + N) := by
  intro R sigma bits u ell N d z hdpos hdle hcutoffBound
  have huPos : sigma < u := by
    exact (FollowerCutoffScan.firstCutoff_bounds p rate.eta.val rate.eta.property
      rate.sourceCap P.sigma bits).1
  have hNu : sigma + N = u := Nat.add_sub_of_le huPos.le
  have hdell : sigma + d = ell := Nat.add_sub_of_le (Nat.sub_pos_iff_lt.mp hdpos).le
  have hbtime : R[b.val].input.time.val = P.sigma.val :=
    (ReferenceAssignmentPayloadChronology.installationBirth_time_eq _ P hbirth).symm
  have hb := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source b
  have hj := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source j
  have hk := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source k
  change R[b.val].input.time.val = _ at hb
  change R[j.val].input.time.val = _ at hj
  change R[k.val].input.time.val = _ at hk
  have hsigma : sigma = R[b.val].input.time.val + 1 := congrArg (· + 1) hbtime.symm
  have hklen : k.val < R.length := k.isLt
  have hsigmaDate : sigma =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + b.val + 1 :=
    hsigma.trans (congrArg (fun t => t + 1) hb)
  have hellDate : ell = min u
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + j.val + 2) := by
    rw [← hj]
  have huDate : u ≤
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k.val + 1 := by
    rw [← hk]
    exact hcutoffBound
  obtain ⟨hz, hzk, hlateDate, hearlyDate⟩ := calendar_dates
    _ b.val j.val k.val sigma u ell N d R.length
    hsigmaDate hNu hdell hellDate hjk hklen huDate hdle
  change z < R.length at hz
  change z ≤ k.val at hzk
  refine ⟨hbtime, hz, hzk, ?_, ?_⟩
  · intro htail
    apply hlateDate
    rw [← hj]
    exact htail
  · intro htail
    apply hearlyDate
    rw [← hj]
    exact htail

/-- Continue the same diagnostic along a supplied literal calendar whose
entries are verified at their actual indices. This lemma only assembles the
accepted kernels; it performs no further occupied service induction. -/
private theorem retained_calendar_terminal
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) (i : Fin (p.m - 1))
    (P : Payload rate)
    (b j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hjk : j.val < k.val)
    (hbirth : InstallationBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[b.val] P)
    (logged after : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (hlogged : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[j.val].output.followers i).downInput = some logged)
    (hdown : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[j.val].output.followers i).down = some cut)
    (houtcome : cut.outcome = .accepted logged after raw (P.downRecord i) scan registers lastService)
    (A : List (Bool × ℕ)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let M := P.downRecord i
    let sigma := P.sigma.val + 1
    let cap := 4 * rate.n
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
    let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
    let ell := min u (R[j.val].input.time.val + 2)
    let N := u - sigma
    let d := ell - sigma
    let z := max (b.val + N) (j.val + 1)
    let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
    let W := fun count => QueueReplay.replay cap registers ((A.drop d).take (count - d))
    ell = scan.endpoint → 0 < d → d ≤ N →
    u ≤ R[k.val].input.time.val + 1 →
    ∀ hAlen : A.length = N,
    (∀ (n : Fin N) (hn : b.val + n.val < R.length),
      ∃ (selected : Selection (R[b.val + n.val]'hn).input)
        (ordinary : ReferenceLaterLiveNumericalReadout.preparedOrdinary (R[b.val + n.val]'hn)),
        (R[b.val + n.val]'hn).output.preparation.coordinator.selection = some selected ∧
        CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff
          (R[b.val + n.val]'hn).input.time ∧
        (A[n.val]'(Nat.lt_of_lt_of_eq n.isLt hAlen.symm)) =
          let cell := ReferenceFirstWindowNumericalStream.sourceCell
            (R[b.val + n.val]'hn) selected.view.payload selected.view.pendingAtChoice
            (ReferenceLaterLiveNumericalReadout.preparedStates _ ordinary)
            selected.view.complementWeights selected.view.cutoff
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)
          (cell.enabled, RecordedQueueRun.quantizedArrival qp cell
            (selected.view.payload.assignment.assigned i))) →
    ∃ nextMemory,
      after.lastDown = some M ∧ R[j.val].output.next.followers i = .ordinary after nextMemory ∧
      ∃ hz : z < R.length, z ≤ k.val ∧ ∃ terminal terminalMemory,
        (ReferenceFollowerFixedReply.actualChoice (R[z]'hz) i).configuration =
          .ordinary terminal terminalMemory ∧ terminal.status = .unoccupied ∧
        terminal.lastDown = some M ∧ (terminal.S, terminal.backlog) = W N ∧
        terminal.delta = (if d < N then (W N).1 - (W (N - 1)).1 else lastService) := by
  intro R M sigma cap bits u ell N d z qp W hscan hdpos hdle hcutoffBound hAlen hcalendar
  obtain ⟨hbtime, hz, hzk, hlateDate, hearlyDate⟩ :=
    complete_calendar_dates rewards C_star C_h source P b j k hjk hbirth
      hdpos hdle hcutoffBound
  have hklen : k.val < R.length := k.isLt
  have hnextBound : j.val + 1 < R.length := lt_of_le_of_lt hjk hklen
  have hrow := complete_record_row rewards C_star C_h source j
  obtain ⟨hlast, hS, hdelta, hbacklog, _, _⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_down_output
      (rate := rate) rewards C_star C_h source j i logged after cut raw M
      scan registers lastService hlogged hdown houtcome
  have hregs : (after.S, after.backlog) = registers := by
    rw [hS, hbacklog]
  obtain ⟨hstatus, nextMemory, hnext, htoken⟩ :=
    ReferenceCompleteFollowerContinuationKernel.accepted_down_successor_token
      (rate := rate) rewards C_star C_h source j i logged after cut raw M
      scan registers lastService hlogged hdown houtcome
  have hterminal : ∃ terminal terminalMemory,
      (ReferenceFollowerFixedReply.actualChoice (R[z]'hz) i).configuration =
        .ordinary terminal terminalMemory ∧ terminal.status = .unoccupied ∧
      terminal.lastDown = some M ∧ (terminal.S, terminal.backlog) = W N ∧
      terminal.delta = (if d < N then (W N).1 - (W (N - 1)).1 else lastService) := by
    by_cases htail : u ≤ R[j.val].input.time.val + 2
    · obtain ⟨hdEq, hzEq⟩ := hlateDate htail
      change d = N at hdEq
      change z = j.val + 1 at hzEq
      have hs : scan.endpoint = min
          (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val R[j.val].input.row))
          (R[j.val].input.time.val + 2) := by
        rw [hrow]
        exact hscan.symm
      obtain ⟨terminal, memory, hchoice, hu, hl, hr, hdel⟩ :=
        ReferenceCompleteFollowerContinuationKernel.accepted_down_next_cutoff_choice
          (rate := rate) rewards C_star C_h source j i P
          logged after cut raw scan registers lastService hlogged hdown houtcome
          hnextBound hs (by rw [hrow]; exact htail)
      refine ⟨terminal, memory, ?_, hu, hl, ?_, ?_⟩
      · simpa only [hzEq] using hchoice
      · simpa only [W, hdEq, Nat.sub_self, List.take_zero, QueueReplay.replay,
          List.foldl_nil] using hr
      · simpa only [hdEq, lt_self_iff_false, ite_false] using hdel
    · have hell : ell = R[j.val].input.time.val + 2 := Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge htail))
      obtain ⟨heIndex, hdlt, hzEq⟩ := hearlyDate htail
      change b.val + d = j.val + 1 at heIndex
      change d < N at hdlt
      change z = b.val + N at hzEq
      have hbn : b.val + N < R.length := by
        rw [← hzEq]
        exact hz
      have hbd : b.val + d < R.length := heIndex.symm ▸ hnextBound
      have hprior : b.val + d - 1 < R.length :=
        lt_of_le_of_lt (Nat.sub_le _ _) hbd
      have hin : (R[b.val + d]'hbd).input.state.followers i =
          .ordinary after nextMemory := by
        have hadj := complete_next_input rewards C_star C_h source j hnextBound
        simpa only [heIndex] using (congrArg (fun st => st.followers i) hadj).trans hnext
      have hread : nextMemory.lastProposalRead = some
          ⟨(R[b.val + d - 1]'hprior).input.time,
            bits (R[b.val + d - 1]'hprior).input.time⟩ := by
        have hendpoint : scan.endpoint = R[j.val].input.time.val + 2 := hscan.symm.trans hell
        have ht := htoken hendpoint
        have he : b.val + d - 1 = j.val := by
          rw [heIndex, Nat.add_sub_cancel]
        simpa only [he, hrow] using ht
      have hcell (n : Fin N) : b.val + n.val < R.length :=
        (Nat.add_lt_add_left n.isLt b.val).trans hbn
      have hoccupied : after.status ≠ .unoccupied := by
        have hendpoint : scan.endpoint = R[j.val].input.time.val + 2 := hscan.symm.trans hell
        rw [hstatus, ite_eq_left hendpoint]
        simp only [ne_eq, reduceCtorEq, not_false_eq_true]
      obtain ⟨terminal, memory, hchoice, hu, hl, hr, hdel⟩ :=
        ReferenceCompleteFollowerContinuationKernel.complete_occupied_calendar_tail
          (rate := rate) rewards C_star C_h source P i b d hbn
          hbtime hdpos hdlt after nextMemory registers lastService A hin hoccupied
          hlast hregs hdelta hread hAlen (fun n => hcalendar n (hcell n))
      refine ⟨terminal, memory, ?_, hu, hl, hr, ?_⟩
      · simpa only [hzEq] using hchoice
      · simpa only [ite_eq_left hdlt] using hdel
  exact ⟨nextMemory, hlast, hnext, hz, hzk, hterminal⟩

/-- A single accepted UP supplies the recovery/calendar witnesses together
with their actual terminal choice and the literal offered reply fields.
The initial queue is the retained DOWN field, without a global queue premise. -/
theorem complete_accepted_up_terminal_reply
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
      (b j : Fin R.length)
      (logged after : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
      (scan : FollowerCutoffScan.ScanResult p.T)
      (registers : ℕ × ℕ) (lastService : ℕ),
      ReferenceCollectionSegmentExtraction.choice R[k.val].input = some c ∧
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] c.payload ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i (c.payload.downRecord i) ∧
      (R[j.val].output.followers i).downInput = some logged ∧
      (R[j.val].output.followers i).down = some cut ∧
      cut.outcome = .accepted logged after raw (c.payload.downRecord i) scan registers lastService ∧
      let P := c.payload
      let M := P.downRecord i
      let a := P.assignment.assigned i
      let sigma := P.sigma.val + 1
      let cap := 4 * rate.n
      let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
      let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
      let ell := min u (R[j.val].input.time.val + 2)
      let N := u - sigma
      let d := ell - sigma
      let z := max (b.val + N) (j.val + 1)
      let L := (R.drop b.val).take N
      let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
      ell = scan.endpoint ∧
      ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell =
        .ok ⟨registers, lastService⟩ ∧
      M.val.q = P.queues a ∧ 0 < d ∧ d ≤ N ∧
      L.map (fun r => r.input.time.val + 1) = List.range' sigma N ∧
      ∃ (hLlen : L.length = N)
        (v : ∀ n : Fin N, Selection
          (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input)
        (ho : ∀ n : Fin N, ReferenceLaterLiveNumericalReadout.preparedOrdinary
          (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm))),
        (∀ n, (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).output.preparation.coordinator.selection =
            some (v n) ∧ (v n).view.payload = P ∧ (v n).view.cutoff = none ∧
            CoordinatorLocalArmChoice.assignmentIsLive (v n).view.payload
              (v n).view.cutoff (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input.time) ∧
        (∀ n f, (ReferenceFollowerFixedReply.actualChoice
            (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) f).configuration =
          .ordinary
            (ReferenceLaterLiveNumericalReadout.preparedStates
              (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n) f)
            (ReferenceLaterLiveNumericalReadout.preparedMemories
              (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n) f)) ∧
        let Cells : Fin N → RecordedQueueRun.RoundInput p.K := fun n =>
          ReferenceFirstWindowNumericalStream.sourceCell
            (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (v n).view.payload
            (v n).view.pendingAtChoice
            (ReferenceLaterLiveNumericalReadout.preparedStates
              (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n))
            (v n).view.complementWeights (v n).view.cutoff
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v n))
        let A := List.ofFn (fun n : Fin N =>
          ((Cells n).enabled, RecordedQueueRun.quantizedArrival qp (Cells n) a))
        let Ed := ((R.drop b.val).take d).map
          (fun r => (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution M i r))
        let Q := ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell
        let V := fun count => QueueReplay.replay cap (0, M.val.q) (A.take count)
        Q = Ed ∧ Ed = A.take d ∧ A.length = N ∧
        (∀ x ∈ A, x.1 = true) ∧ registers = V d ∧
        lastService = (V d).1 - (V (d - 1)).1 ∧
        let W := fun count => QueueReplay.replay cap registers ((A.drop d).take (count - d))
        ∃ hz : z < R.length, z ≤ k.val ∧
          ∃ (terminal : ReferencePrelaunchFollower.State p rate.eta)
            (terminalMemory : ActiveFollowerLifecycle.LocalMemory p),
            (ReferenceFollowerFixedReply.actualChoice (R[z]'hz) i).configuration =
              .ordinary terminal terminalMemory ∧
            terminal.status = .unoccupied ∧ terminal.lastDown = some M ∧
            (terminal.S, terminal.backlog) = W N ∧
            terminal.delta = (if d < N then (W N).1 - (W (N - 1)).1 else lastService) ∧
            U.val.sigma = sigma ∧ U.val.S = terminal.S ∧
            U.val.delta = terminal.delta ∧ U.val.q = terminal.backlog := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  obtain ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService, hjoined⟩ :=
    ReferenceCompleteFollowerRecoveryCalendarJoin.accepted_up_recovery_calendar_join
      (rate := rate) rewards C_star C_h source k i U hacc
  obtain ⟨hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome, hcalendarJoin⟩ := hjoined
  dsimp only at hcalendarJoin
  obtain ⟨hscan, hchecked, hq, hdpos, hdle, htimes, hcalendarJoin⟩ := hcalendarJoin
  obtain ⟨hLlen, v, ho, hselected, hprepared, hQ, hEd, hAlen,
    hAenabled, hregisters, hlastService⟩ := hcalendarJoin
  let P := c.payload
  let M := P.downRecord i
  let a := P.assignment.assigned i
  let sigma := P.sigma.val + 1
  let cap := 4 * rate.n
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
  let ell := min u (R[j.val].input.time.val + 2)
  let N := u - sigma
  let d := ell - sigma
  let L := (R.drop b.val).take N
  let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let Cells : Fin N → RecordedQueueRun.RoundInput p.K := fun n =>
    ReferenceFirstWindowNumericalStream.sourceCell
      (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (v n).view.payload
      (v n).view.pendingAtChoice
      (ReferenceLaterLiveNumericalReadout.preparedStates
        (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n))
      (v n).view.complementWeights (v n).view.cutoff
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v n))
  let A := List.ofFn (fun n : Fin N =>
    ((Cells n).enabled, RecordedQueueRun.quantizedArrival qp (Cells n) a))
  let W := fun count => QueueReplay.replay cap registers ((A.drop d).take (count - d))
  let z := max (b.val + N) (j.val + 1)
  change 0 < d at hdpos
  change d ≤ N at hdle
  change ell = scan.endpoint at hscan
  change A.length = N at hAlen
  obtain ⟨hUsigma, hcutoffBound⟩ :=
    accepted_up_metadata rewards C_star C_h source k i U hacc c hc
  change U.val.sigma = sigma at hUsigma
  change u ≤ R[k.val].input.time.val + 1 at hcutoffBound
  have hcalendar (n : Fin N) (hn : b.val + n.val < R.length) :
      ∃ (selected : Selection (R[b.val + n.val]'hn).input)
        (ordinary : ReferenceLaterLiveNumericalReadout.preparedOrdinary (R[b.val + n.val]'hn)),
        (R[b.val + n.val]'hn).output.preparation.coordinator.selection = some selected ∧
        CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff
          (R[b.val + n.val]'hn).input.time ∧
        (A[n.val]'(Nat.lt_of_lt_of_eq n.isLt hAlen.symm)) =
          let cell := ReferenceFirstWindowNumericalStream.sourceCell
            (R[b.val + n.val]'hn) selected.view.payload selected.view.pendingAtChoice
            (ReferenceLaterLiveNumericalReadout.preparedStates _ ordinary)
            selected.view.complementWeights selected.view.cutoff
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)
          (cell.enabled, RecordedQueueRun.quantizedArrival qp cell
            (selected.view.payload.assignment.assigned i)) := by
    have he : L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm) =
        R[b.val + n.val]'hn := by
      simp only [L, List.getElem_take, List.getElem_drop]
    rw [← he]
    refine ⟨v n, ho n, (hselected n).1, (hselected n).2.2.2, ?_⟩
    simp only [A, List.getElem_ofFn, Fin.eta, Cells, a, P, (hselected n).2.1]
  obtain ⟨nextMemory, hlast, hnext, hz, hzk, terminal, terminalMemory,
    hterminalChoice, hterminalStatus, hterminalDown, hterminalRegisters, hterminalDelta⟩ :=
    retained_calendar_terminal rewards C_star C_h source k i P b j hjk hbirth
      logged after cut raw scan registers lastService hlogged hdown houtcome A
      hscan hdpos hdle hcutoffBound hAlen hcalendar
  have hjz : j.val < z :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self j.val) (Nat.le_max_right _ _)
  have hMsigma : M.val.sigma = sigma :=
    congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
  obtain ⟨hUSterminal, hUdterminal, hUqterminal⟩ :=
    retained_terminal_reply_fields rewards C_star C_h source k i U hacc j M
      after nextMemory hlast hnext (hUsigma.trans hMsigma.symm)
      ⟨z, hz⟩ hjz hzk terminal terminalMemory hterminalChoice hterminalStatus
  refine ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    hscan, hchecked, hq, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    hz, hzk, terminal, terminalMemory, hterminalChoice, hterminalStatus,
    hterminalDown, hterminalRegisters, hterminalDelta, hUsigma,
    hUSterminal, hUdterminal, hUqterminal⟩

end Bandits.Support.ReferenceCompleteFollowerTerminalReplyAssembly
