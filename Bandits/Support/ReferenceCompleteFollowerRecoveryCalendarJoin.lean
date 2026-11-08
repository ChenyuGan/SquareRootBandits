/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteFollowerRetainedDownRecovery

import Lean.Elab.Tactic.Omega

/-!
# Accepted UP recovery joined to the original live calendar

Sources: sources/zip4/manuscript/05_binary_transport.tex:60-88,354-431,
sources/zip4/manuscript/06_interruptions.tex:110-121,192-233,246-349,
sources/zip4/manuscript/04_slow_fast_learner.tex:140-187, and
sources/zip4/manuscript/appendix_a_local_protocol.tex:8-84.

This joins an actual accepted UP's retained DOWN recovery list to the whole
original enabled calendar interval. Each calendar entry is built from its
actual selection and prepared follower states. The final service is the last
calendar transition, including a zero arrival.
-/
@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceFollowerSparseEmissionRecovery
open ReferenceAssignmentPayloadChronology DeclaredFollowerLocalRound

namespace Bandits.Support.ReferenceCompleteFollowerRecoveryCalendarJoin

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem min_sub_le_left (x y z : ℕ) : min x y - z ≤ x - z := by
  exact Nat.sub_le_sub_right (Nat.min_le_left x y) z

private theorem installation_birth_index_unique
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (b₁ b₂ : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (h₁ : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[b₁.val] payload)
    (h₂ : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[b₂.val] payload) :
    b₁ = b₂ := by
  have ht₁ := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    _ payload h₁
  have ht₂ := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    _ payload h₂
  have hr₁ := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source b₁
  have hr₂ := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source b₂
  apply Fin.ext
  omega

private theorem retained_down_lt_impossible
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1))
    (message : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (j₁ j₂ : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hlt : j₁.val < j₂.val)
    (h₁ : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[j₁.val] i message)
    (h₂ : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[j₂.val] i message) :
    False := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  obtain ⟨hc, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source j₁
  have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate source rewards C_star C_h hc
  have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate source rewards C_star C_h
    (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc) hlaunch
  have happlied₁ := ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown h₁
  have happlied₂ := ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown h₂
  rcases h₁ with ⟨logged₁, cut₁, after₁, raw₁, scan₁, regs₁, last₁,
    hinput₁, hdown₁, houtcome₁⟩
  rcases h₂ with ⟨logged₂, cut₂, after₂, raw₂, scan₂, regs₂, last₂,
    hinput₂, hdown₂, houtcome₂⟩
  have hnext₁ := ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_down_output
    (rate := rate) rewards C_star C_h source j₁ i logged₁ after₁ cut₁ raw₁ message
    scan₁ regs₁ last₁ hinput₁ hdown₁ houtcome₁
  obtain ⟨_, _, _, _, memory₁, hnext₁⟩ := hnext₁
  obtain ⟨choice₁, choiceMemory₁, _, _, hstart₁⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict R[j₁.val] i message.val.sigma
      happlied₁ after₁ memory₁ hnext₁
  have hnext₂ := ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_down_output
    (rate := rate) rewards C_star C_h source j₂ i logged₂ after₂ cut₂ raw₂ message
    scan₂ regs₂ last₂ hinput₂ hdown₂ houtcome₂
  obtain ⟨_, _, _, _, memory₂, hnext₂⟩ := hnext₂
  obtain ⟨choice₂, choiceMemory₂, hchoice₂, hlt₂, _⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict R[j₂.val] i message.val.sigma
      happlied₂ after₂ memory₂ hnext₂
  have hdrop := ReferenceFollowerReplyChronology.connected_drop_from_output
    hchain j₁.val j₁.isLt
  let count := j₂.val - (j₁.val + 1)
  have hcount : count < (R.drop (j₁.val + 1)).length := by
    simp only [List.length_drop]
    have hj₂ : j₂.val < R.length := by simp [R]
    dsimp [count]
    omega
  have hsegment := ReferenceFollowerReplyChronology.connected_take_to_input hdrop count hcount
  have hget : (R.drop (j₁.val + 1))[count]'hcount = R[j₂.val] := by
    simp only [List.getElem_drop]
    congr 1
    dsimp [count]
    omega
  rw [hget] at hsegment
  obtain ⟨before₂, beforeMemory₂, hbefore₂, hreply₂, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice R[j₂.val] i choice₂
      choiceMemory₂ hchoice₂
  obtain ⟨first, firstMemory, hfirst, hmono, _, _⟩ :=
    ReferenceFollowerReplyChronology.connected_ordinary_chronology hsegment i
      before₂ beforeMemory₂ hbefore₂
  have hfirstEq : first = after₁ :=
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hfirst.symm.trans hnext₁)).1
  subst first
  have hstartBefore₂ := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply₂
  have hle : message.val.sigma ≤ ReferencePrelaunchFollower.acceptedStart choice₂ := by
    calc
      message.val.sigma = ReferencePrelaunchFollower.acceptedStart after₁ := hstart₁.symm
      _ ≤ ReferencePrelaunchFollower.acceptedStart before₂ := hmono
      _ = ReferencePrelaunchFollower.acceptedStart choice₂ := hstartBefore₂.symm
  omega

private theorem retained_down_index_unique
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1))
    (message : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (j₁ j₂ : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (h₁ : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[j₁.val] i message)
    (h₂ : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[j₂.val] i message) :
    j₁ = j₂ := by
  by_contra hne
  have hval : j₁.val ≠ j₂.val := by
    intro h
    exact hne (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact (retained_down_lt_impossible (rate := rate) rewards C_star C_h source i message
      j₁ j₂ hlt h₁ h₂).elim
  · exact (retained_down_lt_impossible (rate := rate) rewards C_star C_h source i message
      j₂ j₁ hgt h₂ h₁).elim

private theorem restarted_successor_eq_actual
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (ConstructorDimensions.M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s l : ℕ) (hspan : s + (l + 1) ≤ p.T)
    (mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (b j : Fin R.length)
    (hphysical : ReferenceFollowerSparseEmissionRecovery.physicalRecords
      initial rows selected rewards s l hspan mode = (R.drop b.val).take (l + 1))
    (hindex : b.val + l = j.val) (hj : j.val < R.length) :
    ReferenceFollowerSparseEmissionRecovery.successorRecord
      initial rows selected rewards s l hspan mode = R[j.val] := by
  have hg := congrArg
    (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =>
      records[l]?) hphysical
  rw [ReferenceFollowerSparseEmissionRecovery.physicalRecords,
    List.getElem?_append_right (by
      rw [ReferenceFollowerSparseEmissionRecovery.priorRun,
        ReferenceActivePhysicalHorizon.run_record_count])] at hg
  simp only [ReferenceFollowerSparseEmissionRecovery.priorRun,
    ReferenceActivePhysicalHorizon.run_record_count, Nat.sub_self,
    List.getElem?_cons_zero, List.getElem?_take, Nat.lt_succ_self, ite_true,
    List.getElem?_drop, hindex] at hg
  rw [List.getElem?_eq_getElem hj] at hg
  exact Option.some.inj hg

private theorem restarted_recovery_prefix
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (ConstructorDimensions.M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s l : ℕ) (span : s + (l + 1) ≤ p.T)
    (mode : allActiveAtStart initial s)
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) (b j : Fin R.length)
    (hindex : b.val + l = j.val)
    (hfull : (run initial rows J rewards s (l + 1) span mode).records =
      (R.drop b.val).take (l + 1))
    (hprior : (run initial rows J rewards s l (by omega) mode).records =
      (R.drop b.val).take l)
    (i : Fin (p.m - 1))
    (seed logged after : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed memory)
    (hvalid : ActiveFollowerLifecycle.localBufferValid seed)
    (hpair : seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ s)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (hlogged : (R[j.val].output.followers i).downInput = some logged)
    (hdown : (R[j.val].output.followers i).down = some cut)
    (houtcome : cut.outcome = .accepted logged after raw M scan registers lastService)
    (hsigma : M.val.sigma = s + 1)
    (hwindow : selectedViewInterval s ((R.drop b.val).take l)) :
    ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged scan.endpoint =
      ((R.drop b.val).take (scan.endpoint - M.val.sigma)).map
        (fun r => (true, emissionContribution M i r)) ∧
    (∀ r ∈ (R.drop b.val).take l,
      ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i r) ∧
    scan.endpoint ≤ s + l + 2 := by
  have hphysical : physicalRecords initial rows J rewards s l span mode =
      (R.drop b.val).take (l + 1) := by
    rw [physicalRecords_eq_run_successor]
    exact hfull
  have hcurrent : successorRecord initial rows J rewards s l span mode = R[j.val] :=
    restarted_successor_eq_actual initial rows J rewards s l span mode R b j
      hphysical hindex j.isLt
  have hprior' : (priorRun initial rows J rewards s l span mode).records =
      (R.drop b.val).take l := hprior
  have hwindow' : selectedViewInterval s
      (priorRun initial rows J rewards s l span mode).records := by
    rw [hprior']
    exact hwindow
  have hi : ((successorRecord initial rows J rewards s l span mode).output.followers i).downInput =
      some logged := by rw [hcurrent]; exact hlogged
  have hd : ((successorRecord initial rows J rewards s l span mode).output.followers i).down =
      some cut := by rw [hcurrent]; exact hdown
  have hn := accepted_window_no_prior_reset initial rows J rewards s l span mode i
    logged cut after raw M scan registers lastService hi hd houtcome hsigma hwindow'
  have hq := accepted_window_recoveryQueueRecords_eq_physical_prefix initial rows J rewards
    s l span mode i seed memory hseed hvalid hpair htime logged cut after raw M scan registers
    lastService hi hd houtcome hsigma hwindow'
  have ht := actualAcceptedCut_downTransition (successorRecord initial rows J rewards s l span mode)
    i logged cut after raw M scan registers lastService hi hd houtcome
  have hendpoint : scan.endpoint ≤ s + l + 2 := by
    let r := successorRecord initial rows J rewards s l span mode
    have hc := ActiveFollowerDownAcceptance.downTransition_accepted_checked p
      (r.output.preparation.followers.followers i).follower
      (r.output.preparation.followers.followers i).row
      (r.output.preparation.followers.followers i).time
      (r.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged after raw M scan
      registers lastService ht
    have halign := PreparedRound.follower_alignment r.output.preparation i
    have hrt := (physicalRecords_time_and_length initial rows J rewards s l span mode).1
    have hb := hc.2.2.2.1
    rw [halign.2.2.1] at hb
    exact hb.trans_eq (congrArg (fun n => n + 2) hrt)
  refine ⟨?_, ?_, hendpoint⟩
  · rw [hphysical, List.take_take, Nat.min_eq_left (by omega)] at hq
    exact hq
  · rw [← hprior']
    exact hn

private theorem selected_cell_arrival
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : r = (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val])
    (v : Selection r.input)
    (hv : r.output.preparation.coordinator.selection = some v)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff r.input.time)
    (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r)
    (i : Fin (p.m - 1))
    (hu : (ReferenceLaterLiveNumericalReadout.preparedStates r ho i).status = .unoccupied) :
    RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (ReferenceFirstWindowNumericalStream.sourceCell r v.view.payload v.view.pendingAtChoice
        (ReferenceLaterLiveNumericalReadout.preparedStates r ho) v.view.complementWeights v.view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid v))
      (v.view.payload.assignment.assigned i) = emissionContribution (v.view.payload.downRecord i) i r := by
  classical
  subst r
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)[k.val]
  let states := ReferenceLaterLiveNumericalReadout.preparedStates r ho
  let memories := ReferenceLaterLiveNumericalReadout.preparedMemories r ho
  let P := v.view.payload
  let a := P.assignment.assigned i
  obtain ⟨st, mem, hactual, hcontribution⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_selected_original_candidate_contribution
      (rate := rate) rewards C_star C_h source k v hv hlive
  have hstates : st = states := by
    funext f
    exact (LocalConfiguration.ordinary.inj ((hactual f).symm.trans
      (ReferenceLaterLiveNumericalReadout.prepared_configuration r ho f))).1
  subst st
  have hc := hcontribution i hu
  have hvalid := ReferenceLaterLiveNumericalReadout.selection_choiceValid v
  let W := ReferenceFirstWindowNumericalStream.sourceWeights P v.view.complementWeights
  have hWpos := ReferenceFirstWindowNumericalStream.sourceWeights_pos P
    v.view.complementWeights v.view.cutoff r.input.time hvalid
  have hWlower := ReferenceFirstWindowNumericalStream.sourceWeights_lower P
    v.view.complementWeights v.view.cutoff r.input.time hvalid
  have hWupper := ReferenceFirstWindowNumericalStream.sourceWeights_upper P
    v.view.complementWeights v.view.cutoff r.input.time hvalid
  have hsel : (prepare r.input).coordinator.selection = some v := by
    have hprep : r.output.preparation = prepare r.input := by rw [r.output_eq]; rfl
    rw [← hprep]
    exact hv
  have hevents := ReferenceSelectedCandidateRecorderEvent.selected_candidate_arm_event_independent_of_weights
    r v hsel i (ReferenceActiveDataOwnership.choiceSnapshot v states) (states i) (memories i)
    (ReferenceLaterLiveNumericalReadout.prepared_configuration r ho i) hu rfl W hWpos hWlower hWupper
  have hrw : r.input.rewards = rewards := by
    obtain ⟨_, _, heq⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
      rate rewards C_star C_h source k
    change ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k).input.rewards = rewards
    rw [heq]
    rfl
  have hrate : OrdinaryMessageCodec.dyadicRate (P.downRecord i).val.h = P.rate a := by
    have hh := congrArg OrdinaryMessageCodec.DownFields.h (P.downRecord_fields i)
    rw [hh, P.dyadicRate_eq_rate]
  have hscale : (rate.n : ℝ) = (D p : ℝ) * rate.eta.val := by
    rw [rate.n_scale, mul_comm]
  rw [ReferenceFirstWindowNumericalStream.sourceCell_quantizedArrival, hc]
  have hevent : ReferenceFirstWindowNumericalStream.sourceArm r P v.view.pendingAtChoice
      states v.view.complementWeights v.view.cutoff hvalid = some a ↔
    SnapshotRecordingKernel.recordingMap p
      (.live P.assignment (ReferenceActiveDataOwnership.choiceSnapshot v states))
      true rate.eta.val rate.eta.property P.eta_le_source_cap P.anchor P.anchor
      P.anchor_pos P.anchor_pos (fun _ => le_rfl)
      (fun j => by rw [two_mul]; exact le_add_of_nonneg_right (le_of_lt (P.anchor_pos j)))
      (r.input.row.2 r.input.time).1 = some a := by
    simpa only [ReferenceFirstWindowNumericalStream.sourceArm,
      ReferenceActiveDataOwnership.choiceSnapshot, v.pending_eq, P, W, a] using hevents
  by_cases h : ReferenceFirstWindowNumericalStream.sourceArm r P v.view.pendingAtChoice
      states v.view.complementWeights v.view.cutoff hvalid = some a
  · rw [ite_eq_left h, ite_eq_left (hevent.mp h), hrw, hrate, hscale]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hevent.mpr h'))]

private theorem checked_recovery_calendar_delta
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (logged : ReferencePrelaunchFollower.State p rate.eta) (ell : ℕ)
    (registers : ℕ × ℕ) (lastService : ℕ)
    (hinterval : M.val.sigma < ell)
    (hchecked : ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell =
      .ok ⟨registers, lastService⟩)
    (A : List (Bool × ℕ)) (d : ℕ) (hd : d = ell - M.val.sigma)
    (hQ : ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell = A.take d) :
    let V := fun count => QueueReplay.replay (4 * rate.n) (0, M.val.q) (A.take count)
    registers = V d ∧ lastService = (V d).1 - (V (d - 1)).1 := by
  dsimp only
  have hregs := (ActiveFollowerDownAcceptance.checkedRecovery_success
    p rate M logged ell ⟨registers, lastService⟩ hchecked).2.1
  have hlast := ActiveFollowerDownAcceptance.checkedRecovery_success_last_service
    p rate M logged ell hinterval ⟨registers, lastService⟩ hchecked
  have hpreLen : (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
      (ell - 1)).length = d - 1 := by
    simp only [ActiveFollowerDownAcceptance.recoveryQueueRecords,
      ActiveFollowerDownAcceptance.recoveryArrivals, List.length_map,
      ActiveFollowerDownAcceptance.recoveryRounds_length]
    omega
  have hpre : ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged (ell - 1) =
      A.take (d - 1) := by
    have ht := congrArg (fun xs : List (Bool × ℕ) => xs.take (d - 1)) hQ
    rw [ActiveFollowerDownAcceptance.recoveryQueueRecords_append_last p rate M logged ell hinterval,
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.take_take, Nat.min_eq_left (by omega)] at ht
    exact ht
  constructor
  · simpa only [ActiveFollowerDownAcceptance.recoveredRegisters, hQ] using hregs
  · change lastService = _ at hlast
    rw [hlast, ActiveFollowerDownAcceptance.recoveredLastService,
      ← ActiveFollowerDownAcceptance.recoveredRegisters_eq_lastTransition p rate M logged ell hinterval]
    simp only [ActiveFollowerDownAcceptance.recoveredRegisters,
      ActiveFollowerDownAcceptance.recoveredRegistersBeforeLast, hQ, hpre]

private theorem prepared_of_actual
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hactual : ∀ f, (ReferenceFollowerFixedReply.actualChoice r f).configuration =
      .ordinary (states f) (memories f)) :
    ∃ ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r,
      ReferenceLaterLiveNumericalReadout.preparedStates r ho = states ∧
      ReferenceLaterLiveNumericalReadout.preparedMemories r ho = memories := by
  have ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r := by
    intro f
    have hf := hactual f
    change (r.output.preparation.followers.followers f).configuration = _ at hf
    simp only [hf, ReferenceLaterLiveNumericalReadout.ordinaryData,
      Option.isSome_some]
  refine ⟨ho, ?_, ?_⟩
  · funext f
    exact (LocalConfiguration.ordinary.inj
      ((ReferenceLaterLiveNumericalReadout.prepared_configuration r ho f).symm.trans (hactual f))).1
  · funext f
    exact (LocalConfiguration.ordinary.inj
      ((ReferenceLaterLiveNumericalReadout.prepared_configuration r ho f).symm.trans (hactual f))).2

private theorem unoccupied_choice_of_no_reset
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial R final)
    (i : Fin (p.m - 1)) (b l n : ℕ)
    (hb : b < R.length) (hn : b + n < R.length) (hnl : n ≤ l)
    (seed current : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory currentMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceFollowerFixedReply.actualChoice R[b] i).configuration =
      .ordinary seed seedMemory)
    (hcurrent : (ReferenceFollowerFixedReply.actualChoice R[b + n] i).configuration =
      .ordinary current currentMemory)
    (hu : seed.status = .unoccupied)
    (hnoReset : ∀ r ∈ (R.drop b).take l,
      ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i r) :
    current.status = .unoccupied := by
  have hc := ReferenceFollowerReplyChronology.connected_choice_chronology chain i b (b + n)
    hb hn (by omega) seed current seedMemory currentMemory hseed hcurrent
  apply (hc.2.1 hu ?_).1
  by_contra hne
  obtain ⟨badIndex, hlo, hhi, badSigma, happlied, _, _⟩ := hc.2.2 hne
  have hbad : ReferenceFollowerBufferProvenance.acceptedDownReset i R[badIndex.val] := by
    rcases happlied with ⟨lg, cd, aft, rw, msg, sc, regs, ls, _, hdn, hout, _⟩
    exact ⟨cd, hdn, lg, aft, rw, msg, sc, regs, ls, hout⟩
  have hmem : R[badIndex.val] ∈ (R.drop b).take l := by
    apply List.mem_iff_getElem.mpr
    refine ⟨badIndex.val - b, ?_, ?_⟩
    · simp only [List.length_take, List.length_drop]
      omega
    · simp only [List.getElem_take, List.getElem_drop]
      congr 1
      omega
  exact hnoReset _ hmem hbad

private theorem aligned_accepted_up
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate) (b j : Fin R.length)
      (seed seedChoice : ReferencePrelaunchFollower.State p rate.eta)
      (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
      (logged after : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
      (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ),
      ReferenceCollectionSegmentExtraction.choice R[k.val].input = some c ∧
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] c.payload ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i (c.payload.downRecord i) ∧
      R[b.val].input.state.followers i = .ordinary seed seedMemory ∧
      seed.status = .unoccupied ∧
      (ReferenceFollowerFixedReply.actualChoice R[b.val] i).configuration =
        .ordinary seedChoice seedMemory ∧
      seedChoice.status = .unoccupied ∧ ActiveFollowerLifecycle.localBufferValid seed ∧
      seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ seed.buffer, saved.calendarRound ≤ c.payload.sigma.val) ∧
      ReferenceFollowerSparseEmissionRecovery.selectedViewInterval c.payload.sigma.val
        ((R.drop b.val).take (j.val - b.val)) ∧
      (R[j.val].output.followers i).downInput = some logged ∧
      (R[j.val].output.followers i).down = some cut ∧
      cut.outcome = .accepted logged after raw (c.payload.downRecord i) scan registers lastService ∧
      scan.endpoint = min
        (FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))))
        (R[j.val].input.time.val + 2) ∧
      ActiveFollowerDownAcceptance.checkedRecovery p rate (c.payload.downRecord i)
        logged scan.endpoint = .ok ⟨registers, lastService⟩ ∧
      let sigma := c.payload.sigma.val + 1
      let u := FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)))
      let L := (R.drop b.val).take (u - sigma)
      1 ≤ u - sigma ∧ u ≤ R[k.val].input.time.val + 1 ∧
      L.map (fun r => r.input.time.val + 1) = List.range' sigma (u - sigma) ∧
      (∀ n : Fin L.length, ∃ v : Selection L[n.val].input,
        L[n.val].output.preparation.coordinator.selection = some v ∧
        v.view.payload = c.payload ∧ v.view.cutoff = none ∧
        CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff L[n.val].input.time ∧
        ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
          (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
          (∀ f, (ReferenceFollowerFixedReply.actualChoice L[n.val] f).configuration =
            .ordinary (states f) (memories f)) ∧
          (∀ f, (states f).status ≠ .unoccupied →
            (states f).lastDown = some (c.payload.downRecord f))) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  obtain ⟨cL, bL, jL, hchoiceL, hblL, hjkL, hbirthL, hretainedL, hbaseL,
    hpositiveL, huleL, htimesL, hselectedL⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_up_live_calendar_interval
      (rate := rate) rewards C_star C_h source k i U hacc
  obtain ⟨cB, bB, jB, seed, seedChoice, seedMemory, hchoiceB, hblB, hjkB,
    hbirthB, hretainedB, hseed, hdomain, hseedStatus, hstartRound, hchoiceSeed,
    hchoiceStatus, hbufferValid, hbufferPair, hbufferTime, hinitialQueue, hwindowB⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_up_birth_buffer_interval
      (rate := rate) rewards C_star C_h source k i U hacc
  obtain ⟨cR, bR, jR, logged, after, cut, raw, scan, registers, lastService,
    hchoiceR, hblR, hjkR, hbirthR, hlogged, hdown, houtcome, hscanEndpoint,
    hchecked, hregisters⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_up_retained_down_recovery
      (rate := rate) rewards C_star C_h source k i U hacc
  have hcLB : cL = cB := Option.some.inj (hchoiceL.symm.trans hchoiceB)
  cases hcLB
  have hcLR : cL = cR := Option.some.inj (hchoiceL.symm.trans hchoiceR)
  cases hcLR
  have hbLB : bL = bB := installation_birth_index_unique
    (rate := rate) rewards C_star C_h source cL.payload bL bB hbirthL hbirthB
  cases hbLB
  have hbLR : bL = bR := installation_birth_index_unique
    (rate := rate) rewards C_star C_h source cL.payload bL bR hbirthL hbirthR
  cases hbLR
  have hretainedR : ReferenceAcceptedUpFollowerHistory.RetainedDown
      R[jR.val] i (cL.payload.downRecord i) :=
    ⟨logged, cut, after, raw, scan, registers, lastService, hlogged, hdown, houtcome⟩
  have hjBR := retained_down_index_unique (rate := rate) rewards C_star C_h source i
    (cL.payload.downRecord i) jB jR hretainedB hretainedR
  have hjLR := retained_down_index_unique (rate := rate) rewards C_star C_h source i
    (cL.payload.downRecord i) jL jR hretainedL hretainedR
  subst jB
  subst jL
  exact ⟨cL, bL, jR, seed, seedChoice, seedMemory, logged, after, cut, raw, scan,
    registers, lastService, hchoiceR, hblR, hjkR, hbirthR, hretainedR, hseed,
    hseedStatus, hchoiceSeed, hchoiceStatus, hbufferValid, hbufferPair, hbufferTime,
    hwindowB, hlogged, hdown, houtcome, hscanEndpoint, hchecked,
    hpositiveL, huleL, htimesL, hselectedL⟩

theorem accepted_up_recovery_calendar_join
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
          (fun r => (true, emissionContribution M i r))
        let Q := ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell
        let V := fun count => QueueReplay.replay cap (0, M.val.q) (A.take count)
        Q = Ed ∧ Ed = A.take d ∧ A.length = N ∧
        (∀ x ∈ A, x.1 = true) ∧ registers = V d ∧
        lastService = (V d).1 - (V (d - 1)).1 := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  obtain ⟨c, b, j, seed, seedChoice, seedMemory, logged, after, cut, raw, scan,
    registers, lastService, hchoiceR, hblR, hjkR, hbirthR, hretainedR, hseed,
    hseedStatus, hchoiceSeed, hchoiceStatus, hbufferValid, hbufferPair, hbufferTime,
    hwindowB, hlogged, hdown, houtcome, hscanEndpoint, hchecked,
    hpositiveL, huleL, htimesL, hselectedL⟩ :=
    aligned_accepted_up (rate := rate) rewards C_star C_h source k i U hacc
  let P := c.payload
  let M := P.downRecord i
  let a := P.assignment.assigned i
  let sigma := P.sigma.val + 1
  let cap := 4 * rate.n
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
  let endpointRound := R[j.val].input.time.val + 2
  let ell := min u endpointRound
  let N := u - sigma
  let d := ell - sigma
  let L := (R.drop b.val).take N
  let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have hchoice : ReferenceCollectionSegmentExtraction.choice R[k.val].input = some c := hchoiceR
  have hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] P := hbirthR
  have hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i M := hretainedR
  have hMsigma : M.val.sigma = P.sigma.val + 1 :=
    congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
  have hbtime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    R[b.val] P hbirth
  have hsigma : M.val.sigma = R[b.val].input.time.val + 1 := by
    exact hMsigma.trans (congrArg (fun n => n + 1) hbtime)
  have htimeb := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source b
  have htimej := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source j
  have htimek := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source k
  have hsigtime : sigma = R[b.val].input.time.val + 1 := by
    dsimp [sigma]
    rw [hbtime]
  have hbk : b.val ≤ k.val := Nat.le_trans hblR (Nat.le_of_lt hjkR)
  have hk : k.val < R.length := by simp [R]
  have hNbound : N ≤ R.length - b.val := by
    dsimp [N]
    rw [hsigtime]
    calc
      u - (R[b.val].input.time.val + 1) ≤
          (R[k.val].input.time.val + 1) - (R[b.val].input.time.val + 1) :=
        Nat.sub_le_sub_right huleL _
      _ ≤ R.length - b.val := by rw [htimek, htimeb]; omega
  have hLlen : L.length = N := by
    simp only [L, List.length_take, List.length_drop, Nat.min_eq_left hNbound]
  have hcell (n : Fin N) : b.val + n.val < R.length := by omega
  have hget (n : Fin N) : L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm) =
      R[b.val + n.val]'(hcell n) := by
    simp only [L, List.getElem_take, List.getElem_drop]
  have hjstart : R[j.val].input.time.val = R[b.val].input.time.val + (j.val - b.val) := by
    rw [htimej, htimeb]
    omega
  have hscanEndpoint' : ell = scan.endpoint := by
    dsimp [ell, u, bits]
    exact hscanEndpoint.symm
  have huPos : sigma < u := by
    have hpositive : 1 ≤ u - sigma := by simpa [u, sigma, bits] using hpositiveL
    omega
  have hjEndpoint : sigma < endpointRound := by
    dsimp [endpointRound]
    rw [hsigtime, hjstart]
    have hbj : b.val ≤ j.val := hblR
    omega
  have hltEll : sigma < ell := by
    dsimp [ell]
    exact lt_min huPos hjEndpoint
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.sub_pos_of_lt hltEll
  have hminSub : min u endpointRound - sigma ≤ u - sigma :=
    min_sub_le_left u endpointRound sigma
  have hdle : d ≤ N := by
    simpa only [d, N, ell, endpointRound] using hminSub
  have hcount : j.val - b.val + 1 ≤ R.length - b.val := by omega
  obtain ⟨span, mode, hfull⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_input_suffix_reindex
      (rate := rate) rewards C_star C_h source b (j.val - b.val + 1) (by omega)
  obtain ⟨priorSpan, priorMode, hprior⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_input_suffix_reindex
      (rate := rate) rewards C_star C_h source b (j.val - b.val) (by omega)
  let birthRecord := R[b.val]
  let birthInput := birthRecord.input
  let birthState := birthInput.state
  let s := birthInput.time.val
  let l := j.val - b.val
  have htimeBuffer : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ s := by
    change ∀ saved ∈ seed.buffer, saved.calendarRound ≤ P.sigma.val at hbufferTime
    rw [hbtime] at hbufferTime
    exact hbufferTime
  have hwindow : selectedViewInterval s ((R.drop b.val).take l) := by
    change selectedViewInterval P.sigma.val ((R.drop b.val).take l) at hwindowB
    rw [hbtime] at hwindowB
    exact hwindowB
  obtain ⟨hqueue, hnoReset, hendpoint⟩ := restarted_recovery_prefix
    birthState source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards s l span mode R b j (by dsimp [l]; omega) hfull hprior i seed logged after
    seedMemory hseed hbufferValid hbufferPair htimeBuffer cut raw M scan registers lastService
    hlogged hdown houtcome (by simpa only [s] using hsigma) hwindow
  have hQEd : ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell =
      ((R.drop b.val).take d).map (fun r => (true, emissionContribution M i r)) := by
    rw [← hscanEndpoint'] at hqueue
    rw [hMsigma] at hqueue
    exact hqueue
  have hselectedN : ∀ n : Fin N, ∃ v : Selection
      (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input,
      (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).output.preparation.coordinator.selection = some v ∧
      v.view.payload = P ∧ v.view.cutoff = none ∧
      CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
        (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input.time ∧
      ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
        (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
        (∀ f, (ReferenceFollowerFixedReply.actualChoice
          (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) f).configuration =
            .ordinary (states f) (memories f)) ∧
        (∀ f, (states f).status ≠ .unoccupied →
          (states f).lastDown = some (P.downRecord f)) := by
    intro n
    simpa only [P] using hselectedL ⟨n.val, Nat.lt_of_lt_of_eq n.isLt hLlen.symm⟩
  choose v hvselect hpayload hcut hlive states memories hactual hstatus using hselectedN
  have hprepared (n : Fin N) := prepared_of_actual
    (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (states n) (memories n) (hactual n)
  choose ho hstateAlign hmemAlign using hprepared
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
  let Ed := ((R.drop b.val).take d).map (fun r => (true, emissionContribution M i r))
  let Q := ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell
  let V := fun count => QueueReplay.replay cap (0, M.val.q) (A.take count)
  have hchoiceActual (n : Fin N) (f : Fin (p.m - 1)) :
      (ReferenceFollowerFixedReply.actualChoice
        (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) f).configuration =
        .ordinary
          (ReferenceLaterLiveNumericalReadout.preparedStates
            (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n) f)
          (ReferenceLaterLiveNumericalReadout.preparedMemories
            (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n) f) := by
    rw [hstateAlign n, hmemAlign n]
    exact hactual n f
  obtain ⟨hcLaunch, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source b
  have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate source rewards C_star C_h hcLaunch
  have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate source rewards C_star C_h
    (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcLaunch) hlaunch
  have hdj : d ≤ l + 1 := by
    have hms : M.val.sigma = s + 1 := by simpa only [s] using hsigma
    change ell - sigma ≤ l + 1
    rw [hscanEndpoint']
    change scan.endpoint - (P.sigma.val + 1) ≤ l + 1
    rw [← hMsigma, hms]
    omega
  have hUnoccupied (n : Fin d) :
      (states ⟨n.val, by omega⟩ i).status = .unoccupied := by
    let f : Fin N := ⟨n.val, by omega⟩
    have hbirthChoice : (ReferenceFollowerFixedReply.actualChoice R[b.val] i).configuration =
        .ordinary seedChoice seedMemory := hchoiceSeed
    have hright : (ReferenceFollowerFixedReply.actualChoice
        (R[b.val + f.val]'(hcell f)) i).configuration =
        .ordinary (states f i) (memories f i) := by
      have hgetL : L[f.val]'(Nat.lt_of_lt_of_eq f.isLt hLlen.symm) =
          R[b.val + f.val]'(hcell f) := hget f
      rw [← hgetL]
      exact hactual f i
    exact unoccupied_choice_of_no_reset hchain i b.val l f.val b.isLt (hcell f)
      (by have hn := n.isLt; dsimp only [f]; omega) seedChoice (states f i)
      seedMemory (memories f i) hbirthChoice hright hchoiceStatus hnoReset
  have hentry (n : Fin N) (hn : n.val < d) :
      A[n.val]'(by simpa only [A, List.length_ofFn] using n.isLt) =
        (true, emissionContribution M i (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm))) := by
    let f : Fin N := ⟨n.val, by omega⟩
    let r := L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)
    have hr : r = R[b.val + n.val]'(hcell f) := by simpa [r, f] using hget f
    have hu : (states f i).status = .unoccupied := by
      simpa only [f] using hUnoccupied ⟨n.val, hn⟩
    have harrival := selected_cell_arrival (rate := rate) rewards C_star C_h source
      ⟨b.val + n.val, hcell f⟩ r hr (v f) (hvselect f) (hlive f) (ho f) i
      (by rw [hstateAlign f]; exact hu)
    have hcellArrival : RecordedQueueRun.quantizedArrival qp (Cells f) a =
        emissionContribution M i r := by
      simpa only [Cells, qp, hpayload f, M, a, r, f] using harrival
    have henabled : (Cells f).enabled = true := by
      dsimp [Cells]
      exact ReferenceFirstWindowNumericalStream.sourceCell_enabled
        r (v f).view.payload (v f).view.pendingAtChoice
        (ReferenceLaterLiveNumericalReadout.preparedStates r (ho f))
        (v f).view.complementWeights (v f).view.cutoff
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v f))
    rw [List.getElem_ofFn]
    change ((Cells f).enabled, RecordedQueueRun.quantizedArrival qp (Cells f) a) = _
    rw [henabled, hcellArrival]
  have hEdA : Ed = A.take d := by
    have hEdL : Ed = (L.take d).map (fun r => (true, emissionContribution M i r)) := by
      dsimp only [Ed, L]
      rw [List.take_take, Nat.min_eq_left hdle]
    rw [hEdL]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, hLlen, A, List.length_ofFn,
        Nat.min_eq_left hdle]
    · intro n hnEd hnA
      have hn : n < d := by
        simp only [List.length_map, List.length_take, hLlen, Nat.min_eq_left hdle] at hnEd
        exact hnEd
      simp only [List.getElem_map, List.getElem_take]
      exact (hentry ⟨n, by omega⟩ hn).symm
  have hAlen : A.length = N := by simp [A]
  have hallEnabled : ∀ x ∈ A, x.1 = true := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hx
    simp [A, Cells, ReferenceFirstWindowNumericalStream.sourceCell]
  have hcheckedEll : ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell =
      .ok ⟨registers, lastService⟩ := by
    rw [hscanEndpoint']
    exact hchecked
  obtain ⟨hregistersV, hlastV⟩ := checked_recovery_calendar_delta M logged ell
    registers lastService (by rw [hMsigma]; exact hltEll) hcheckedEll A d
    (by dsimp only [d]; rw [hMsigma]) (hQEd.trans hEdA)
  have htimeMapAll : L.map (fun r => r.input.time.val + 1) = List.range' sigma N :=
    htimesL
  refine ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
    hchoice, hblR, hjkR, hbirth, hretained, hlogged, hdown, houtcome, ?_⟩
  change ell = scan.endpoint ∧ _
  refine ⟨hscanEndpoint', hcheckedEll, P.downRecord_initialQueue i,
    hdpos, hdle, htimeMapAll, ?_⟩
  refine ⟨hLlen, v, ho, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact ⟨hvselect n, hpayload n, hcut n, hlive n⟩
  · exact hchoiceActual
  · exact ⟨hQEd, hEdA, hAlen, hallEnabled, hregistersV, hlastV⟩

end Bandits.Support.ReferenceCompleteFollowerRecoveryCalendarJoin

end
