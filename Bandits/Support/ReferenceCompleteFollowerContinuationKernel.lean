/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteFollowerRetainedDownRecovery

import Lean.Elab.Tactic.Omega

/-!
# Actual follower continuation kernels

Sources: `sources/zip4/manuscript/05_binary_transport.tex:60-88,354-431`,
`sources/zip4/manuscript/06_interruptions.tex:110-121,192-233,246-349`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-84`.

These internal kernels continue the existing complete physical history from an
actual accepted DOWN diagnostic or an actual occupied successor. They retain
the original source, whole reward table, selected row, and follower memory.
All executed-branch and calendar-cell inputs are explicit in the statements;
there is no occupied-trajectory, queue-replay, or service-success premise.

The acceptance kernel returns the actual successor memory. If acceptance is
live through the current round, that memory contains its real FinishRound
proposal read. The empty-tail kernel handles both late acceptance and pending
acceptance immediately before cutoff, interrupting at the next StartRound.

For a nonempty tail, induction proves online service on every remaining
calendar date, including enabled zero arrivals. Disabled entries preserve the
queue registers. Only the focal occupied recorder event is compared between
current source weights and anchor weights; no whole-kernel equality is used.
At the first cutoff the follower becomes unoccupied before arm choice and
retains the terminal registers, without an occupied cutoff-date update.

`ReferenceCompleteFollowerTerminalReplyAssembly` is the intended consumer. It
must produce these local inputs from its single accepted-UP recovery/calendar
join and preserve those same witnesses when applying the kernels. This module
does not construct that join, identify the terminal reply, identify a global
queue, or close any manuscript theorem.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteFollowerContinuationKernel

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence
open ReferenceFollowerReplyChronology

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- An actual accepted DOWN installs the diagnostic status and the same
successor memory. At a live endpoint the proposal token is the actual
FinishRound read, after the unoccupied-at-choice release branch. -/
theorem accepted_down_successor_token
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) (i : Fin (p.m - 1))
    (logged after : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (hlogged : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[j.val].output.followers i).downInput = some logged)
    (hdown : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[j.val].output.followers i).down = some cut)
    (houtcome : cut.outcome = .accepted logged after raw M scan registers lastService) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[j.val]
    after.status = (if scan.endpoint = r.input.time.val + 2 then .pending else .unoccupied) ∧
    ∃ nextMemory : ActiveFollowerLifecycle.LocalMemory p,
      r.output.next.followers i = .ordinary after nextMemory ∧
      (scan.endpoint = r.input.time.val + 2 →
        nextMemory.lastProposalRead = some ⟨r.input.time,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time⟩) := by
  classical
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[j.val]
  have htransition := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
    r i logged cut after raw M scan registers lastService hlogged hdown houtcome
  obtain ⟨_, _, hsigma, _, _, _, hafter⟩ :=
    ActiveFollowerDownAcceptance.downTransition_accepted_checked p _ _ _ _ rate
      logged after raw M scan registers lastService htransition
  have halign := r.output.preparation.follower_alignment i
  have hstatus : after.status =
      (if scan.endpoint = r.input.time.val + 2 then .pending else .unoccupied) := by
    rw [hafter]
    simp only [halign.2.2.1]
  obtain ⟨_, memory, choice, next, nextMemory, _, hchoice, _, hdomain,
    hconfiguration, _, hnext⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_output
      (rate := rate) rewards C_star C_h source j i
  have hchoice' : (r.output.preparation.followers.followers i).configuration =
      .ordinary choice memory := hchoice
  obtain ⟨hfinish, hnextAfter⟩ :=
    ReferenceFirstLiveDownNumericalRecovery.accepted_down_release_finish_frame
      r i choice memory hchoice' logged after cut raw M scan registers lastService
      hlogged hdown houtcome next nextMemory hconfiguration
  subst next
  refine ⟨hstatus, nextMemory, hnext, ?_⟩
  intro hendpoint
  have hoccupied : after.status ≠ .unoccupied := by
    rw [hstatus, ite_eq_left hendpoint]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  obtain ⟨choiceD, memoryD, _, hchoiceD, huD, _, _, _⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hdown
  have heq : choiceD = choice :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hchoiceD.symm.trans hchoice')).1
  have hunoccupied : choice.status = .unoccupied := heq ▸ huD
  have hlast : after.lastDown = some M := by rw [hafter]
  have htime : M.val.sigma ≤ (r.output.preparation.followers.followers i).time.val + 1 := by
    rw [halign.2.2.1]
    rw [hendpoint] at hsigma
    omega
  unfold DeclaredFollowerLocalRound.releaseAndFinish at hfinish
  simp only [halign.1, halign.2.1, halign.2.2.1] at hfinish
  rw [ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta i r.input.time
    (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
    (r.output.preparation.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    choice after hunoccupied] at hfinish
  rw [halign.2.2.1] at htime
  dsimp only at hfinish
  rw [ActiveFollowerLifecycle.finishRound_occupied_read rate.eta r.input.time r.input.row
    after memory hoccupied hdomain M hlast htime] at hfinish
  have hmem := (Prod.mk.inj (Except.ok.inj hfinish)).2
  rw [← hmem]

private theorem occupied_fixed_event
    (P : Payload rate) (snapshot : ActiveRoundActions.Snapshot P.assignment)
    (i : Fin (p.m - 1)) (hoccupied : snapshot.status i ≠ .unoccupied)
    (w : Fin p.K → ℝ) (hw : ∀ a, 0 < w a)
    (hlower : ∀ a, P.anchor a ≤ w a) (hupper : ∀ a, w a ≤ 2 * P.anchor a) :
    {x | SnapshotRecordingKernel.recordingMap p (.live P.assignment snapshot)
      true rate.eta.val rate.eta.property rate.sourceCap P.anchor w P.anchor_pos hw
      hlower hupper x = some (P.assignment.assigned i)} =
    {x | CanonicalRecordingSlice.deterministicOwnedRecordingGate p.two_le_m
      p.m_lt_K (ConstructorDimensions.K_pos p) (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      (P.assignment.assigned i)
      (CanonicalRecordingRates.xi p rate.eta.val P.anchor (P.assignment.assigned i) /
        CanonicalRecordingSlice.deterministicOwnedGateRawProbability (K := p.K)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) x} := by
  have hsource := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
  have hindex := ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hsource
  apply SnapshotRecordingKernel.recordingMap_fixed_event_eq
  · simp only [SnapshotRecordingKernel.owns, hsource, dite_false, hindex]
  · intro x
    simp only [SnapshotRecordingKernel.dataAction, hsource, dite_false, hindex,
      hoccupied]
  · simp only [SnapshotRecordingKernel.actionProbability, hsource, dite_false,
      hindex, hoccupied, eq_self, dite_true]

private theorem occupied_sourceArm_gate
    (r : RoundRecord (p := p) (rate := rate)) (v : Selection r.input)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (i : Fin (p.m - 1)) (hoccupied : (states i).status ≠ .unoccupied) :
    ActiveFollowerQueueOperation.recorderGate rate.eta i r.input.row r.input.time
      (v.view.payload.downRecord i) ↔
    ReferenceFirstWindowNumericalStream.sourceArm r v.view.payload v.view.pendingAtChoice
      states v.view.complementWeights v.view.cutoff
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid v) =
      some (v.view.payload.assignment.assigned i) := by
  let P := v.view.payload
  let snapshot := ReferenceActiveDataOwnership.choiceSnapshot v states
  have hstatus : (states i).status.occupied := by
    cases hs : (states i).status with
    | unoccupied => exact False.elim (hoccupied hs)
    | pending => exact Or.inl rfl
    | released => exact Or.inr rfl
  have hgate := ReferenceFollowerOccupiedRecorderEvent.occupiedGate_eq_canonicalRecordingMap
    P snapshot i r.input.row r.input.time (states i) rfl hstatus
  have hsnapshot : snapshot.status i ≠ .unoccupied := hoccupied
  have hanchor := occupied_fixed_event P snapshot i hsnapshot P.anchor P.anchor_pos
    (fun _ => le_rfl) (fun a => by
      rw [two_mul]
      exact le_add_of_nonneg_right (le_of_lt (P.anchor_pos a)))
  have hcurrent := occupied_fixed_event P snapshot i hsnapshot
    (ReferenceFirstWindowNumericalStream.sourceWeights P v.view.complementWeights)
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos P v.view.complementWeights
      v.view.cutoff r.input.time (ReferenceLaterLiveNumericalReadout.selection_choiceValid v))
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower P v.view.complementWeights
      v.view.cutoff r.input.time (ReferenceLaterLiveNumericalReadout.selection_choiceValid v))
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper P v.view.complementWeights
      v.view.cutoff r.input.time (ReferenceLaterLiveNumericalReadout.selection_choiceValid v))
  have hevent := Set.ext_iff.mp (hanchor.trans hcurrent.symm)
    ((r.input.row.2 r.input.time).1)
  apply hgate.trans
  simpa only [Set.mem_ofPred_eq, ReferenceFirstWindowNumericalStream.sourceArm,
    ReferenceActiveDataOwnership.choiceSnapshot, P, snapshot, ← v.pending_eq] using hevent

/-- Pointwise online continuation uses the literal prepared-state numerical
cell at the actual selection. Service includes every enabled zero arrival.
The returned memory is the actual post-service proposal read. -/
private theorem complete_prepared_occupied_cell_service
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (v : Selection (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input)
    (hv : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].output.preparation.coordinator.selection = some v)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.time)
    (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val])
    (i : Fin (p.m - 1))
    (hoccupied : (ReferenceLaterLiveNumericalReadout.preparedStates
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val] ho i).status ≠ .unoccupied) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]
    let states := ReferenceLaterLiveNumericalReadout.preparedStates r ho
    let cell := ReferenceFirstWindowNumericalStream.sourceCell r v.view.payload
      v.view.pendingAtChoice states v.view.complementWeights v.view.cutoff
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid v)
    let arrival := RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
      (v.view.payload.assignment.assigned i)
    ∃ next nextMemory,
      r.output.next.followers i = .ordinary next nextMemory ∧
      next.status ≠ .unoccupied ∧ next.lastDown = (states i).lastDown ∧
      (next.S, next.backlog) = QueueReplay.transition (4 * rate.n)
        ((states i).S, (states i).backlog) (cell.enabled, arrival) ∧
      next.delta = next.S - (states i).S ∧
      nextMemory.lastProposalRead = some ⟨r.input.time,
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time⟩ := by
  classical
  dsimp only
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]
  let states := ReferenceLaterLiveNumericalReadout.preparedStates r ho
  let memories := ReferenceLaterLiveNumericalReadout.preparedMemories r ho
  have hactual (f : Fin (p.m - 1)) :
      (ReferenceFollowerFixedReply.actualChoice r f).configuration =
        .ordinary (states f) (memories f) :=
    ReferenceLaterLiveNumericalReadout.prepared_configuration r ho f
  obtain ⟨otherStates, otherMemories, _, hother, _, _, hservice⟩ :=
    ReferenceCompleteOccupiedFollowerDataArrival.complete_selected_occupied_follower_arrival_service
      (rate := rate) rewards C_star C_h source k v hv hlive
  have heq (f : Fin (p.m - 1)) : otherStates f = states f :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((hother f).symm.trans (hactual f))).1
  have hstates : otherStates = states := funext heq
  subst otherStates
  obtain ⟨serviced, next, nextMemory, _, _, _, _, _, _, _, _, _, _, hnext,
    hS, hdelta, _, htransition, hlast, _, _, _, _⟩ := hservice i hoccupied
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, nextF, memoryF,
    _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, hocc, htoken, _, _, _, _, hnext'⟩ :=
    ReferenceCompleteOccupiedServiceForward.complete_ordinary_occupied_service_forward
      (rate := rate) rewards C_star C_h source k i (states i) (memories i) (hactual i) hoccupied
  have hpair := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hnext'.symm.trans hnext)
  have hgate := occupied_sourceArm_gate r v states i hoccupied
  have harrival : RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (ReferenceFirstWindowNumericalStream.sourceCell r v.view.payload v.view.pendingAtChoice
        states v.view.complementWeights v.view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid v))
      (v.view.payload.assignment.assigned i) =
      if ActiveFollowerQueueOperation.recorderGate rate.eta i r.input.row r.input.time
        (v.view.payload.downRecord i) then
        Nat.floor ((D p : ℝ) * rate.eta.val *
          (((rewards r.input.time (v.view.payload.assignment.assigned i)).val : ℝ) / (D p : ℝ)) /
          OrdinaryMessageCodec.dyadicRate (v.view.payload.downRecord i).val.h)
      else 0 := by
    rw [ReferenceFirstWindowNumericalStream.sourceCell_quantizedArrival]
    have hreward : r.input.rewards = rewards := by
      obtain ⟨_, _, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
        rate rewards C_star C_h source k
      change (List.get _ k).input.rewards = rewards
      rw [hr]
      rfl
    rw [hreward, v.view.payload.downRecord_rate i, v.view.payload.rate_eq_canonical]
    have hn : (rate.n : ℝ) = (D p : ℝ) * rate.eta.val := by
      rw [rate.n_scale, mul_comm]
    rw [hn]
    exact if_congr hgate.symm rfl rfl
  refine ⟨next, nextMemory, hnext, ?_, hlast, ?_, ?_, ?_⟩
  · exact hpair.1 ▸ hocc
  · change (next.S, next.backlog) = QueueReplay.transition (4 * rate.n)
      ((states i).S, (states i).backlog)
      ((ReferenceFirstWindowNumericalStream.sourceCell r v.view.payload v.view.pendingAtChoice
        states v.view.complementWeights v.view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid v)).enabled, _)
    rw [ReferenceFirstWindowNumericalStream.sourceCell_enabled, harrival]
    exact htransition
  · change next.delta = next.S - (states i).S
    rw [hdelta, hS]
    omega
  · exact hpair.2 ▸ htoken

private theorem connected_next
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (chain : Connected initial records final)
    (n : ℕ) (hn : n + 1 < records.length) :
    records[n + 1].input.state = records[n].output.next := by
  have hs := connected_drop_from_output chain n (by omega)
  have ht := connected_take_to_input hs 0 (by simp only [List.length_drop]; omega)
  simpa only [List.take_zero, Connected, List.getElem_drop, Nat.add_zero] using ht

private theorem first_cutoff_test
    (sigma t prior : Fin p.T) (bits : Fin p.T → Bool)
    (hstart : sigma.val < t.val) (hprior : prior.val + 1 = t.val)
    (hle : t.val + 1 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits) :
    (FollowerCutoffScan.gridBoundary p rate.eta.val sigma = t.val + 1 ∨
      bits prior = true) ↔
      FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits = t.val + 1 := by
  classical
  let carrier := FollowerCutoffScan.firstCutoffCarrier p rate.eta.val sigma bits
  have hmin : FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits =
      carrier.min' (FollowerCutoffScan.firstCutoffCarrier_nonempty _ _ _ _) := rfl
  constructor
  · intro h
    have hmem : t.val + 1 ∈ carrier := by
      rcases h with hg | hb
      · exact hg ▸ Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        refine ⟨prior, Finset.mem_filter.mpr ⟨?_, hb⟩, ?_⟩
        · simp only [FollowerCutoffScan.proposalCoordinates, Finset.mem_filter,
            Finset.mem_univ, true_and]
          omega
        · simp only [FollowerCutoffScan.proposalEndpoint]
          omega
    have hm := Finset.min'_le carrier (t.val + 1) hmem
    omega
  · intro he
    have hm : FollowerCutoffScan.firstCutoff p rate.eta.val sigma bits ∈ carrier :=
      Finset.min'_mem _ _
    rw [he] at hm
    rcases Finset.mem_insert.mp hm with hg | hb
    · exact Or.inl hg.symm
    · obtain ⟨v, hv, ht⟩ := Finset.mem_image.mp hb
      have hvbit := (Finset.mem_filter.mp hv).2
      have heq : v = prior := by
        apply Fin.ext
        simp only [FollowerCutoffScan.proposalEndpoint] at ht
        omega
      exact Or.inr (heq ▸ hvbit)

/-- One occupied StartRound, using the actual prior proposal token, preserves
all registers and interrupts exactly at the first cutoff. This local branch
lemma performs no service on the cutoff round. -/
private theorem occupied_start_first_cutoff_frame
    (P : Payload rate) (i : Fin (p.m - 1))
    (t prior : Fin p.T) (bits : Fin p.T → Bool)
    (before choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta t before memory = .ok (choice, memory))
    (hoccupied : before.status ≠ .unoccupied)
    (hlast : before.lastDown = some (P.downRecord i))
    (hstarted : P.sigma.val < t.val)
    (hprior : prior.val + 1 = t.val)
    (hread : memory.lastProposalRead = some ⟨prior, bits prior⟩)
    (hle : t.val + 1 ≤ FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits) :
    choice = {before with status :=
      if FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits = t.val + 1
      then .unoccupied else before.status} := by
  classical
  have hvalid : ActiveFollowerLifecycle.localStateDomainValid before := by
    by_contra hn
    simp only [ActiveFollowerLifecycle.startRound,
      ActiveFollowerLifecycle.interruptionDecision_invalid_domain rate.eta t before memory hn]
      at hstart
    cases hstart
  have hcoordinate : ActiveFollowerLifecycle.acceptedStartCoordinate (P.downRecord i) = P.sigma := by
    apply Fin.ext
    have hc := ActiveFollowerLifecycle.accepted_start_coordinate_one_based (P.downRecord i)
    have hf : (P.downRecord i).val.sigma = P.sigma.val + 1 :=
      congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
    omega
  have hbounds := FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
    rate.eta.property rate.sourceCap P.sigma bits
  have hMsigma : (P.downRecord i).val.sigma = P.sigma.val + 1 :=
    congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
  have hnotmissed : t.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
      (ActiveFollowerLifecycle.acceptedStartCoordinate (P.downRecord i)) := by
    rw [hcoordinate]
    exact hle.trans hbounds.2
  have hbranch := ActiveFollowerLifecycle.startRound_occupied_branch rate.eta t before memory
    hoccupied hvalid (P.downRecord i) hlast (by omega) hnotmissed
    ⟨prior, bits prior⟩ hread hprior
  have hchoice := (Prod.mk.inj (Except.ok.inj (hstart.symm.trans hbranch))).1
  have htest := first_cutoff_test P.sigma t prior bits hstarted hprior hle
  have hbool : ((decide (FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma = t.val + 1)) ||
      bits prior) = true ↔
      FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits = t.val + 1 := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using htest
  rw [hchoice]
  simp only [hcoordinate]
  simp only [hbool]

/-- Acceptance with no remaining service tail yields an actual unoccupied
choice on the next date. Equality at the scan endpoint first installs pending,
then the next StartRound interrupts it; late acceptance is already unoccupied. -/
theorem accepted_down_next_cutoff_choice
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) (i : Fin (p.m - 1))
    (P : Payload rate)
    (logged after : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (hlogged : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[j.val].output.followers i).downInput = some logged)
    (hdown : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[j.val].output.followers i).down = some cut)
    (houtcome : cut.outcome = .accepted logged after raw (P.downRecord i) scan registers lastService)
    (hnextBound : j.val + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hscan : scan.endpoint = min
      (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[j.val].input.row))
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[j.val].input.time.val + 2))
    (htail : FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[j.val].input.row) ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[j.val].input.time.val + 2) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ terminal memory,
      (ReferenceFollowerFixedReply.actualChoice (R[j.val + 1]'hnextBound) i).configuration =
        .ordinary terminal memory ∧ terminal.status = .unoccupied ∧
      terminal.lastDown = some (P.downRecord i) ∧
      (terminal.S, terminal.backlog) = registers ∧ terminal.delta = lastService := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let a : Fin R.length := ⟨j.val + 1, hnextBound⟩
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val R[j.val].input.row
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
  change scan.endpoint = min u (R[j.val].input.time.val + 2) at hscan
  change u ≤ R[j.val].input.time.val + 2 at htail
  obtain ⟨hlast, hS, hd, hq, _, _⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_down_output
      (rate := rate) rewards C_star C_h source j i logged after cut raw (P.downRecord i)
      scan registers lastService hlogged hdown houtcome
  obtain ⟨hstatus, nextMemory, hnext, htoken⟩ := accepted_down_successor_token
    rewards C_star C_h source j i logged after cut raw (P.downRecord i)
    scan registers lastService hlogged hdown houtcome
  change after.status = (if scan.endpoint = R[j.val].input.time.val + 2 then
    .pending else .unoccupied) at hstatus
  rw [hscan, Nat.min_eq_left htail] at hstatus
  obtain ⟨before, memory, terminal, hinput, hdomain, hstart, hchoice, _, _⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h source a i
  obtain ⟨crossing, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source j
  have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate source rewards C_star C_h
    (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h crossing)
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source rewards C_star C_h crossing)
  have hinput' : R[a.val].input.state.followers i = .ordinary after nextMemory :=
    (congrArg (fun st => st.followers i) (connected_next hchain j.val hnextBound)).trans hnext
  obtain ⟨heBefore, heMemory⟩ :=
    DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hinput.symm.trans hinput')
  subst before
  subst memory
  have hframe := ActiveFollowerLifecycle.startRound_frame rate.eta _ _ _ _ _ hstart
  have hprior : R[j.val].input.time.val + 1 = R[a.val].input.time.val := by
    have hj := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source j
    have ha := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source a
    change R[j.val].input.time.val = _ at hj
    change R[a.val].input.time.val = _ at ha
    rw [hj, ha]
    dsimp only [a]
    omega
  have hterminal : terminal.status = .unoccupied := by
    by_cases he : u = R[j.val].input.time.val + 2
    · have hpending : after.status = .pending := by rw [hstatus, ite_eq_left he]
      have hread : nextMemory.lastProposalRead = some ⟨R[j.val].input.time,
          bits R[j.val].input.time⟩ := by
        apply htoken
        rw [hscan, Nat.min_eq_left htail, he]
      have hbound := (FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
        rate.eta.property rate.sourceCap P.sigma bits).1
      change P.sigma.val + 1 < u at hbound
      have hfirst := occupied_start_first_cutoff_frame P i R[a.val].input.time
        R[j.val].input.time bits after terminal nextMemory hstart
        (by rw [hpending]; simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hlast
        (by omega) hprior hread (by omega)
      have hcut : FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits =
          R[a.val].input.time.val + 1 := by change u = _; omega
      rw [hfirst]
      simp only [hcut, ite_true]
    · have hunoccupied : after.status = .unoccupied := by rw [hstatus, ite_eq_right he]
      have hnoop := ActiveFollowerLifecycle.startRound_unoccupied rate.eta
        R[a.val].input.time after nextMemory hdomain hunoccupied
      have heq := (Prod.mk.inj (Except.ok.inj (hstart.symm.trans hnoop))).1
      exact heq ▸ hunoccupied
  refine ⟨terminal, nextMemory, hchoice, hterminal, hframe.1.trans hlast, ?_,
    hframe.2.2.1.trans hd⟩
  rw [hframe.2.1, hframe.2.2.2.1, hS, hq]

/-- Successive prefixes of the literal service tail satisfy the queue replay
recurrence, with the original calendar entry at position `v`. Zero arrivals
and disabled entries retain their literal queue-transition meanings. -/
private theorem replay_service_tail_step
    (capacity : ℕ) (registers : ℕ × ℕ) (A : List (Bool × ℕ))
    (d v : ℕ) (hdv : d ≤ v) (hv : v < A.length) :
    QueueReplay.replay capacity registers ((A.drop d).take (v + 1 - d)) =
      QueueReplay.transition capacity
        (QueueReplay.replay capacity registers ((A.drop d).take (v - d))) A[v] := by
  have hindex : v - d < (A.drop d).length := by
    rw [List.length_drop]
    omega
  have hsucc : v + 1 - d = (v - d) + 1 := by omega
  rw [hsucc, List.take_succ_eq_append_getElem hindex, QueueReplay.replay_append]
  simp only [QueueReplay.replay, List.foldl_cons, List.foldl_nil, List.getElem_drop,
    Nat.add_sub_of_le hdv]

private theorem calendar_time_arithmetic (start birth n sigma t prior : ℕ)
    (hb : sigma = start + birth) (ht : t = start + (birth + n))
    (hp : prior = start + (birth + n - 1)) (hn : 0 < n) :
    sigma < t ∧ prior + 1 = t ∧ t + 1 = sigma + 1 + n := by omega

/-- The actual StartRound at a calendar position uses the preceding token. -/
private theorem complete_occupied_calendar_start
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (P : Payload rate) (i : Fin (p.m - 1))
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) (n : ℕ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
    let N := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits - (P.sigma.val + 1)
    ∀ (_hn : 0 < n) (_hnN : n ≤ N) (hbound : b.val + n < R.length),
      R[b.val].input.time.val = P.sigma.val →
      ∀ state memory,
      R[b.val + n].input.state.followers i = .ordinary state memory →
      state.status ≠ .unoccupied → state.lastDown = some (P.downRecord i) →
      memory.lastProposalRead = some ⟨(R[b.val + n - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) hbound)).input.time,
        bits (R[b.val + n - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) hbound)).input.time⟩ →
      ∃ choice, (ReferenceFollowerFixedReply.actualChoice R[b.val + n] i).configuration =
        .ordinary choice memory ∧
        choice = {state with status := if n = N then .unoccupied else state.status} := by
  classical
  intro R bits N hn hnN hbound hbtime state memory hin hocc hlast hread
  let q : Fin R.length := ⟨b.val + n, hbound⟩
  obtain ⟨before, mem, choice, hin', _, hstart, hchoice, _, _⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h source q i
  obtain ⟨he, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hin'.symm.trans hin)
  subst before
  subst mem
  have hq : q.val = b.val + n := rfl
  have ht := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source q
  have hb := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source b
  have hp : (R[b.val + n - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) hbound)).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
        (b.val + n - 1) :=
    ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h source
      ⟨b.val + n - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hbound⟩
  change R[q.val].input.time.val = _ at ht
  change R[b.val].input.time.val = _ at hb
  have ht' : R[q.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + (b.val + n) :=
    ht.trans (congrArg (fun x =>
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + x) hq)
  have ha := calendar_time_arithmetic _ _ _ _ _ _ (hbtime.symm.trans hb) ht' hp hn
  have hu := (FollowerCutoffScan.firstCutoff_bounds p rate.eta.val rate.eta.property
    rate.sourceCap P.sigma bits).1
  have hNu : P.sigma.val + 1 + N = FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits := by
    exact Nat.add_sub_of_le hu.le
  have hf := occupied_start_first_cutoff_frame P i R[q.val].input.time
    (R[b.val + n - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) hbound)).input.time bits state choice memory hstart hocc hlast
    ha.1 ha.2.1 hread (by rw [ha.2.2, ← hNu]; exact Nat.add_le_add_left hnN _)
  have heq : (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits =
      R[q.val].input.time.val + 1) ↔ n = N := by
    rw [ha.2.2, ← hNu]
    rw [Nat.add_left_cancel_iff]
    exact eq_comm
  exact ⟨choice, hchoice, by simpa only [heq] using hf⟩

/-- An actual occupied successor traverses the complete selected calendar and
is interrupted before choice at its first cutoff. Inputs are local branch and
selection equations; the occupied trajectory and replay are proved here. -/
theorem complete_occupied_calendar_tail
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (P : Payload rate) (i : Fin (p.m - 1))
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) (d : ℕ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
    let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
    let N := u - (P.sigma.val + 1)
    ∀ (hbound : b.val + N < R.length),
      R[b.val].input.time.val = P.sigma.val →
      ∀ (hd : 0 < d) (hdN : d < N),
      ∀ (initial : ReferencePrelaunchFollower.State p rate.eta)
        (initialMemory : ActiveFollowerLifecycle.LocalMemory p)
        (registers : ℕ × ℕ) (lastService : ℕ) (A : List (Bool × ℕ)),
      (R[b.val + d]'(by omega)).input.state.followers i = .ordinary initial initialMemory →
      initial.status ≠ .unoccupied → initial.lastDown = some (P.downRecord i) →
      (initial.S, initial.backlog) = registers → initial.delta = lastService →
      initialMemory.lastProposalRead = some ⟨(R[b.val + d - 1]'(by omega)).input.time,
        bits (R[b.val + d - 1]'(by omega)).input.time⟩ →
      ∀ (hlength : A.length = N),
      (∀ n : Fin N, ∃ (v : Selection (R[b.val + n.val]'(by omega)).input)
          (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary (R[b.val + n.val]'(by omega))),
        (R[b.val + n.val]'(by omega)).output.preparation.coordinator.selection = some v ∧
        CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
          (R[b.val + n.val]'(by omega)).input.time ∧
        (A[n.val]'(by omega)) =
          let cell := ReferenceFirstWindowNumericalStream.sourceCell (R[b.val + n.val]'(by omega))
            v.view.payload v.view.pendingAtChoice
            (ReferenceLaterLiveNumericalReadout.preparedStates _ ho)
            v.view.complementWeights v.view.cutoff
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid v)
          (cell.enabled, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell
            (v.view.payload.assignment.assigned i))) →
      let W := fun v => QueueReplay.replay (4 * rate.n) registers ((A.drop d).take (v - d))
      ∃ terminal terminalMemory,
        (ReferenceFollowerFixedReply.actualChoice (R[b.val + N]'(by omega)) i).configuration =
          .ordinary terminal terminalMemory ∧
        terminal.status = .unoccupied ∧ terminal.lastDown = some (P.downRecord i) ∧
        (terminal.S, terminal.backlog) = W N ∧ terminal.delta = (W N).1 - (W (N - 1)).1 := by
  classical
  intro R bits u N hbound hbtime hd hdN initial initialMemory registers lastService A
    hinput hoccupied hlast hregisters hdelta htoken hlength hcalendar W
  obtain ⟨crossing, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source b
  have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate source rewards C_star C_h
    (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h crossing)
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source rewards C_star C_h crossing)
  have hinvariant : ∀ v (hdv : d ≤ v) (hvN : v ≤ N),
      ∃ state memory, (R[b.val + v]'(by omega)).input.state.followers i = .ordinary state memory ∧
        state.status ≠ .unoccupied ∧ state.lastDown = some (P.downRecord i) ∧
        (state.S, state.backlog) = W v ∧
        state.delta = (if d < v then (W v).1 - (W (v - 1)).1 else lastService) ∧
        memory.lastProposalRead = some ⟨(R[b.val + v - 1]'(by omega)).input.time,
          bits (R[b.val + v - 1]'(by omega)).input.time⟩ := by
    intro v hdv
    induction v, hdv using Nat.le_induction with
    | base =>
      intro _
      refine ⟨initial, initialMemory, hinput, hoccupied, hlast, ?_, ?_, htoken⟩
      · simpa only [W, Nat.sub_self, List.take_zero, QueueReplay.replay,
          List.foldl_nil] using hregisters
      · simpa only [lt_self_iff_false, ite_false] using hdelta
    | succ v hdv ih =>
      intro hvN
      obtain ⟨state, memory, hin, hocc, hdown, hregs, hdelt, hread⟩ := ih (by omega)
      let q : Fin R.length := ⟨b.val + v, by omega⟩
      let qnext : Fin R.length := ⟨b.val + (v + 1), by omega⟩
      obtain ⟨choice, hchoice, hframe⟩ := complete_occupied_calendar_start
        rewards C_star C_h source P i b v (by omega) (by change v ≤ N; omega) q.isLt
        hbtime state memory hin hocc hdown hread
      change choice = {state with status := if v = N then .unoccupied else state.status} at hframe
      have hechoice : choice = state := by
        simpa only [ite_eq_right (show v ≠ N by omega)] using hframe
      rw [hechoice] at hchoice
      obtain ⟨sel, ho, hsel, hlive, hentry⟩ := hcalendar ⟨v, by omega⟩
      have hprepared := ReferenceLaterLiveNumericalReadout.prepared_configuration R[q.val] ho i
      have hstate := (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hprepared.symm.trans hchoice)).1
      obtain ⟨next, nextMemory, hnext, hnextocc, hnextdown, hnextregs, hnextdelta, hnextread⟩ :=
        complete_prepared_occupied_cell_service rewards C_star C_h source q sel hsel hlive ho i
          (by rw [hstate]; exact hocc)
      have hq : q.val = b.val + v := rfl
      have hadj := connected_next (records := R) hchain q.val (by omega)
      have hnextinput : R[qnext.val].input.state.followers i = .ordinary next nextMemory := by
        have heq : qnext.val = q.val + 1 := by dsimp only [q, qnext]; omega
        simpa only [heq] using (congrArg (fun st => st.followers i) hadj).trans hnext
      have hstep : W (v + 1) = QueueReplay.transition (4 * rate.n) (W v) A[v] :=
        replay_service_tail_step _ _ _ d v hdv (by omega)
      have hpair : (next.S, next.backlog) = W (v + 1) := by
        rw [hstate, hregs] at hnextregs
        rw [hstep, hentry]
        exact hnextregs
      have hrow : R[q.val].input.row =
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
        obtain ⟨_, _, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
          rate rewards C_star C_h source q
        change (R.get q).input.row = _
        rw [hr]
        rfl
      refine ⟨next, nextMemory, hnextinput, hnextocc, ?_, hpair, ?_, ?_⟩
      · exact (hnextdown.trans (congrArg ReferencePrelaunchFollower.State.lastDown hstate)).trans hdown
      · rw [ite_eq_left (by omega), hnextdelta, hstate]
        have hS := congrArg Prod.fst hpair
        have hprev := congrArg Prod.fst hregs
        have hsub : v + 1 - 1 = v := by omega
        rw [hsub, ← hS, ← hprev]
      · have heq : b.val + (v + 1) - 1 = q.val := by dsimp only [q]; omega
        change nextMemory.lastProposalRead = some ⟨R[q.val].input.time,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val R[q.val].input.row
            R[q.val].input.time⟩ at hnextread
        rw [hrow] at hnextread
        simpa only [heq] using hnextread
  obtain ⟨state, memory, hin, hocc, hdown, hregs, hdelt, hread⟩ :=
    hinvariant N (by omega) (by omega)
  let q : Fin R.length := ⟨b.val + N, hbound⟩
  obtain ⟨terminal, hchoice, hframe⟩ := complete_occupied_calendar_start
    rewards C_star C_h source P i b N (by omega) (by change N ≤ N; exact le_rfl) hbound
    hbtime state memory hin hocc hdown hread
  change terminal = {state with status := if N = N then .unoccupied else state.status} at hframe
  have hterminal : terminal = {state with status := .unoccupied} := by
    simpa only [ite_true] using hframe
  refine ⟨terminal, memory, hchoice, ?_, ?_, ?_, ?_⟩
  · rw [hterminal]
  · simpa only [hterminal] using hdown
  · simpa only [hterminal] using hregs
  · simpa only [hterminal, ite_eq_left hdN] using hdelt

end Bandits.Support.ReferenceCompleteFollowerContinuationKernel

end
