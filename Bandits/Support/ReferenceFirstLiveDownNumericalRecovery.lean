/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveUnoccupiedEmission
public import Bandits.Support.ReferenceFirstDownZeroRecovery

import Lean.Elab.Tactic.Omega

/-!
# First-live DOWN recovery on the original numerical source stream

Sources: `sources/zip4/manuscript/06_interruptions.tex:192-233,246-295,391-408`,
`sources/zip4/manuscript/05_binary_transport.tex:354-396,426-431`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

The retained diagnostic selects an actual internal branch. The original launch,
whole rows, reward table and private source are kept throughout. Calendar cells
with zero arrivals remain enabled cells. These results concern the first live
assignment's first retained DOWN, not subsequent occupied service or collection,
and make no manuscript or regret closure claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower

namespace Bandits.Support.ReferenceFirstLiveDownNumericalRecovery

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev RoundRecord {p : Parameters} {rate : RateInput p} :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable {p : Parameters} {rate : RateInput p}

/-- Geometry of every actual first-live record, obtained from the live prefix
after that record, the original clock and the first installation birth. -/
theorem first_live_geometry
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : RewardTable p) (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (hfirst : initial.coordinator = .first) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ (k : Fin W.length) (selected : ReferenceActivePhysicalStep.Selection W[k.val].input),
      W[k.val].output.preparation.coordinator.selection = some selected →
      selected.view.payload.sigma.val = start ∧
      W[k.val].input.time.val = start + k.val ∧
      W[k.val].input.time.val + 2 ≤
        FollowerCutoffScan.gridBoundary p rate.eta.val selected.view.payload.sigma ∧
      ∀ t : Fin p.T, start ≤ t.val → t.val < W[k.val].input.time.val →
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J) t = false := by
  intro E W k selected hselected
  have hw : W.length ≤ count :=
    (List.takeWhile_prefix _).length_le.trans_eq
      (ReferenceActivePhysicalHorizon.run_record_count
        initial rows J rewards start count hspan active)
  obtain ⟨hstep, hactual, _⟩ := ReferenceFirstLiveUnoccupiedEmission.window_record_eq_candidate
    initial rows J rewards start count hspan active k
  have htime : W[k.val].input.time.val = start + k.val := by rw [hactual]; rfl
  have hsafe := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
    initial rows J rewards start count hspan active hfirst
  have hkWindow : k.val + 1 ≤ W.length := Nat.succ_le_of_lt k.isLt
  have hkCount : k.val + 1 ≤ count := hkWindow.trans hw
  obtain ⟨r, q, base, hr⟩ := (hsafe.2.1 (k.val + 1) hkWindow).2 (by omega)
  obtain ⟨_, hsigma, _, ⟨birth, hbirth, hborn, hbirthTime, _⟩, hbits, _⟩ :=
    ReferenceFirstComplementReplay.run_first_complement_replay
      initial rows J rewards start count hspan active hfirst
      (k.val + 1) hkCount hkWindow r q base hr
  have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
    simp only [ReferenceCoordinatorClockDomains.clockAt, hfirst]
  have hclock := (ReferenceRunClockPreservation.run_clockAt
    initial rows J rewards start (k.val + 1) hstep active hseed).1
  simp only [ReferenceCoordinatorClockDomains.clockAt, hr] at hclock
  obtain ⟨_, hclock, hclockSigma, _, hgrid, _, hbeforeGrid, _⟩ := hclock
  have hg : r.gridBoundary = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
    rw [hgrid, hclock.1, hclockSigma]
    rfl
  have hbirthFull : birth ∈ E.records := by
    obtain ⟨suffix, heq⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
      initial rows J rewards start (k.val + 1) (count - (k.val + 1)) (by omega) active
    have heq' : E.records =
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start
          (k.val + 1) hstep active).records ++ suffix := by
      simpa only [Nat.add_sub_of_le hkCount] using heq
    rw [heq']
    exact List.mem_append_left _ hbirth
  obtain ⟨other, hother, hotherTime, hotherBorn, hselectedSigma, _⟩ :=
    ReferenceFirstDownRecoveryBudget.run_first_selected_payload
      initial rows J rewards start count hspan active hfirst k selected hselected
  have heq : other = birth := ReferenceAssignmentPayloadChronology.run_records_time_injective
    initial rows J rewards start count hspan active hother hbirthFull
    (hotherTime.trans hbirthTime.symm)
  subst other
  have hp : selected.view.payload = r.payload :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      birth _ _ hotherBorn hborn
  refine ⟨hselectedSigma, htime, ?_, ?_⟩
  · rw [hp, htime]
    rw [hg] at hbeforeGrid
    omega
  · intro t ht hbefore
    apply hbits t ht
    rw [htime] at hbefore
    omega

/-- The literal finite cutoff minimum at a live record. Future proposal bits
cannot shorten the endpoint before the current round's successor. -/
theorem min_firstCutoff_eq_current
    (row : CompletePublicTable.CompleteRow p) (sigma t : Fin p.T)
    (hgrid : t.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val sigma)
    (hbits : ∀ r : Fin p.T, sigma.val ≤ r.val → r.val < t.val →
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val row r = false) :
    min (FollowerCutoffScan.firstCutoff p rate.eta.val sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)) (t.val + 2) = t.val + 2 := by
  classical
  apply Nat.min_eq_right
  unfold FollowerCutoffScan.firstCutoff
  apply Finset.le_min'
  intro x hx
  simp only [FollowerCutoffScan.firstCutoffCarrier, Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact hgrid
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_filter, FollowerCutoffScan.proposalCoordinates,
      Finset.mem_univ, true_and] at hr
    by_cases hbefore : r.val < t.val
    · have hf := hbits r hr.1.1 hbefore
      rw [hf] at hr
      cases hr.2
    · change t.val + 2 ≤ r.val + 2
      omega

/-- On an actual connected history, a strict accepted-start change would be
an actual accepted reset. With no such reset an initially unoccupied follower
keeps its reply fields and remains unoccupied. All history inputs are explicit. -/
theorem unoccupied_reply_of_no_reset
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (chain : Connected initial records final) (i : Fin (p.m - 1))
    (seed last : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed seedMemory)
    (hunoccupied : seed.status = .unoccupied)
    (hlast : final.followers i = .ordinary last lastMemory)
    (hno : ∀ record ∈ records, ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i record) :
    last.status = .unoccupied ∧
      ReferenceFollowerReplyChronology.reply last = ReferenceFollowerReplyChronology.reply seed := by
  obtain ⟨first, memory, hfirst, _, hkeep, hstrict⟩ :=
    ReferenceFollowerReplyChronology.connected_ordinary_chronology chain i last lastMemory hlast
  rw [hseed] at hfirst
  obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hfirst
  apply hkeep hunoccupied
  by_contra hne
  obtain ⟨record, hrecord, sigma, happlied, _, _⟩ := hstrict hne
  obtain ⟨logged, cut, after, raw, message, scan, registers, lastService,
    _, hdown, houtcome, _⟩ := happlied
  exact hno record hrecord
    ⟨cut, hdown, logged, after, raw, message, scan, registers, lastService, houtcome⟩

/-- The physical successor list is the original run's initial calendar prefix. -/
theorem physicalRecords_eq_take
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : RewardTable p) (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (j : ℕ) (hj : j + 1 ≤ count) :
    ReferenceFollowerSparseEmissionRecovery.physicalRecords initial rows J rewards start j
        (by omega) active =
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records.take
        (j + 1) := by
  rw [ReferenceFollowerSparseEmissionRecovery.physicalRecords_eq_run_successor]
  obtain ⟨suffix, heq⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows J rewards start (j + 1) (count - (j + 1)) (by omega) active
  have hp : (ReferenceActivePhysicalHorizon.run initial rows J rewards start (j + 1)
      (by omega) active).records.IsPrefix
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records := by
    refine ⟨suffix, ?_⟩
    simpa only [Nat.add_sub_of_le hj] using heq.symm
  have ht := List.prefix_iff_eq_take.mp hp
  rw [ReferenceActivePhysicalHorizon.run_record_count] at ht
  exact ht

/-- Before or on the retained-DOWN index, the reply list uses every saved
emission, including the current log before the accepted reset clears it. -/
theorem firstReplyQueueRecords_eq_emissions
    (records : List (RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (j b : ℕ)
    (message : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hb : b ≤ j + 1) :
    ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords records i j message b =
      (records.take b).map (fun record =>
        (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution message i record)) := by
  apply List.ext_getElem
  · simp only [ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords,
      List.length_map, List.length_zipIdx]
  · intro n _ hright
    have hn : n < b := by
      simp only [List.length_map, List.length_take] at hright
      exact (Nat.lt_min.mp hright).1
    have hbefore : 0 + n ≤ j := by omega
    simp only [ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords,
      List.getElem_map, List.getElem_zipIdx, ite_eq_left hbefore]

/-- An actual ordinary output after a retained DOWN preserves the accepted
state through release and finish. The saved unoccupied choice disables release;
finish may update the actual proposal memory, but frames the local state. -/
theorem accepted_down_release_finish_frame
    (record : RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (record.output.preparation.followers.followers i).configuration = .ordinary choice memory)
    (logged after : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (message : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (hlogged : (record.output.followers i).downInput = some logged)
    (hdown : (record.output.followers i).down = some cut)
    (houtcome : cut.outcome = .accepted logged after raw message scan registers lastService)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hnext : (record.output.followers i).configuration = .ordinary next nextMemory) :
    DeclaredFollowerLocalRound.releaseAndFinish rate
        (record.output.preparation.followers.followers i).follower
        (record.output.preparation.followers.followers i).row
        (record.output.preparation.followers.followers i).time
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice memory after = .ok (next, nextMemory) ∧
      next = after := by
  have hfinish := ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i record
  rw [hfinish] at hnext
  obtain ⟨choice', memory', post, hc, hpost, hrelease, _, _⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ next nextMemory hnext
  obtain ⟨hchoices, hmemories⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hc.symm.trans hchoice)
  subst choice'
  subst memory'
  obtain ⟨choiceD, memoryD, loggedD, hcD, huD, hloggingD, hloggedD, hcallD⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i cut hdown
  have hchoiceD' : choiceD = choice :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hcD.symm.trans hchoice)).1
  have hloggedD' : loggedD = logged := Option.some.inj (hloggedD.symm.trans hlogged)
  subst choiceD
  subst loggedD
  simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left huD, hloggingD] at hpost
  rw [← hcallD, houtcome] at hpost
  have hpostEq : post = after := (Except.ok.inj hpost).symm
  subst post
  refine ⟨hrelease, ?_⟩
  have hfinishRound : ActiveFollowerLifecycle.finishRound rate.eta
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.followers.followers i).row after memory = .ok (next, nextMemory) := by
    unfold DeclaredFollowerLocalRound.releaseAndFinish at hrelease
    simp only [ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta
      (record.output.preparation.followers.followers i).follower
      (record.output.preparation.followers.followers i).time
      (ActiveFollowerLifecycle.publicRowOfCompleteRow
        (record.output.preparation.followers.followers i).row
        (record.output.preparation.followers.followers i).time)
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice after huD] at hrelease
    cases hf : ActiveFollowerLifecycle.finishRound rate.eta
        (record.output.preparation.followers.followers i).time
        (record.output.preparation.followers.followers i).row after memory with
    | error reason => simp only [hf] at hrelease; cases hrelease
    | ok pair =>
      simp only [hf] at hrelease
      exact congrArg Except.ok (Except.ok.inj hrelease)
  exact ActiveFollowerLifecycle.finishRound_frame _ _ _ _ _ _ _ hfinishRound

/-- The actual accepted transition supplies the literal pending state when
its derived endpoint is the current successor. No decoder output is supplied. -/
theorem accepted_down_pending_state
    (record : RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (logged after : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (message : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (hlogged : (record.output.followers i).downInput = some logged)
    (hdown : (record.output.followers i).down = some cut)
    (houtcome : cut.outcome = .accepted logged after raw message scan registers lastService)
    (hendpoint : scan.endpoint = record.input.time.val + 2) :
    after = ({ logged with
      lastDown := some message
      S := registers.1
      delta := lastService
      backlog := registers.2
      status := .pending
      downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep p i
        (record.output.preparation.followers.followers i).row
        (record.output.preparation.followers.followers i).time
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).1
      buffer := [] } : ReferencePrelaunchFollower.State p rate.eta) := by
  have htransition := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
    record i logged cut after raw message scan registers lastService hlogged hdown houtcome
  obtain ⟨_, _, _, _, _, _, hafter⟩ := ActiveFollowerDownAcceptance.downTransition_accepted_checked
    p _ _ _ _ rate logged after raw message scan registers lastService htransition
  have halign := record.output.preparation.follower_alignment i
  simpa only [halign.2.1, halign.2.2.1, hendpoint, ite_true] using hafter

/-- The actual unoccupied numerical cell remains enabled on non-DATA,
other-source and failed-thinning branches, and its assigned arrival is zero.
Logging is not filtered by these numerical thinning tests. -/
theorem unoccupied_arrival_zero_tests
    (record : RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (i : Fin (p.m - 1)) (hunoccupied : (cell.states i).status = .unoccupied) :
    let payload := cell.selected.view.payload
    let slice := (record.input.row.2 record.input.time).1
    let arrival := RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input (payload.assignment.assigned i)
    cell.input.enabled = true ∧
      (PublicDiscreteDraws.slotDraw slice ≠ PublicDiscreteDraws.dataSlot → arrival = 0) ∧
      (PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K slice ≠
        PublicDiscreteDraws.followerPlayer p.two_le_m i → arrival = 0) ∧
      ((4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * payload.rate (payload.assignment.assigned i)) /
          CanonicalRecordingSlice.recordingZeta p.m p.K <
        (slice ContinuousControlSlice.Label.thin).val → arrival = 0) := by
  classical
  dsimp only
  have hzero :
      ¬ (PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
          (record.input.row.2 record.input.time).1 = PublicDiscreteDraws.followerPlayer p.two_le_m i ∧
        ReferenceFirstLaunchNumericalCell.firstFollowerEvent i record.input.row record.input.time
          (cell.selected.view.payload.assignment.assigned i)
          (cell.selected.view.payload.rate (cell.selected.view.payload.assignment.assigned i))) →
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        cell.input (cell.selected.view.payload.assignment.assigned i) = 0 := by
    intro hfail
    rw [cell.quantizedArrival_eq]
    apply ite_eq_right
    intro hmarker
    exact hfail ((ReferenceFirstLiveUnoccupiedEmission.sourceArm_eq_some_iff_unoccupied
      record cell i hunoccupied).mp hmarker)
  refine ⟨cell.enabled, ?_, ?_, ?_⟩
  · intro hnondata
    apply hzero
    rintro ⟨_, hdata, _⟩
    exact hnondata hdata
  · intro hother
    apply hzero
    rintro ⟨hsource, _⟩
    exact hother hsource
  · intro hthin
    apply hzero
    rintro ⟨_, _, _, _, hpass⟩
    exact (not_le_of_gt hthin) hpass

section ActualWindow

variable (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ)
  (hc : (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
  (count : ℕ)
  (hspan : ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
        count ≤ p.T)

/-- Actual first-live ordinary output and absence of a local failure, with
all incoming local domains produced from the original initialization seed. -/
theorem actual_live_next_ordinary
    (i : Fin (p.m - 1))
    (j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length) :
    let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan
    ∃ next nextMemory,
      (W[j.val].output.followers i).configuration = .ordinary next nextMemory ∧
      (W[j.val].output.followers i).failure = none := by
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc
  have hsafe := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    seed.followers seed.memory seed.configuration seed.S_zero seed.delta_zero seed.backlog_zero
    seed.lastDown_none seed.unoccupied seed.bufferValid seed.chronologicalBuffer seed.bufferStamps
    seed.decoderValid
  obtain ⟨_, _, next, nextMemory, _, hnext, hfailure, _⟩ := hsafe.2 j i
  exact ⟨next, nextMemory, hnext, hfailure⟩

/-- Conditional pre-DOWN history alignment. The no-reset input is supplied
by the actual zero-seeded recovery theorem in the final composition. -/
theorem actual_pre_down_alignment
    (i : Fin (p.m - 1))
    (j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length)
    (hno : ∀ prior ∈ (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan).records.take j.val,
      ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i prior) :
    let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan
    ∀ k : Fin W.length, k.val ≤ j.val →
      (cell k).selected.view.payload = (cell j).selected.view.payload ∧
      ((cell k).states i).status = .unoccupied ∧
      ∃ before memory, W[k.val].input.state.followers i = .ordinary before memory ∧
        before.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply ((cell k).states i) =
          ReferenceFollowerReplyChronology.reply before := by
  dsimp only
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc
  let rows := source.1.2
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan seed.activeAtStart
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan
  have hprefix : W.IsPrefix E.records := List.takeWhile_prefix _
  obtain ⟨_, _, _, _, hsigma, _⟩ := ReferenceFirstDownRecoveryBudget.run_first_selected_payload
    initial rows J rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    j (cell j).selected (cell j).selection_actual
  intro k hkj
  have hkfull : k.val < E.records.length := k.isLt.trans_le hprefix.length_le
  have hkrecord : E.records[k.val] = W[k.val] := (hprefix.getElem k.isLt).symm
  obtain ⟨before, memory, hbefore, hreply, hchoice⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice
      W[k.val] i ((cell k).states i) ((cell k).memories i) ((cell k).ordinary i)
  have hchain := ReferenceFollowerReplyChronology.connected_take_to_input E.connected k.val hkfull
  rw [hkrecord] at hchain
  have hbeforeUnoccupied := unoccupied_reply_of_no_reset hchain i
    (seed.followers i) before (seed.memory i) memory (seed.configuration i)
    (seed.unoccupied i) hbefore (fun record hrecord =>
      hno record (List.take_subset_take_left E.records hkj hrecord))
  obtain ⟨_, _, _, _, hksigma, _⟩ := ReferenceFirstDownRecoveryBudget.run_first_selected_payload
    initial rows J rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    k (cell k).selected (cell k).selection_actual
  have hp := ReferenceSelectedPayloadChronology.run_two_actualSelectedPayloads_eq_of_equal_sigma
    initial rows J rewards start count hspan seed.activeAtStart seed.coordinatorFirst
    W[k.val] W[j.val] (cell k).selected (cell j).selected
    (hprefix.sublist.subset (List.getElem_mem k.isLt))
    (hprefix.sublist.subset (List.getElem_mem j.isLt))
    (cell k).selection_actual (cell j).selection_actual (hksigma.trans hsigma.symm)
  exact ⟨hp, hchoice hbeforeUnoccupied.1, before, memory, hbefore, hbeforeUnoccupied.1, hreply⟩

/-- Conditional whole-list join. Its no-reset input is explicit; the actual
accepted branch in the final theorem produces that input. -/
theorem actual_reply_records_eq_source_prefix
    (i : Fin (p.m - 1))
    (j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length)
    (message : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hmessage : message = (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan j).selected.view.payload.downRecord i)
    (hno : ∀ prior ∈ (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan).records.take j.val,
      ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i prior) :
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate source rewards C_star C_h hc count hspan
    let payload := (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan j).selected.view.payload
    ∀ b, b ≤ j.val + 1 →
      ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j.val message b =
        (cells.take b).map (fun c => (c.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c (payload.assignment.assigned i))) := by
  dsimp only
  let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
    rate source rewards C_star C_h hc count hspan
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hc count hspan
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan
  let payload := (cell j).selected.view.payload
  have hprefix : W.IsPrefix E.records := List.takeWhile_prefix _
  have hcellLength : cells.length = W.length :=
    ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate source rewards C_star C_h hc count hspan
  have halignment := actual_pre_down_alignment rate source rewards C_star C_h hc count hspan i j hno
  intro b hb
  have hbW : b ≤ W.length := hb.trans (Nat.succ_le_of_lt j.isLt)
  change ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j.val message b =
    (cells.take b).map (fun c => (c.enabled, RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c (payload.assignment.assigned i)))
  apply List.ext_getElem
  · simp only [ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords,
      List.length_map, List.length_zipIdx, List.length_take, hcellLength,
      Nat.min_eq_left (hbW.trans hprefix.length_le), Nat.min_eq_left hbW]
  · intro n hleft hright
    have hnb : n < b := by
      simp only [List.length_map, List.length_take] at hright
      exact (Nat.lt_min.mp hright).1
    let k : Fin W.length := ⟨n, hnb.trans_le hbW⟩
    have hkj : k.val ≤ j.val := by dsimp only [k]; omega
    obtain ⟨hp, hu, _⟩ := halignment k hkj
    have he := ReferenceFirstLiveUnoccupiedEmission.actual_firstReplyQueueRecords_before_down
      rate source rewards C_star C_h hc count hspan k i hu j.val b hkj hnb
    have hM : message = (cell k).selected.view.payload.downRecord i :=
      hmessage.trans (congrArg (fun P : ReferenceActivePhysicalStep.Payload rate => P.downRecord i) hp).symm
    have hrecords := congrArg (fun M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) =>
        ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j.val M b) hM
    have harm := congrArg (fun P : ReferenceActivePhysicalStep.Payload rate => P.assignment.assigned i) hp
    have harrival := congrArg (fun a : Fin p.K =>
      (true, RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (cell k).input a)) harm
    refine (List.getElem_of_eq hrecords hleft).trans (he.trans (harrival.trans ?_))
    simp only [List.getElem_map, List.getElem_take]
    rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
      rate source rewards C_star C_h hc count hspan k, (cell k).enabled]

/-- The actual retained diagnostic identifies the current whole DOWN. Its
assignment start is produced by the original first-assignment birth theorem. -/
theorem actual_retained_down_identity
    (i : Fin (p.m - 1))
    (j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length)
    (message : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc count hspan)[j.val] i message) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let payload := (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan j).selected.view.payload
    message = payload.downRecord i ∧ payload.sigma.val = start ∧ message.val.sigma = start + 1 := by
  dsimp only
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan j
  obtain ⟨_, _, _, _, hsigma, _⟩ := ReferenceFirstDownRecoveryBudget.run_first_selected_payload
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan
    seed.activeAtStart seed.coordinatorFirst j cell.selected cell.selection_actual
  obtain ⟨logged, cut, after, raw, scan, registers, lastService, _, hdown, houtcome⟩ := hretained
  obtain ⟨_, _, _, _, _, _, _, hcall⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice W[j.val] i cut hdown
  have hcaccepted := hcall ▸ houtcome
  obtain ⟨view, hview⟩ := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_someView
    _ _ _ _ _ _ _ _ _ _ _ _ _ hcaccepted
  rw [hview] at hcaccepted
  have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields
    view _ _ _ _ _ _ _ _ _ _ _ _ hcaccepted
  obtain ⟨selected, hselected, hselectedView⟩ := Option.map_eq_some_iff.mp hview
  have hsameSelected : selected = cell.selected :=
    Option.some.inj (hselected.symm.trans cell.selection_actual)
  have hmessage : message = cell.selected.view.payload.downRecord i := by
    rw [← hselectedView, hsameSelected,
      (W[j.val].output.preparation.follower_alignment i).2.1] at hfields
    exact hfields.1
  refine ⟨hmessage, hsigma, ?_⟩
  exact (congrArg (fun M : OrdinaryMessageCodec.DownRecord
    (ReferencePrelaunchFollower.codecParams p rate.eta) => M.val.sigma) hmessage).trans
      (congrArg (fun n => n + 1) hsigma)

/-- The first retained DOWN inside the actual first-live window initializes
the follower from the SAME original-source numerical cells. No seed, zero
queue, matching-payload, no-reset, scan geometry or success law is an input.
The diagnostic premise is only the actual internal accepted branch query. -/
theorem actual_first_live_down_numerical_recovery
    (i : Fin (p.m - 1))
    (j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length)
    (message : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc count hspan)[j.val] i message) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan
    let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate source rewards C_star C_h hc count hspan
    let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan
    let payload := (cell j).selected.view.payload
    let Da := fun b => (cells.take b).map (fun c =>
      (c.enabled, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c (payload.assignment.assigned i)))
    let Va := fun b => QueueReplay.replay (4 * rate.n) (0, 0) (Da b)
    message = payload.downRecord i ∧ payload.sigma.val = start ∧
    message.val.sigma = start + 1 ∧ message.val.q = 0 ∧
    (∀ k : Fin W.length, k.val ≤ j.val →
      (cell k).selected.view.payload = payload ∧ ((cell k).states i).status = .unoccupied ∧
      ∃ before memory, W[k.val].input.state.followers i = .ordinary before memory ∧
        before.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply ((cell k).states i) =
          ReferenceFollowerReplyChronology.reply before) ∧
    (∀ prior ∈ E.records.take j.val,
      ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i prior) ∧
    (∀ b, b ≤ j.val + 1 →
      ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
        E.records i j.val message b = Da b) ∧
    Va 0 = (0, 0) ∧
    ∃ logged cut after raw scan registers lastService next nextMemory,
      (W[j.val].output.followers i).downInput = some logged ∧
      (W[j.val].output.followers i).down = some cut ∧
      cut.outcome = .accepted logged after raw message scan registers lastService ∧
      scan.endpoint = start + j.val + 2 ∧
      scan.endpoint - message.val.sigma = j.val + 1 ∧
      ActiveFollowerDownAcceptance.recoveryQueueRecords p rate message logged scan.endpoint =
        Da (j.val + 1) ∧
      ActiveFollowerDownAcceptance.checkedRecovery p rate message logged scan.endpoint =
        .ok ⟨registers, lastService⟩ ∧
      registers = Va (j.val + 1) ∧ lastService = (Va (j.val + 1)).1 - (Va j.val).1 ∧
      (∀ b, ∃ middle,
        ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
          ⟨(0, 0), 0⟩ ((Da (j.val + 1)).take b) = .ok middle ∧
        ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
        middle.registers = QueueReplay.replay (4 * rate.n) (0, 0) ((Da (j.val + 1)).take b)) ∧
      after = ({ logged with
        lastDown := some message
        S := registers.1
        delta := lastService
        backlog := registers.2
        status := .pending
        downBatch := (ActiveFollowerDownAcceptance.currentDecodeStep p i
          (W[j.val].output.preparation.followers.followers i).row
          (W[j.val].output.preparation.followers.followers i).time
          (W[j.val].output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).1
        buffer := [] } : ReferencePrelaunchFollower.State p rate.eta) ∧
      (W[j.val].output.followers i).configuration = .ordinary next nextMemory ∧
      (W[j.val].output.followers i).failure = none ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate
        (W[j.val].output.preparation.followers.followers i).follower
        (W[j.val].output.preparation.followers.followers i).row
        (W[j.val].output.preparation.followers.followers i).time
        (W[j.val].output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        ((cell j).states i) ((cell j).memories i) after = .ok (next, nextMemory) ∧
      next.lastDown = some message ∧ next.S = registers.1 ∧ next.delta = lastService ∧
      next.backlog = registers.2 ∧ next.status = .pending ∧ next.buffer = [] ∧
      next.downBatch = after.downBatch ∧ next.initializationFailure = logged.initializationFailure := by
  classical
  dsimp only
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let rows := source.1.2
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan seed.activeAtStart
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hc count hspan
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hc count hspan
  let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan
  let payload := (cell j).selected.view.payload
  let Da := fun b => (cells.take b).map (fun c =>
    (c.enabled, RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c (payload.assignment.assigned i)))
  let Va := fun b => QueueReplay.replay (4 * rate.n) (0, 0) (Da b)
  have hprefix : W.IsPrefix E.records := List.takeWhile_prefix _
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start count hspan seed.activeAtStart
  have hjfull : j.val < E.records.length := j.isLt.trans_le hprefix.length_le
  let jf : Fin E.records.length := ⟨j.val, hjfull⟩
  have hjrecord : E.records[jf.val] = W[j.val] := (hprefix.getElem j.isLt).symm
  have hgeometry := first_live_geometry initial rows J rewards start count hspan
    seed.activeAtStart seed.coordinatorFirst j (cell j).selected (cell j).selection_actual
  obtain ⟨hsigma, htime, hgrid, hbits⟩ := hgeometry
  change payload.sigma.val = start at hsigma
  change W[j.val].input.time.val = start + j.val at htime
  change W[j.val].input.time.val + 2 ≤
    FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma at hgrid
  change ∀ t : Fin p.T, start ≤ t.val → t.val < W[j.val].input.time.val →
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J) t = false at hbits
  obtain ⟨hmessage, _, hMsigma⟩ := actual_retained_down_identity
    rate source rewards C_star C_h hc count hspan i j message hretained
  change message = payload.downRecord i at hmessage
  change message.val.sigma = start + 1 at hMsigma
  have hretainedFull : ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[jf.val] i message := by
    rw [hjrecord]
    exact hretained
  obtain ⟨logged, cut, after, raw, scan, registers, lastService,
      hlogged, hdown, houtcome, viewZ, selectedZ, _, _, _, _,
      birth, installed, firstChoice, _, _, _, _, _, _, _, _, _, hq, _, _,
      n0, hn0, hscan, hnpos, hnbound, hno, hphysical, hchecked, hregisters,
      hlast, hdomains, hafter⟩ :=
    ReferenceFirstDownZeroRecovery.actual_first_down_zero_seeded_recovery
      initial rows J rewards start count hspan seed.activeAtStart seed.coordinatorFirst i
      (seed.followers i) (seed.memory i) (seed.configuration i) (seed.lastDown_none i)
      (seed.unoccupied i) (seed.bufferValid i) (seed.chronologicalBuffer i)
      (seed.bufferStamps i) jf message hretainedFull hMsigma
  rw [hjrecord] at hlogged hdown hafter
  dsimp only [jf] at hn0 hscan hno hphysical hregisters hlast hdomains
  have hdownStart : ActiveFollowerDownAcceptance.downStart p rate message = payload.sigma := by
    apply Fin.ext
    have hadd := ActiveFollowerDownAcceptance.downStart_val_add_one p rate message
    exact Nat.add_right_cancel
      (hadd.trans (hMsigma.trans (congrArg (fun n => n + 1) hsigma.symm)))
  have hmin := min_firstCutoff_eq_current (rate := rate) (rows J) payload.sigma
    W[j.val].input.time hgrid (by simpa only [hsigma] using hbits)
  have hendpoint : scan.endpoint = start + j.val + 2 := by
    have hscan' : scan.endpoint = min
        (FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)))
        (start + j.val + 2) := by simpa only [hdownStart] using hscan
    exact hscan'.trans (by simpa only [htime] using hmin)
  have hn : n0 = j.val + 1 := by
    rw [hendpoint, hMsigma] at hn0
    have heq : start + j.val + 2 = (start + 1) + (j.val + 1) := by
      simp only [Nat.add_assoc, Nat.add_left_comm 1 j.val 1]
    rw [heq, Nat.add_sub_cancel_left] at hn0
    exact hn0
  have halignment := actual_pre_down_alignment
    rate source rewards C_star C_h hc count hspan i j hno
  have hlist := actual_reply_records_eq_source_prefix
    rate source rewards C_star C_h hc count hspan i j message hmessage hno
  change ∀ b, b ≤ j.val + 1 →
    ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j.val message b = Da b at hlist
  have hjCount : j.val + 1 ≤ count := (Nat.succ_le_of_lt hjfull).trans_eq hcount
  have hstep : start + (j.val + 1) ≤ p.T :=
    (Nat.add_le_add_left hjCount start).trans hspan
  have hphysicalTake := physicalRecords_eq_take initial rows J rewards start count hspan
    seed.activeAtStart j.val hjCount
  have hinput :
      ((ReferenceFollowerSparseEmissionRecovery.physicalRecords initial rows J rewards start j.val
        hstep seed.activeAtStart).take n0).map
        (fun record => (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution message i record)) =
      Da (j.val + 1) := by
    rw [hphysicalTake, hn, List.take_take, Nat.min_self,
      ← firstReplyQueueRecords_eq_emissions E.records i j.val (j.val + 1) message le_rfl]
    exact hlist _ le_rfl
  have hrecovery : ActiveFollowerDownAcceptance.recoveryQueueRecords p rate message logged
      scan.endpoint = Da (j.val + 1) := hphysical.trans hinput
  have hregs : registers = Va (j.val + 1) := by
    rw [hn, hlist _ le_rfl] at hregisters
    exact hregisters
  have hlast' : lastService = (Va (j.val + 1)).1 - (Va j.val).1 := by
    rw [hn, Nat.add_sub_cancel, hlist _ le_rfl, hlist _ (Nat.le_succ j.val)] at hlast
    exact hlast
  have hdomains' : ∀ b, ∃ middle,
      ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
        ⟨(0, 0), 0⟩ ((Da (j.val + 1)).take b) = .ok middle ∧
      ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
      middle.registers = QueueReplay.replay (4 * rate.n) (0, 0) ((Da (j.val + 1)).take b) := by
    simpa only [hinput, hq] using hdomains
  have hendpointCurrent : scan.endpoint = W[j.val].input.time.val + 2 := by
    simpa only [htime] using hendpoint
  have hafter' := accepted_down_pending_state
    W[j.val] i logged after cut raw message scan registers lastService hlogged hdown houtcome
    hendpointCurrent
  obtain ⟨next, nextMemory, hnext, hfailure⟩ := actual_live_next_ordinary
    rate source rewards C_star C_h hc count hspan i j
  obtain ⟨hrelease', hnextEq⟩ := accepted_down_release_finish_frame
    W[j.val] i ((cell j).states i) ((cell j).memories i) ((cell j).ordinary i)
    logged after cut raw message scan registers lastService hlogged hdown houtcome next nextMemory hnext
  refine ⟨hmessage, hsigma, hMsigma, hq, halignment, hno, hlist, rfl,
    logged, cut, after, raw, scan, registers, lastService, next, nextMemory,
    hlogged, hdown, houtcome, hendpoint, ?_, hrecovery, hchecked, hregs, hlast', hdomains',
    hafter', hnext, hfailure, hrelease', ?_⟩
  · exact hn0.symm.trans hn
  · rw [hnextEq, hafter']
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every checked prefix, written directly on the literal numerical readout
`Da b`. This includes the empty and current logging-before-clear prefixes. -/
theorem actual_first_live_down_checked_prefixes
    (i : Fin (p.m - 1))
    (j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length)
    (message : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc count hspan)[j.val] i message) :
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate source rewards C_star C_h hc count hspan
    let payload := (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate source rewards C_star C_h hc count hspan j).selected.view.payload
    let Da := fun b => (cells.take b).map (fun c =>
      (c.enabled, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c (payload.assignment.assigned i)))
    ∀ b, b ≤ j.val + 1 → ∃ middle,
      ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
        ⟨(0, 0), 0⟩ (Da b) = .ok middle ∧
      ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
      middle.registers = QueueReplay.replay (4 * rate.n) (0, 0) (Da b) := by
  dsimp only
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hc count hspan
  let payload := (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
    rate source rewards C_star C_h hc count hspan j).selected.view.payload
  let Da := fun b => (cells.take b).map (fun c =>
    (c.enabled, RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c (payload.assignment.assigned i)))
  obtain ⟨_, _, _, _, _, _, _, _, logged, cut, after, raw, scan, registers, lastService,
      next, nextMemory, _, _, _, _, _, _, _, _, _, hdomains, _⟩ :=
    actual_first_live_down_numerical_recovery
      rate source rewards C_star C_h hc count hspan i j message hretained
  change ∀ b, ∃ middle,
    ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
      ⟨(0, 0), 0⟩ ((Da (j.val + 1)).take b) = .ok middle ∧
    ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
    middle.registers = QueueReplay.replay (4 * rate.n) (0, 0) ((Da (j.val + 1)).take b) at hdomains
  intro b hb
  have htake : (Da (j.val + 1)).take b = Da b := by
    dsimp only [Da]
    rw [← List.map_take, List.take_take, Nat.min_eq_left hb]
  simpa only [htake] using hdomains b

end ActualWindow

end Bandits.Support.ReferenceFirstLiveDownNumericalRecovery

end
