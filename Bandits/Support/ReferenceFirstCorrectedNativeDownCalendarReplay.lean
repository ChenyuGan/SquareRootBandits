/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedAssignedOverflowCover

import Mathlib.Tactic

/-!
# Original-source first corrected native DOWN calendar replay

The actual first corrected installation keeps the queue from the original
source prefix. Its literal current-DOWN diagnostics retain every rejected
alternative and exclude checked failure. On acceptance, the logged buffer,
native recovery word and every checked replay prefix agree with the same
attributed calendar prefix, including late acceptance in the first collection.
The optional exit is covered whenever its actual selection still uses this
payload, even if the coordinator tail fails. No future UP is an input.

Sources: ZIP4 `04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:40-100,192-233,246-299,355-426`, and
`appendix_a_local_protocol.tex:28-64` under `sources/zip4/manuscript/`.
-/

@[expose] public section
noncomputable section

open Bandits.Support
open BootstrapPrivateRoundStreams (SourceInput)
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
open RecordedQueueRun

namespace Bandits.Support.ReferenceFirstCorrectedNativeDownCalendarReplay

variable {p : ConstructorDimensions.Parameters}

local instance (Q : Prop) : Decidable Q := Classical.propDecidable Q

/-- The first corrected cell supplies the actual installed DOWN queue from
the same original source prefix. In particular, this exposes the nonzero
initial replay register that a later accepted DOWN must retain. -/
theorem firstCell_actual_installed_down_seed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    let b := birthIndex rate rewards C_star C_h z
    ∃ (L : List (RoundInput p.K)) (c : RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : ReferenceActivePhysicalStep.Payload rate),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t z = some c ∧
      prefixInputs rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ R[b]? = some birth ∧
      InstallationBirth birth P ∧ P.sigma = t ∧
      (∀ a : Fin p.K,
        P.queues a = (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          L L.length a).2) ∧
      (∀ i : Fin (p.m - 1),
        (P.downRecord i).val.q =
          (UnstoppedRecordedQueueComparison.unstoppedReplay
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            L L.length (P.assignment.assigned i)).2) := by
  classical
  obtain ⟨L, c, birth, P, _base, hL, hc, hinputs, hlen, hbirth,
      _hactual, _hbirthTime, _hrows, _hselected, _hrewards, _hrecordRows,
      _hchosen, _henabled, hborn, hSigma, _hcRate, _hcReward, hqueues,
      hbase, _hterminal, _hbirthWord, _hafter⟩ :=
    ReferenceFirstCorrectedAssignedArrivalPrefix.firstCell_total_assigned_arrival_prefix
      rate rewards C_star C_h u t z hz
  dsimp only
  refine ⟨L, c, birth, P, hL, hc, hinputs, hlen, hbirth, hborn, hSigma,
    hqueues, ?_⟩
  intro i
  exact (hbase i).2

private theorem actual_record_eq_step
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferenceAssignmentPayloadChronology.actualStepRecord r.input = r := by
  cases r with
  | mk input output heq =>
      cases heq
      rfl

/-- A current selection of the original payload forces every preceding
selection back to its actual birth to carry that same payload. The argument
uses actual successor storage, and does not require the current coordinator
tail to succeed. -/
theorem complete_birth_current_selected_interval
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : SourceInput p)
    (b j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : Payload rate)
    (hbirth : InstallationBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val] P)
    (_hbefore : b.val ≤ j.val)
    (current : Selection (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val].input)
    (hcurrent : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val].output.preparation.coordinator.selection = some current)
    (hpayload : current.view.payload = P) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ n : Fin R.length, b.val ≤ n.val → n.val < j.val →
      ∃ selected : Selection R[n.val].input,
        R[n.val].output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = P := by
  classical
  intro R n hbn hnj
  have hj : j.val < R.length := j.isLt
  have htime (k : Fin R.length) : R[k.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val :=
    ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z k
  have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    R[b.val] P hbirth
  rw [htime b] at hbirthTime
  have hstored : storedPayload R[j.val].input.state.coordinator = some P := by
    rcases ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
        R[j.val] current hcurrent with hstored | hborn
    · simpa only [hpayload] using hstored
    · have ht := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
        R[j.val] current.view.payload hborn
      rw [htime j, hpayload] at ht
      omega
  have hback : ∀ d, d ≤ j.val → b.val < j.val - d →
      storedPayload (R[j.val - d]'(by omega)).input.state.coordinator = some P := by
    intro d
    induction d with
    | zero => intro _ _; simpa only [Nat.sub_zero] using hstored
    | succ d ih =>
        intro hd hb
        have hprev := ih (by omega) (by omega)
        let k : Fin R.length := ⟨j.val - (d + 1), by omega⟩
        have hnext : storedPayload R[k.val].output.next.coordinator = some P := by
          rw [← ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
            rewards C_star C_h z k.val (by dsimp [k]; omega)]
          have hi : k.val + 1 = j.val - d := by dsimp [k]; omega
          simpa only [hi] using hprev
        have hclass := ReferenceAssignmentPayloadChronology.actualStep_payload_classification
          R[k.val].input
        rw [R[k.val].output_eq] at hnext
        rcases hclass with hnone | ⟨old, hold, hout⟩ | ⟨fresh, hfresh, hout⟩
        · rw [hnext] at hnone
          cases hnone
        · have heq : old = P := Option.some.inj (hout.symm.trans hnext)
          simpa only [heq] using hold
        · have heq : fresh = P := Option.some.inj (hout.symm.trans hnext)
          rw [actual_record_eq_step, heq] at hfresh
          have ht := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[k.val] P hfresh
          rw [htime k] at ht
          dsimp only [k] at ht
          omega
  let successor : Fin R.length := ⟨n.val + 1, by omega⟩
  have hs := hback (j.val - successor.val) (by dsimp [successor]; omega)
    (by dsimp [successor]; omega)
  have hi : j.val - (j.val - successor.val) = successor.val := by dsimp [successor]; omega
  have hs' : storedPayload R[successor.val].input.state.coordinator = some P := by
    simpa only [hi] using hs
  have hnext : storedPayload R[n.val].output.next.coordinator = some P := by
    rw [← ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
      rewards C_star C_h z n.val (by omega)]
    exact hs'
  have hp := ReferenceGeneratedUpSitePayloadOrder.actual_step_stored_payload_eq_selected
    R[n.val].input P (by rw [← R[n.val].output_eq]; exact hnext)
  rw [actual_record_eq_step] at hp
  unfold selectedPayload at hp
  obtain ⟨selected, hselected, heq⟩ := Option.map_eq_some_iff.mp hp
  exact ⟨selected, hselected, heq⟩

/-- The selected-view interval on the original slice is constructed from
birth and the literal current selection, before inspecting any accepted UP. -/
theorem complete_birth_current_down_view_interval
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : SourceInput p)
    (b j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : Payload rate)
    (hbirth : InstallationBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val] P)
    (hbefore : b.val ≤ j.val)
    (current : Selection (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val].input)
    (hcurrent : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val].output.preparation.coordinator.selection = some current)
    (hpayload : current.view.payload = P) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ReferenceFollowerSparseEmissionRecovery.selectedViewInterval P.sigma.val
      ((R.drop b.val).take (j.val - b.val)) := by
  intro R record hrecord view hview
  obtain ⟨a, ha, hr⟩ := List.mem_iff_getElem.mp hrecord
  have ha' : a < j.val - b.val ∧ a < R.length - b.val := by
    simpa only [List.length_take, List.length_drop, lt_min_iff] using ha
  have hindex : b.val + a < R.length := by omega
  have hr' : R[b.val + a] = record := by
    simpa only [List.getElem_take, List.getElem_drop] using hr
  obtain ⟨selected, hselected, hp⟩ := complete_birth_current_selected_interval
    rewards C_star C_h z b j P hbirth hbefore current hcurrent hpayload
    ⟨b.val + a, hindex⟩ (by change b.val ≤ b.val + a; omega)
      (by change b.val + a < j.val; omega)
  change R[b.val + a].output.preparation.coordinator.selection = some selected at hselected
  have hv : view = selected.view := by
    rw [← hr'] at hview
    simpa only [DispatchCut.downView, hselected, Option.map_some, Option.some.injEq]
      using hview.symm
  rw [hv, hp]

/-- An actual accepted current DOWN, without any future UP assumption,
contains precisely the original physical log since this installation. The
checked recovery word uses all calendar dates, and every checked prefix is
retained with its original queue seed. -/
theorem complete_birth_current_down_physical_recovery
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : SourceInput p)
    (b j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (P : Payload rate)
    (hbirth : InstallationBirth (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val] P)
    (hbefore : b.val ≤ j.val)
    (current : Selection (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val].input)
    (hcurrent : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val].output.preparation.coordinator.selection = some current)
    (hpayload : current.view.payload = P)
    (i : Fin (p.m - 1))
    (logged after : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (hlogged : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val].output.followers i).downInput = some logged)
    (hdown : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val].output.followers i).down = some cut)
    (haccepted : cut.outcome = .accepted logged after raw M scan registers lastService) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let v := scan.endpoint - (P.sigma.val + 1)
    let word := ((R.drop b.val).take v).map
      (fun r => (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution (P.downRecord i) i r))
    M = P.downRecord i ∧
    scan.endpoint = min
      (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))))
      (R[j.val].input.time.val + 2) ∧
    1 ≤ v ∧ v ≤ j.val - b.val + 1 ∧
    (∃ (seed : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      R[b.val].input.state.followers i = .ordinary seed memory ∧
      seed.status = .unoccupied ∧
      logged.buffer = seed.buffer ++
        ((R.drop b.val).take (j.val - b.val + 1)).flatMap
          (ReferenceFollowerBufferProvenance.logEmission i)) ∧
    (∀ r ∈ (R.drop b.val).take (j.val - b.val),
      ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i r) ∧
    ActiveFollowerDownAcceptance.recoveryQueueRecords p rate (P.downRecord i) logged scan.endpoint = word ∧
    ActiveFollowerDownAcceptance.checkedRecovery p rate (P.downRecord i) logged scan.endpoint =
      .ok ⟨registers, lastService⟩ ∧
    registers = QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word ∧
    (∀ k, ∃ middle,
      ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
        ⟨(0, (P.downRecord i).val.q), 0⟩ (word.take k) = .ok middle ∧
      ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
      middle.registers = QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word.take k)) ∧
    (∃ hinterval : (P.downRecord i).val.sigma < scan.endpoint,
      lastService =
        (ActiveFollowerDownAcceptance.recoveredLastTransition p rate (P.downRecord i) logged
          scan.endpoint hinterval).1 -
        (ActiveFollowerDownAcceptance.recoveredRegistersBeforeLast p rate (P.downRecord i) logged
          scan.endpoint hinterval).1) ∧
    after.lastDown = some (P.downRecord i) ∧ after.S = registers.1 ∧
    after.delta = lastService ∧ after.backlog = registers.2 ∧
    ∃ nextMemory : ActiveFollowerLifecycle.LocalMemory p,
      R[j.val].output.next.followers i = .ordinary after nextMemory := by
  classical
  intro R v word
  change R[j.val].output.preparation.coordinator.selection = some current at hcurrent
  have hj : j.val < R.length := j.isLt
  obtain ⟨choice, choiceMemory, actualLogged, _hchoice, _hunoccupied,
      _hlogging, hdiagInput, hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice R[j.val] i cut hdown
  have heq : actualLogged = logged := Option.some.inj (hdiagInput.symm.trans hlogged)
  subst actualLogged
  have haccepted' := haccepted
  rw [hcut] at haccepted'
  have hview : R[j.val].output.preparation.coordinator.downView = some current.view := by
    simp only [DispatchCut.downView, hcurrent, Option.map_some]
  rw [hview] at haccepted'
  have halign := R[j.val].output.preparation.follower_alignment i
  have hM := (ReferenceActiveDataOwnership.referenceDown_accepted_fields current.view
    _ _ _ _ logged logged after raw M scan registers lastService haccepted').1
  rw [halign.2.1, hpayload] at hM
  subst M
  obtain ⟨seed, seedChoice, memory, hseed, _hdomain, hseedStatus, _hstart,
    _hseedChoice, _hseedChoiceStatus, hvalid, hpair, htimes⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_installation_carried_buffer_seed
      rewards C_star C_h z b P hbirth i
  let s := R[b.val].input.time.val
  let l := j.val - b.val
  have hbTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq R[b.val] P hbirth
  have hsigma : (P.downRecord i).val.sigma = s + 1 := by
    exact (congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)).trans
      (congrArg (fun n => n + 1) hbTime)
  have hMsigma : (P.downRecord i).val.sigma = P.sigma.val + 1 :=
    congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
  obtain ⟨span, mode, hfull⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_input_suffix_reindex
      rewards C_star C_h z b (l + 1) (by dsimp [l]; omega)
  obtain ⟨prefixSpan, prefixMode, hprior⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_input_suffix_reindex
      rewards C_star C_h z b l (by dsimp [l]; omega)
  let actual := ReferenceFollowerSparseEmissionRecovery.successorRecord R[b.val].input.state
    z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s l span mode
  have hphysical : ReferenceFollowerSparseEmissionRecovery.physicalRecords R[b.val].input.state
      z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s l span mode =
      (R.drop b.val).take (l + 1) := by
    rw [ReferenceFollowerSparseEmissionRecovery.physicalRecords_eq_run_successor]
    exact hfull
  have hactual : actual = R[j.val] := by
    have hg := congrArg (fun records : List (ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate)) => records[l]?) hphysical
    rw [ReferenceFollowerSparseEmissionRecovery.physicalRecords,
      List.getElem?_append_right (by
        rw [ReferenceFollowerSparseEmissionRecovery.priorRun, run_record_count])] at hg
    have hi : b.val + l = j.val := by dsimp [l]; omega
    simp only [ReferenceFollowerSparseEmissionRecovery.priorRun, run_record_count,
      Nat.sub_self, List.getElem?_cons_zero, List.getElem?_take, Nat.lt_succ_self, ite_true,
      List.getElem?_drop, hi] at hg
    rw [List.getElem?_eq_getElem hj] at hg
    exact Option.some.inj hg
  have hwindow : ReferenceFollowerSparseEmissionRecovery.selectedViewInterval s
      (ReferenceFollowerSparseEmissionRecovery.priorRun R[b.val].input.state z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s l span mode).records := by
    change ReferenceFollowerSparseEmissionRecovery.selectedViewInterval s
      (run R[b.val].input.state z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
        rewards s l _ mode).records
    rw [hprior]
    simpa only [s, l, hbTime] using complete_birth_current_down_view_interval
      rewards C_star C_h z b j P hbirth hbefore current hcurrent hpayload
  have htimes' : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ s := by
    simpa only [hbTime, s] using htimes
  have hlogActual : (actual.output.followers i).downInput = some logged := by
    rw [hactual]; exact hlogged
  have hdownActual : (actual.output.followers i).down = some cut := by
    rw [hactual]; exact hdown
  have hbuffer := ReferenceFollowerSparseEmissionRecovery.accepted_window_logged_buffer_eq_physical_emissions
    R[b.val].input.state z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
    rewards s l span mode i seed memory hseed hvalid hpair htimes' logged cut after raw
    (P.downRecord i) scan registers lastService hlogActual hdownActual haccepted hsigma hwindow
  rw [hphysical] at hbuffer
  have hno := ReferenceFollowerSparseEmissionRecovery.accepted_window_no_prior_reset
    R[b.val].input.state z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
    rewards s l span mode i logged cut after raw (P.downRecord i) scan registers lastService
    hlogActual hdownActual haccepted hsigma hwindow
  change ∀ r ∈ (run R[b.val].input.state z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s l _ mode).records,
    ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i r at hno
  rw [hprior] at hno
  have htransition := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
    R[j.val] i logged cut after raw (P.downRecord i) scan registers lastService
    hlogged hdown haccepted
  have htransition' : ActiveFollowerDownAcceptance.downTransition p i R[j.val].input.row
      R[j.val].input.time (R[j.val].output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged =
        .accepted logged after raw (P.downRecord i) scan registers lastService := by
    simpa only [halign.1, halign.2.1, halign.2.2.1] using htransition
  have hscan := ReferenceAssignmentFollowerMassSteps.accepted_down_scan_endpoint i R[j.val].input.row
    R[j.val].input.time _ logged after raw (P.downRecord i) scan registers lastService htransition'
  have hstartP : ActiveFollowerDownAcceptance.downStart p rate (P.downRecord i) = P.sigma := by
    apply Fin.ext
    change (P.downRecord i).val.sigma - 1 = P.sigma.val
    rw [hMsigma, Nat.add_sub_cancel]
  obtain ⟨_, _, hrj⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z j
  have hrow : R[j.val].input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
    change (R.get j).input.row = _
    rw [hrj]
    rfl
  rw [hstartP, hrow] at hscan
  have hchecked := ActiveFollowerDownAcceptance.downTransition_accepted_checked p _ _ _ _ rate
    logged after raw (P.downRecord i) scan registers lastService htransition
  have hpositive : 1 ≤ v := by dsimp only [v]; omega
  have hjtime : R[j.val].input.time.val = s + l := by
    have hb := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z b
    have ht := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z j
    change R[b.val].input.time.val = _ at hb
    change R[j.val].input.time.val = _ at ht
    dsimp only [s, l]
    rw [hb, ht, Nat.add_assoc, Nat.add_sub_of_le hbefore]
  have hle : v ≤ l + 1 := by
    have hbound := hchecked.2.2.2.1
    rw [halign.2.2.1, hjtime] at hbound
    dsimp only [v]
    omega
  have hword := ReferenceFollowerSparseEmissionRecovery.accepted_window_recoveryQueueRecords_eq_physical_prefix
    R[b.val].input.state z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
    rewards s l span mode i seed memory hseed hvalid hpair htimes' logged cut after raw
    (P.downRecord i) scan registers lastService hlogActual hdownActual haccepted hsigma hwindow
  rw [hphysical, List.take_take, hMsigma] at hword
  have hmin : min v (l + 1) = v := Nat.min_eq_left hle
  change ActiveFollowerDownAcceptance.recoveryQueueRecords p rate (P.downRecord i) logged scan.endpoint =
    ((R.drop b.val).take (min v (l + 1))).map _ at hword
  rw [hmin] at hword
  have hresult := ReferenceFollowerSparseEmissionRecovery.accepted_window_checked_physical_queue
    R[b.val].input.state z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
    rewards s l span mode i seed memory hseed hvalid hpair htimes' logged cut after raw
    (P.downRecord i) scan registers lastService hlogActual hdownActual haccepted hsigma hwindow
  obtain ⟨hc, hreplay, _hsplit, _hscore, _hlast, _hqueue, hlastService, hprefix, _hraw⟩ := hresult
  have hphysicalWord :
      ((ReferenceFollowerSparseEmissionRecovery.physicalRecords R[b.val].input.state z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s l span mode).take
          (scan.endpoint - (P.downRecord i).val.sigma)).map
        (fun r => (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution (P.downRecord i) i r)) = word := by
    rw [hphysical, List.take_take, hMsigma]
    change ((R.drop b.val).take (min v (l + 1))).map _ = word
    rw [hmin]
  rw [hphysicalWord] at hreplay hprefix
  obtain ⟨hlastDown, hS, hdelta, hbacklog, nextMemory, hnext⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_down_output
      rewards C_star C_h z j i logged after cut raw (P.downRecord i) scan registers lastService
      hlogged hdown haccepted
  exact ⟨rfl, hscan, hpositive, hle, ⟨seed, memory, hseed, hseedStatus, hbuffer⟩,
    hno, hword, hc, hreplay, hprefix, hlastService, hlastDown, hS, hdelta, hbacklog,
    nextMemory, hnext⟩

private theorem complete_slice_connected_to_input
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : SourceInput p)
    (b n : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (hbn : b.val ≤ n.val) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    Connected R[b.val].input.state ((R.drop b.val).take (n.val - b.val))
      R[n.val].input.state := by
  intro R
  have hb : b.val < R.length := b.isLt
  have hn : n.val < R.length := n.isLt
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h ≠ none := by
    intro hnone
    have hb' := b.isLt
    simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone] at hb'
  have hl := ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
    rate z rewards C_star C_h hlaunch
  have chain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate z rewards C_star C_h _ hl
  have suffix := ReferenceFollowerReplyChronology.connected_drop_from_input chain b.val hb
  have hindex : n.val - b.val < (R.drop b.val).length := by
    simp only [List.length_drop]
    omega
  have hpref := ReferenceFollowerReplyChronology.connected_take_to_input suffix
    (n.val - b.val) hindex
  have heq : b.val + (n.val - b.val) = n.val := Nat.add_sub_of_le hbn
  simpa only [List.getElem_drop, heq] using hpref

/-- No accepted reset before the current diagnostic forces each earlier
actual choice to remain unoccupied, even when its seed has an old reply. -/
theorem complete_seed_no_reset_unoccupied_choice
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : SourceInput p)
    (b n j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hbn : b.val ≤ n.val) (hnj : n.val ≤ j.val) (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val].input.state.followers i = .ordinary seed seedMemory)
    (hseedStatus : seed.status = .unoccupied)
    (hno : ∀ r ∈ ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).drop b.val).take (j.val - b.val),
      ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i r) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∃ choice memory,
      (R[n.val].output.preparation.followers.followers i).configuration = .ordinary choice memory ∧
      choice.status = .unoccupied := by
  intro R
  obtain ⟨before, memory, choice, hinput, _hdomain, _hstart, hchoice,
      _hchoiceDomain, _hoperationDomain⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      rewards C_star C_h z n i
  have chain := complete_slice_connected_to_input rewards C_star C_h z b n hbn
  have hno' : ∀ r ∈ (R.drop b.val).take (n.val - b.val),
      ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i r := by
    intro r hr
    exact hno r ((List.take_prefix_take_left (l := R.drop b.val) (by omega : n.val - b.val ≤ j.val - b.val)).mem hr)
  have hstatus := (ReferenceFirstLiveDownNumericalRecovery.unoccupied_reply_of_no_reset
    chain i seed before seedMemory memory hseed hseedStatus hinput hno').1
  obtain ⟨before', memory', hbefore', _hreply, hkeep⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice R[n.val] i choice memory hchoice
  have hbeforeEq : before' = before :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hbefore'.symm.trans hinput)).1
  refine ⟨choice, memory, hchoice, ?_⟩
  exact hkeep (hbeforeEq.symm ▸ hstatus)

private theorem attributedArrival?_present_unoccupied
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (P : Payload rate) (i : Fin (p.m - 1))
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (r.output.preparation.followers.followers i).configuration = .ordinary choice memory)
    (hu : choice.status = .unoccupied) (value : Bool × ℕ)
    (hvalue : ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i r = some value) :
    value = (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution (P.downRecord i) i r) := by
  classical
  unfold ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? at hvalue
  cases hselected : r.output.preparation.coordinator.selection with
  | none => simp only [hselected, reduceCtorEq] at hvalue
  | some selected =>
      simp only [hselected] at hvalue
      split at hvalue
      · split at hvalue
        · simp only [hchoice, hu, ite_true, Option.some.injEq] at hvalue
          exact hvalue.symm
        · cases hvalue
      · cases hvalue

private theorem mapM_eq_emissions_of_present_unoccupied
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (P : Payload rate) (i : Fin (p.m - 1))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hchoices : ∀ r ∈ records, ∃ choice memory,
      (r.output.preparation.followers.followers i).configuration = .ordinary choice memory ∧
      choice.status = .unoccupied)
    (word : List (Bool × ℕ))
    (hword : records.mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word) :
    word = records.map
      (fun r => (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution (P.downRecord i) i r)) := by
  induction records generalizing word with
  | nil =>
      change some [] = some word at hword
      exact (Option.some.inj hword).symm
  | cons r rest ih =>
      obtain ⟨choice, memory, hchoice, hu⟩ := hchoices r List.mem_cons_self
      cases hhead : ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i r with
      | none => simp only [List.mapM_cons, hhead] at hword; cases hword
      | some value =>
          cases htail : rest.mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) with
          | none => simp only [List.mapM_cons, hhead, htail] at hword; cases hword
          | some tail =>
              have hv := attributedArrival?_present_unoccupied P i r choice memory hchoice hu value hhead
              have ht := ih (fun r hr => hchoices r (List.mem_cons_of_mem _ hr)) tail htail
              simp only [List.mapM_cons, hhead, htail] at hword
              change some (value :: tail) = some word at hword
              rw [← Option.some.inj hword, List.map_cons, hv, ht]

private theorem firstCell_calendar_replay_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := birthIndex rate rewards C_star C_h z
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b + 1)
    let N := 1 + W.length
    let V := (R.drop b).take N
    ∃ (L : List (RoundInput p.K)) (c : RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : Payload rate),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c ∧
      prefixInputs rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ R[b]? = some birth ∧ InstallationBirth birth P ∧ P.sigma = t ∧
      (∀ a, P.queues a = (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2) ∧
      (∀ i, (P.downRecord i).val.q = (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length (P.assignment.assigned i)).2) ∧
      V = birth :: W ∧ b + N ≤ R.length ∧
      (∀ i : Fin (p.m - 1), ∀ v, v ≤ N → ∃ word,
        (V.take v).mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word) ∧
      (∀ ell, ell ≤ p.T + 1 →
        ell ≤ FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) →
        ell - (P.sigma.val + 1) ≤ N) := by
  classical
  intro R b W N V
  obtain ⟨L, c, birth, P, _base, hL, hc, hinputs, hlen, hbirth,
      _hactual, _hbirthTime, _hrows, _hselected, _hrewards, _hrecordRows,
      _hchosen, _henabled, hborn, hSigma, _hcRate, _hcReward, hqueues,
      hbase, hterminal, hbirthWord, hafter⟩ :=
    ReferenceFirstCorrectedAssignedArrivalPrefix.firstCell_total_assigned_arrival_prefix
      rate rewards C_star C_h u t z hz
  have hbirth' : R[b]? = some birth := hbirth
  have htime : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b = t.val :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
      rate rewards C_star C_h u t z hz
  have hlength : R.length = p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  refine ⟨L, c, birth, P, hL, hc, hinputs, hlen, hbirth, hborn, hSigma,
    hqueues, fun i => (hbase i).2, ?_⟩
  by_cases hterm : t.val + 1 = p.T
  · have hend : b + 1 = R.length := hterminal hterm
    have hdrop : R.drop (b + 1) = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hW : W = [] := by
      change (R.drop (b + 1)).takeWhile _ = []
      rw [hdrop]
      rfl
    have hN : N = 1 := by simp only [N, hW, List.length_nil, Nat.add_zero]
    have hb : b < R.length := (List.getElem?_eq_some_iff.mp hbirth').1
    have hget : R.get ⟨b, hb⟩ = birth := by
      simpa only [List.get_eq_getElem] using (List.getElem?_eq_some_iff.mp hbirth').2
    have hV : V = [birth] := by
      dsimp only [V]
      rw [hN, List.take_one_drop_eq_of_lt_length hb, hget]
    refine ⟨by rw [hV, hW], by omega, ?_, ?_⟩
    · intro i v hv
      by_cases hv0 : v = 0
      · subst v
        exact ⟨[], by rfl⟩
      · have hv1 : v = 1 := by omega
        refine ⟨[(true, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c (P.assignment.assigned i))], ?_⟩
        simpa only [hV, hv1, List.take_succ_cons, List.take_zero] using hbirthWord hterm i
    · intro ell hell _hcut
      rw [hSigma]
      omega
  · have hsucc : t.val + 1 < p.T := by have ht := t.isLt; omega
    obtain ⟨rout, qout, beta, _hbirthNext, hk, hstate, hlater, _hB, hallv,
      hEbound, _hprefixEnd, hdrop, _hrowsW, rE, qE, _hpayloadE, _hstatesE,
      hboundary⟩ := hafter hsucc
    have hV : V = birth :: W := hdrop
    have hNbound : b + N ≤ R.length := by
      change b + (1 + W.length) ≤ R.length
      change b + 1 + W.length ≤ R.length at hEbound
      omega
    refine ⟨hV, hNbound, ?_, ?_⟩
    · intro i v hv
      by_cases hv0 : v = 0
      · subst v
        exact ⟨[], by rfl⟩
      · obtain ⟨word, hword⟩ : ∃ word,
            ((birth :: W).take v).mapM
              (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word :=
          ⟨_, hallv i v (by omega) hv⟩
        exact ⟨word, by rw [hV]; exact hword⟩
    · intro ell hell hcut
      rcases hboundary with hend | ⟨he, seg, I, l0, ccut, _hsegment,
        _hentry, _hpayload, _hpre, _hinitializer, _hI, _hchecked, _hassignment,
        _hsigmaI, hcutoffI, hfirstCutoff, _hrest⟩
      · change b + 1 + W.length = R.length at hend
        rw [hSigma]
        dsimp only [N]
        omega
      · have hU : FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
              (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
              (b + 1 + W.length) + 1 := hfirstCutoff.symm.trans hcutoffI
        rw [hU] at hcut
        rw [hSigma]
        dsimp only [N]
        omega

open ReferenceCollectionSegmentExtraction in
private theorem collection_choice_selection
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (ctx : Choice rate) (hchoice : choice r.input = some ctx) :
    ∃ selected : Selection r.input,
      r.output.preparation.coordinator.selection = some selected ∧ selected.view.payload = ctx.payload := by
  classical
  unfold choice at hchoice
  split at hchoice
  · contradiction
  next hn =>
    have hprep : (prepare r.input).coordinator = r.output.preparation.coordinator := by
      rw [r.output_eq]
      rfl
    rw [hprep] at hchoice hn
    cases hc : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp [hc, choiceOfCut] at hchoice
    | invalidCollectionCutoff => simp [hc, choiceOfCut] at hchoice
    | dagger => simp [hc, choiceOfCut] at hchoice
    | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals try contradiction
      next core snapshot hboundary hchecked =>
        rw [← Option.some.inj hchoice]
        exact ⟨_, rfl, rfl⟩
    | live registers owned base outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals try contradiction
      next dispatched hs ledger hi he hd hclock hp hn selected =>
        rw [← Option.some.inj hchoice]
        simp only [DispatchCut.selection, selectionAt, dite_true]
        exact ⟨_, rfl, rfl⟩

open ReferenceCollectionSegmentExtraction in
private theorem firstCell_first_collection_selections
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P : Payload rate)
    (hbirth : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[
      birthIndex rate rewards C_star C_h z]? = some birth)
    (hborn : InstallationBirth birth P) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := birthIndex rate rewards C_star C_h z
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b + 1)
    let e := b + (1 + W.length)
    e = R.length ∨ ∃ (he : e < R.length) (seg : Segment rate),
      segmentAt R e = some seg ∧ seg.entry = R[e] ∧ seg.context.payload = P ∧
      seg.records ++ seg.remaining = R.drop e ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1 ∧
      ∀ r ∈ seg.records, ∃ selected : Selection r.input,
        r.output.preparation.coordinator.selection = some selected ∧ selected.view.payload = P := by
  intro R b W e
  obtain ⟨otherBirth, rout, qout, beta, hotherBirth, htime, _hdate, _hrows, _hJ,
    _hrewards, hotherBorn, _hsigma, _hlater, _hnext, hcont⟩ :=
    ReferenceFirstCorrectedReplacementCollectionReadout.firstCell_collection_readout_cover
      rate rewards C_star C_h u t z hz
  have heq : otherBirth = birth := Option.some.inj (hotherBirth.symm.trans hbirth)
  subst otherBirth
  have hp : rout.payload = P :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique birth _ _ hotherBorn hborn
  by_cases hterm : t.val + 1 = p.T
  · have hlength : R.length = p.T - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
    have hend : b + 1 = R.length := by
      change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b = t.val at htime
      omega
    have hdrop : R.drop (b + 1) = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hW : W = [] := by
      change (R.drop (b + 1)).takeWhile _ = []
      rw [hdrop]
      rfl
    left
    dsimp only [e]
    rw [hW, List.length_nil, Nat.add_zero]
    exact hend
  · have hsucc : t.val + 1 < p.T := by have ht := t.isLt; omega
    obtain ⟨_hEbound, _hTbound, rE, qE, _hpayloadE, _hstatesE, hcase⟩ := hcont hsucc
    rcases hcase with hend | ⟨he, seg, I, l0, hseg, hentry, hpay, _hpre,
      _hinitializer, _hI, _hchecked, _hassignment, _hsigmaI, hcutoffI, hU,
      _hfreeze, _hbase, _hcutChosen, _hnonempty, hpartition, _hcalendar, hall⟩
    · left
      change b + 1 + W.length = R.length at hend
      dsimp only [e]
      omega
    · right
      have he' : e < R.length := by
        change b + 1 + W.length < R.length at he
        dsimp only [e]
        omega
      refine ⟨he', seg, ?_, ?_, hpay.trans hp, ?_, ?_, ?_⟩
      · change segmentAt R (b + 1 + W.length) = some seg at hseg
        simpa only [e, Nat.add_assoc] using hseg
      · change seg.entry = R[b + 1 + W.length] at hentry
        simpa only [e, Nat.add_assoc] using hentry
      · change seg.records ++ seg.remaining = R.drop (b + 1 + W.length) at hpartition
        simpa only [e, Nat.add_assoc] using hpartition
      · rw [← hp]
        have hcut := hU.symm.trans hcutoffI
        change FollowerCutoffScan.firstCutoff p rate.eta.val rout.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
            (b + 1 + W.length) + 1 at hcut
        simpa only [e, Nat.add_assoc] using hcut
      · intro r hr
        obtain ⟨done, _cell, hdone, _hrest⟩ := hall r hr
        have hctx : done.context.payload = P := _hrest.2.2.1.trans hp
        obtain ⟨selected, hselected, hselectedP⟩ := collection_choice_selection r done.context
          (actual_collection_round_checked r done hdone).1
        exact ⟨selected, hselected, hselectedP.trans hctx⟩

private theorem raw_mismatch_rejected
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hmismatch : ReferenceDownReception.rawMismatch
      (ReferenceDownReception.referenceDownCut p view i row t observation rate logged)) :
    let cut := ReferenceDownReception.referenceDownCut p view i row t observation rate logged
    cut.filteredRaw = none ∧ ∃ after raw,
      cut.outcome = .decodeOrParseRejected logged after raw := by
  classical
  unfold ReferenceDownReception.rawMismatch ReferenceDownReception.referenceDownCut at hmismatch
  split at hmismatch
  next hselected =>
    split at hmismatch
    next hstatus =>
      split at hmismatch
      next hregisters =>
        split at hmismatch
        next hbatch =>
          split at hmismatch
          next hbuffer =>
            dsimp only at hmismatch
            split at hmismatch
            next hmatch => simp only [Option.some.injEq, Bool.true_eq_false] at hmismatch
            next hmatch =>
              simp only [ReferenceDownReception.referenceDownCut, dite_eq_left hselected,
                dite_eq_left hstatus, dite_eq_left hregisters, dite_eq_left hbatch, dite_eq_left hbuffer,
                dite_eq_right hmatch]
              exact ⟨True.intro, _, _, rfl⟩
          next => cases hmismatch
        next => cases hmismatch
      next => cases hmismatch
    next => cases hmismatch
  next => cases hmismatch

/-- Every actual source diagnostic retains its original local alternative.
Checked input/output failures are excluded by the actual ordinary follower
output. In particular, a raw mismatch is a rejection with no filtered word,
not a successful or failed replay. -/
theorem complete_down_diagnostic_outcomes
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : SourceInput p)
    (j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hdown : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[j.val].output.followers i).down = some cut) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j.val]
    ∃ logged : ReferencePrelaunchFollower.State p rate.eta,
      (r.output.followers i).downInput = some logged ∧
      (ReferenceDownReception.rawMismatch cut → cut.filteredRaw = none ∧ ∃ after raw,
        cut.outcome = .decodeOrParseRejected logged after raw) ∧
      ((∃ before reason, cut.outcome = .skipped before reason) ∨
       (∃ before after raw, cut.outcome = .decodeOrParseRejected before after raw) ∨
       (∃ before after raw M, cut.outcome = .parsedButUnaccepted before after raw M) ∨
       (∃ before after raw M scan registers lastService,
         cut.outcome = .accepted before after raw M scan registers lastService)) := by
  intro r
  obtain ⟨choice, memory, logged, hchoice, hu, hlogging, hinput, hcut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hdown
  refine ⟨logged, hinput, ?_, ?_⟩
  · intro hmismatch
    rw [hcut] at hmismatch ⊢
    exact raw_mismatch_rejected _ _ _ _ _ _ hmismatch
  · obtain ⟨_state, _memory, _choice, _next, _nextMemory, _hinput, _hchoice,
        _hchoiceDomain, _hnextDomain, _houtput, hfailure, _hnext⟩ :=
      ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_output
        rewards C_star C_h z j i
    have hfinish := ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i r
    have hrecord :
        (ReferenceActivePhysicalStep.recordFollower r.output.preparation.coordinator.downView
          (r.output.preparation.followers.followers i).follower
          (r.output.preparation.followers.followers i).row
          (r.output.preparation.followers.followers i).activation
          (r.output.preparation.followers.followers i).time
          (r.output.preparation.followers.followers i).active
          (r.output.preparation.followers.followers i).arm
          (r.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice).result =
        DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome := by
      simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hlogging]
      rw [← hcut]
    cases houtcome : cut.outcome with
    | skipped before reason => exact Or.inl ⟨before, reason, rfl⟩
    | decodeOrParseRejected before after raw => exact Or.inr (Or.inl ⟨before, after, raw, rfl⟩)
    | parsedButUnaccepted before after raw M => exact Or.inr (Or.inr (Or.inl ⟨before, after, raw, M, rfl⟩))
    | accepted before after raw M scan registers lastService =>
      exact Or.inr (Or.inr (Or.inr ⟨before, after, raw, M, scan, registers, lastService, rfl⟩))
    | inputFailure before reason =>
      have hfail : (r.output.followers i).failure = some (.downInput reason) := by
        rw [hfinish, ReferenceActivePhysicalStep.finishFollower, hchoice]
        simp only [hrecord, houtcome, DeclaredFollowerLocalRound.consumeDownResult]
      rw [hfailure] at hfail
      cases hfail
    | outputFailure before reason =>
      have hfail : (r.output.followers i).failure = some (.downOutput reason) := by
        rw [hfinish, ReferenceActivePhysicalStep.finishFollower, hchoice]
        simp only [hrecord, houtcome, DeclaredFollowerLocalRound.consumeDownResult]
      rw [hfailure] at hfail
      cases hfail

private theorem recovery_last_service_word_difference
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (logged : ReferencePrelaunchFollower.State p rate.eta) (ell lastService : ℕ)
    (word : List (Bool × ℕ))
    (hword : ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell = word)
    (hi : M.val.sigma < ell)
    (hservice : lastService =
      (ActiveFollowerDownAcceptance.recoveredLastTransition p rate M logged ell hi).1 -
      (ActiveFollowerDownAcceptance.recoveredRegistersBeforeLast p rate M logged ell hi).1) :
    lastService = (QueueReplay.replay (4 * rate.n) (0, M.val.q) word).1 -
      (QueueReplay.replay (4 * rate.n) (0, M.val.q)
        (word.take (ell - M.val.sigma - 1))).1 := by
  have hlength : (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged (ell - 1)).length =
      ell - M.val.sigma - 1 := by
    simp only [ActiveFollowerDownAcceptance.recoveryQueueRecords,
      ActiveFollowerDownAcceptance.recoveryArrivals, List.length_map,
      ActiveFollowerDownAcceptance.recoveryRounds_length]
    omega
  have hprev : word.take (ell - M.val.sigma - 1) =
      ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged (ell - 1) := by
    rw [← hword, ActiveFollowerDownAcceptance.recoveryQueueRecords_append_last p rate M logged ell hi,
      ← hlength, List.take_left]
  have hlast : ActiveFollowerDownAcceptance.recoveredLastTransition p rate M logged ell hi =
      QueueReplay.replay (4 * rate.n) (0, M.val.q) word := by
    rw [← ActiveFollowerDownAcceptance.recoveredRegisters_eq_lastTransition,
      ActiveFollowerDownAcceptance.recoveredRegisters, hword]
  rw [hservice, hlast, hprev]
  rfl

/-- The original first corrected installation's accepted native DOWN word
is the same total attributed calendar prefix. All later actual records are
covered on their literal current-P selection branch, so this includes LIVE,
the first cutoff, late collection acceptance, and a failed coordinator exit
that still selects P. No future UP or successful coordinator tail is required.
The empty prefix retains the original queue; no analytical overflow coverage
is asserted for that separate seed. -/
theorem firstCell_native_down_calendar_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let b := birthIndex rate rewards C_star C_h z
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b + 1)
    let N := 1 + W.length
    let V := (R.drop b).take N
    ∃ (L : List (RoundInput p.K)) (c : RoundInput p.K)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (P : Payload rate),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c ∧
      prefixInputs rate rewards C_star C_h (t.val + 1) z = some (L ++ [c]) ∧
      L.length = b ∧ R[b]? = some birth ∧ InstallationBirth birth P ∧ P.sigma = t ∧
      (∀ a, P.queues a = (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2) ∧
      (∀ i, (P.downRecord i).val.q = (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length (P.assignment.assigned i)).2) ∧
      V = birth :: W ∧ b + N ≤ R.length ∧
      (∀ i : Fin (p.m - 1), ∀ v, v ≤ N → ∃! word,
        (V.take v).mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word) ∧
      (let e := b + N
       e = R.length ∨ ∃ (he : e < R.length) (seg : ReferenceCollectionSegmentExtraction.Segment rate),
         ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧ seg.entry = R[e] ∧
         seg.context.payload = P ∧ seg.records ++ seg.remaining = R.drop e ∧
         FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
           (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
             (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
           ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e + 1 ∧
         ∀ r ∈ seg.records, ∃ selected : Selection r.input,
           r.output.preparation.coordinator.selection = some selected ∧ selected.view.payload = P) ∧
      ∀ (j : Fin R.length), b ≤ j.val → ∀ i : Fin (p.m - 1),
        (R[j.val].output.followers i).failure = none ∧
        (∀ cut : ReferenceDownReception.ReferenceDownCutOutput p rate,
          (R[j.val].output.followers i).down = some cut →
          ∃ logged : ReferencePrelaunchFollower.State p rate.eta,
            (R[j.val].output.followers i).downInput = some logged ∧
            (ReferenceDownReception.rawMismatch cut → cut.filteredRaw = none ∧ ∃ after raw,
              cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.decodeOrParseRejected logged after raw) ∧
            ((∃ before reason, cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.skipped before reason) ∨
             (∃ before after raw, cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.decodeOrParseRejected before after raw) ∨
             (∃ before after raw M, cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.parsedButUnaccepted before after raw M) ∨
             (∃ before after raw M scan registers lastService,
               cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted before after raw M scan registers lastService))) ∧
        ∀ current : Selection R[j.val].input,
          R[j.val].output.preparation.coordinator.selection = some current →
          if current.view.payload = P then
            ∀ (logged before after : ReferencePrelaunchFollower.State p rate.eta)
              (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
              (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
              (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
              (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ),
              (R[j.val].output.followers i).downInput = some logged →
              (R[j.val].output.followers i).down = some cut →
              cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted before after raw M scan registers lastService →
              before = logged ∧ ¬ ReferenceDownReception.rawMismatch cut ∧
              let v := scan.endpoint - (P.sigma.val + 1)
              ∃ word : List (Bool × ℕ),
                (V.take v).mapM (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word ∧
                M = P.downRecord i ∧
                scan.endpoint = min
                  (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))))
                  (R[j.val].input.time.val + 2) ∧
                1 ≤ v ∧ v ≤ N ∧
                (b + N ≤ j.val → scan.endpoint =
                  FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧ v = N) ∧
                (∃ (seed : ReferencePrelaunchFollower.State p rate.eta)
                  (memory : ActiveFollowerLifecycle.LocalMemory p),
                  birth.input.state.followers i = DeclaredFollowerLocalRound.LocalConfiguration.ordinary seed memory ∧
                  seed.status = ActiveRoundActions.FollowerStatus.unoccupied ∧
                  logged.buffer = seed.buffer ++
                    ((R.drop b).take (j.val - b + 1)).flatMap
                      (ReferenceFollowerBufferProvenance.logEmission i)) ∧
                (∀ r ∈ (R.drop b).take (j.val - b),
                  ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i r) ∧
                ActiveFollowerDownAcceptance.recoveryQueueRecords p rate (P.downRecord i) logged scan.endpoint = word ∧
                ActiveFollowerDownAcceptance.checkedRecovery p rate (P.downRecord i) logged scan.endpoint =
                  Except.ok (⟨registers, lastService⟩ : ActiveFollowerDownAcceptance.ReplayRegisters) ∧
                registers = QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word ∧
                (∀ k, ∃ middle,
                  ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
                    ⟨(0, (P.downRecord i).val.q), 0⟩ (word.take k) = Except.ok middle ∧
                  ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
                  middle.registers = QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word.take k)) ∧
                (∃ hinterval : (P.downRecord i).val.sigma < scan.endpoint,
                  lastService =
                    (ActiveFollowerDownAcceptance.recoveredLastTransition p rate (P.downRecord i) logged
                      scan.endpoint hinterval).1 -
                    (ActiveFollowerDownAcceptance.recoveredRegistersBeforeLast p rate (P.downRecord i) logged
                      scan.endpoint hinterval).1) ∧
                lastService = (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 -
                  (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word.take (v - 1))).1 ∧
                after.lastDown = some (P.downRecord i) ∧ after.S = registers.1 ∧
                after.delta = lastService ∧ after.backlog = registers.2 ∧
                ∃ nextMemory : ActiveFollowerLifecycle.LocalMemory p,
                  R[j.val].output.next.followers i = DeclaredFollowerLocalRound.LocalConfiguration.ordinary after nextMemory
          else True := by
  classical
  intro R b W N V
  obtain ⟨L, c, birth, P, hL, hc, hinputs, hlen, hbirth, hborn, hSigma,
      hqueues, hdownQueues, hV, hNbound, htotal, hendpointBound⟩ :=
    firstCell_calendar_replay_data rate rewards C_star C_h u t z hz
  have hbirth' : R[b]? = some birth := hbirth
  have hb : b < R.length := (List.getElem?_eq_some_iff.mp hbirth').1
  have hget : R[b] = birth := (List.getElem?_eq_some_iff.mp hbirth').2
  have hborn' : InstallationBirth R[b] P := by rw [hget]; exact hborn
  have hcollection := firstCell_first_collection_selections
    rate rewards C_star C_h u t z hz birth P hbirth hborn
  refine ⟨L, c, birth, P, hL, hc, hinputs, hlen, hbirth, hborn, hSigma,
    hqueues, hdownQueues, hV, hNbound, ?_, hcollection, ?_⟩
  · intro i v hv
    obtain ⟨word, hw⟩ := htotal i v hv
    exact ⟨word, hw, fun other ho => Option.some.inj (ho.symm.trans hw)⟩
  · intro j hbj i
    obtain ⟨_state, _memory, _choice, _next, _nextMemory, _hinput, _hchoice,
      _hchoiceDomain, _hnextDomain, _houtput, hfailure, _hnext⟩ :=
      ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_output
        rewards C_star C_h z j i
    refine ⟨hfailure, fun cut hdown =>
      complete_down_diagnostic_outcomes rewards C_star C_h z j i cut hdown, ?_⟩
    intro current hselected
    by_cases hp : current.view.payload = P
    · simp only [ite_eq_left hp]
      intro logged before after cut raw M scan registers lastService hlogged hdown haccepted
      obtain ⟨_choice, _memory, actualLogged, _hchoice, _hu, _hlogging, hinput, hcut⟩ :=
        ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice R[j.val] i cut hdown
      have hloggedEq : actualLogged = logged := Option.some.inj (hinput.symm.trans hlogged)
      subst actualLogged
      have hacceptedCut := haccepted
      rw [hcut] at hacceptedCut
      have hbefore := ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_before_eq
        _ _ _ _ _ logged before after raw M scan registers lastService hacceptedCut
      subst before
      have hnoRaw : ¬ ReferenceDownReception.rawMismatch cut := by
        rw [hcut]
        exact ReferenceFollowerSparseEmissionRecovery.acceptedReferenceCut_not_rawMismatch
          _ _ _ _ _ logged after raw M scan registers lastService hacceptedCut
      refine ⟨rfl, hnoRaw, ?_⟩
      let v := scan.endpoint - (P.sigma.val + 1)
      obtain ⟨hM, hscan, hvpos, hvj, hseed, hno, hword, hchecked, hreplay,
        hprefix, hlastService, hlastDown, hS, hdelta, hbacklog, nextMemory, hnext⟩ :=
        complete_birth_current_down_physical_recovery rewards C_star C_h z
          ⟨b, hb⟩ j P hborn' hbj current hselected hp i logged after cut raw M scan
          registers lastService hlogged hdown haccepted
      change v ≤ j.val - b + 1 at hvj
      have htransition := ReferenceFollowerSparseEmissionRecovery.actualAcceptedCut_downTransition
        R[j.val] i logged cut after raw M scan registers lastService hlogged hdown haccepted
      have hdomain := ActiveFollowerDownAcceptance.downTransition_accepted_checked p _ _ _ _ rate
        logged after raw M scan registers lastService htransition
      have hvN : v ≤ N := hendpointBound scan.endpoint hdomain.2.2.2.2.1
        (hscan ▸ Nat.min_le_left _ _)
      have hlate : b + N ≤ j.val → scan.endpoint =
          FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
              (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) ∧ v = N := by
        intro hlateIndex
        rcases hcollection with hend | ⟨he, seg, _hseg, _hentry, _hpayload,
          _hpartition, hcutoff, _hselected⟩
        · change b + N = R.length at hend
          have hj := j.isLt
          omega
        · change FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
              (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + (b + N) + 1 at hcutoff
          have hjtime := ReferenceAssignmentFollowerMassSteps.complete_record_time
            rate rewards C_star C_h z j
          change R[j.val].input.time.val = _ at hjtime
          have hbirthtime := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
            rate rewards C_star C_h u t z hz
          change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b = t.val at hbirthtime
          have hs : scan.endpoint =
              FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                  (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) := by
            have hminBound :
                ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + (b + N) + 1 ≤
                ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + j.val + 2 :=
              (Nat.add_le_add_right (Nat.add_le_add_left hlateIndex _) 1).trans (Nat.le_succ _)
            rw [hscan, hcutoff, hjtime, Nat.min_eq_left hminBound]
          refine ⟨hs, ?_⟩
          dsimp only [v]
          rw [hs, hcutoff, hSigma, ← hbirthtime]
          have hsum : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + (b + N) + 1 =
              (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b + 1) + N := by
            ac_rfl
          rw [hsum, Nat.add_sub_cancel_left]
      obtain ⟨word, hcalendar⟩ := htotal i v hvN
      obtain ⟨seed, seedMemory, hseedInput, hseedStatus, hbuffer⟩ := hseed
      have hchoices : ∀ r ∈ (R.drop b).take v, ∃ choice memory,
          (r.output.preparation.followers.followers i).configuration = DeclaredFollowerLocalRound.LocalConfiguration.ordinary choice memory ∧
          choice.status = ActiveRoundActions.FollowerStatus.unoccupied := by
        intro r hr
        obtain ⟨a, ha, hgetr⟩ := List.mem_iff_getElem.mp hr
        have ha' : a < v ∧ a < R.length - b := by
          simpa only [List.length_take, List.length_drop, lt_min_iff] using ha
        have hindex : b + a < R.length := by omega
        have hr' : R[b + a] = r := by
          simpa only [List.getElem_take, List.getElem_drop] using hgetr
        rw [← hr']
        exact complete_seed_no_reset_unoccupied_choice rewards C_star C_h z
          ⟨b, hb⟩ ⟨b + a, hindex⟩ j (by change b ≤ b + a; omega)
          (by change b + a ≤ j.val; omega) i seed seedMemory hseedInput hseedStatus hno
      have hcalendar' : ((R.drop b).take v).mapM
          (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) = some word := by
        change (((R.drop b).take N).take v).mapM _ = some word at hcalendar
        rw [List.take_take, Nat.min_eq_left hvN] at hcalendar
        exact hcalendar
      have hemission := mapM_eq_emissions_of_present_unoccupied P i
        ((R.drop b).take v) hchoices word hcalendar'
      change word = ((R.drop b).take v).map _ at hemission
      rw [← hemission] at hword hreplay hprefix
      have hserviceWord : lastService =
          (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) word).1 -
          (QueueReplay.replay (4 * rate.n) (0, (P.downRecord i).val.q) (word.take (v - 1))).1 := by
        obtain ⟨hi, hs⟩ := hlastService
        have h := recovery_last_service_word_difference (P.downRecord i) logged scan.endpoint
          lastService word hword hi hs
        have hMsigma := congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
        simpa only [hMsigma, v] using h
      exact ⟨word, hcalendar, hM, hscan, hvpos, hvN, hlate,
        ⟨seed, seedMemory, by rw [← hget]; exact hseedInput, hseedStatus, hbuffer⟩,
        hno, hword, hchecked, hreplay, hprefix, hlastService, hserviceWord,
        hlastDown, hS, hdelta, hbacklog, nextMemory, hnext⟩
    · simp only [ite_eq_right hp]

end Bandits.Support.ReferenceFirstCorrectedNativeDownCalendarReplay

end
