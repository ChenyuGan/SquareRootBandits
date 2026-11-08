/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCollectionKnownQueueOverflowCover
public import Bandits.Support.ReferenceFirstCorrectedCollectionBoundaryExclusion

import Mathlib.Tactic

/-!
# Literal coordinator queue sites on the first corrected assignment

This module starts the original-source coordinator-site observer for one
corrected assignment.  The observer reads actual optional records, registers,
installations, recorder calls, service candidates, and retained-collection
operations.  It does not turn absent registers into zero-valued queues.

Sources: ZIP4 `appendix_a_local_protocol.tex:8-64`,
`06_interruptions.tex:40-100,192-233,246-299,391-408,425-426`, and
`04_slow_fast_learner.tex:157-187,256-290`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
  (correctedCell sourceRecords birthIndex liveTail)
open ReferenceCollectionSegmentExtraction
open ReferenceFirstCorrectedCollectionKnownQueueSource
  (QueueRegisterField)
open ReferenceFirstCorrectedCollectionKnownQueueOverflowCover
  (KnownQueueSourceSite firstCollectionKnownQueueOverflowEvent
    firstCollectionKnownQueueOverflowEvent_subset_allArmCollectionOverflowEvent)
open ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow
  (allArmCollectionOverflowEvent)

namespace Bandits.Support.ReferenceFirstCorrectedCoordinatorQueueOverflowCover

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord
  (p := p) (rate := rate)
local notation "Segment" => ReferenceCollectionSegmentExtraction.Segment rate
local notation "Payload" => ReferenceActivePhysicalStep.Payload rate
local notation "Registers" => CoordinatorLiveChoiceRecorderStep.Registers p rate.eta
local notation "Owned" => fun (r : Registers) =>
  CoordinatorLiveServiceFinish.OwnedRegisters r

/-- The raw complement residual is available after the source service pass's
input, arrival, service, and score guards.  Deliberately, its existence does
not test the later queue-output-domain guard. -/
def reachedCoordinatorResidual? (r : Registers) (owned : Owned r)
    (recording : CoordinatorRecordingOperation.Output p) (a : Fin p.K) : Option ℕ := by
  classical
  exact if ha : a ∉ r.payload.slowSet.val then
    if hqueue : owned.queueDomainValid then
      if hprevious : owned.previousServiceDomainValid then
        let arrival : CanonicalFastSampling.FastArm r.payload.slowSet → ℕ :=
          fun j => CoordinatorLiveServiceFinish.complementArrival r.payload recording j
        if harrival : ∀ j, arrival j ≤ D p then
          let service : CanonicalFastSampling.FastArm r.payload.slowSet → ℕ :=
            fun j => CappedService.service (4 * r.payload.n) (owned.queue j) (arrival j)
          if hservice : ∀ j, service j ≤ D p then
            let score : CanonicalFastSampling.FastArm r.payload.slowSet → ℕ :=
              fun j => r.complementScores j + service j
            if hscore : ∀ j, score j ≤ p.T * D p then
              some (CappedService.residual (4 * r.payload.n)
                (owned.queue ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩)
                (arrival ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩))
            else none
          else none
        else none
      else none
    else none
  else none

/-- On an actual successful service pass, the literal pre-output residual
equals its stored queue.  The observer itself does not test servicePass's
final output-domain guard, so a reached candidate discarded there remains
present. -/
theorem reachedCoordinatorResidual?_eq_serviced
    (r : Registers) (owned : Owned r)
    (recording : CoordinatorRecordingOperation.Output p)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r owned)
    (hservice : CoordinatorLiveServiceFinish.servicePass r owned recording = .ok serviced)
    (a : Fin p.K) (ha : a ∉ r.payload.slowSet.val) :
    reachedCoordinatorResidual? rate r owned recording a =
      some (serviced.queue
        ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩) := by
  classical
  have hqueue : owned.queueDomainValid := by
    by_contra hbad
    simp [CoordinatorLiveServiceFinish.servicePass, hbad] at hservice
  have hprevious : owned.previousServiceDomainValid := by
    by_contra hbad
    simp [CoordinatorLiveServiceFinish.servicePass, hqueue, hbad] at hservice
  have harrivalSource : ∀ (a : Fin p.K)
      (ha : a ∉ r.payload.slowSet.val),
      CoordinatorLiveServiceFinish.complementArrival r.payload recording
        ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩ ≤ D p := by
    by_contra hbad
    simp [CoordinatorLiveServiceFinish.servicePass, hqueue, hprevious, hbad] at hservice
  have harrival : ∀ j, CoordinatorLiveServiceFinish.complementArrival
      r.payload recording j ≤ D p := fun j =>
        harrivalSource j.1 (Finset.mem_sdiff.mp j.2).2
  have hserviceDomainSource : ∀ (a : Fin p.K)
      (ha : a ∉ r.payload.slowSet.val),
      CappedService.service (4 * r.payload.n)
        (owned.queue ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩)
        (CoordinatorLiveServiceFinish.complementArrival r.payload recording
          ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩) ≤ D p := by
    by_contra hbad
    simp [CoordinatorLiveServiceFinish.servicePass, hqueue, hprevious, harrival,
      hbad] at hservice
  have hserviceDomain : ∀ j,
      CappedService.service (4 * r.payload.n) (owned.queue j)
        (CoordinatorLiveServiceFinish.complementArrival r.payload recording j) ≤ D p :=
    fun j => hserviceDomainSource j.1 (Finset.mem_sdiff.mp j.2).2
  have hscoreDomainSource : ∀ (a : Fin p.K)
      (ha : a ∉ r.payload.slowSet.val),
      r.complementScores ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩ +
        CappedService.service (4 * r.payload.n)
        (owned.queue ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩)
        (CoordinatorLiveServiceFinish.complementArrival r.payload recording
          ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩) ≤
          p.T * D p := by
    by_contra hbad
    simp [CoordinatorLiveServiceFinish.servicePass, hqueue, hprevious, harrival,
      hserviceDomain, hbad] at hservice
  have hscoreDomain : ∀ j,
      r.complementScores j + CappedService.service (4 * r.payload.n)
        (owned.queue j) (CoordinatorLiveServiceFinish.complementArrival r.payload recording j) ≤
          p.T * D p := fun j => hscoreDomainSource j.1 (Finset.mem_sdiff.mp j.2).2
  have hrecording : serviced.recording = recording := by
    have hmap :
        (CoordinatorLiveServiceFinish.servicePass r owned recording).map
            (fun result => result.recording) =
          (CoordinatorLiveServiceFinish.servicePass r owned recording).map
            (fun _ => recording) := by
      classical
      unfold CoordinatorLiveServiceFinish.servicePass
      dsimp only
      split_ifs <;> simp [Except.map]
    have hmapped := congrArg
      (fun result : Except CoordinatorLiveServiceFinish.Failure
        (CoordinatorLiveServiceFinish.ServicedRegisters r owned) =>
          result.map (fun output => output.recording)) hservice
    rw [hmap, hservice] at hmapped
    exact (Except.ok.inj hmapped).symm
  rw [serviced.queue_eq
    ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩]
  rw [serviced.arrival_eq
    ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩]
  rw [hrecording]
  simp [reachedCoordinatorResidual?, ha, hqueue, hprevious, harrival,
    hserviceDomain, hscoreDomain]

/-- Identity of a coordinator queue observation.  Source positions index the
original complete suffix; the live-tail and segment indices are local to the
same actual lists.  The known-site constructor deliberately retains the
accepted operation witness verbatim. -/
inductive CoordinatorQueueSite
    (R : List Record) (b : ℕ) (W : List Record) (P : Payload)
    (segment : Option Segment) : Type where
  | birthInputCurrent (a : Fin p.K)
  | birthInputCutoff (a : Fin p.K)
  | birthReconstructionCurrent (a : Fin p.K)
  | birthReconstructionCutoff (a : Fin p.K)
  | birthInstalledPayload (a : Fin p.K)
  | birthInitialQueue (a : Fin p.K)
  | birthComplementChoice (a : Fin p.K)
  | birthServiceResidual (a : Fin p.K)
  | birthOutput (a : Fin p.K)
  | liveInput (i : Fin W.length) (a : Fin p.K)
  | liveChoice (i : Fin W.length) (a : Fin p.K)
  | liveServiceResidual (i : Fin W.length) (a : Fin p.K)
  | liveOutput (i : Fin W.length) (a : Fin p.K)
  | cutoffInput (seg : Segment) (a : Fin p.K) (hsegment : segment = some seg)
  | knownQueue {seg : Segment} (a : Fin p.K)
      (field : QueueRegisterField) (q : ℕ)
      (hsegment : segment = some seg)
      (site : KnownQueueSourceSite rate seg a field q)
  | excludedInstalledPayload (seg : Segment) (a : Fin p.K)
      (hsegment : segment = some seg)
  | excludedInitialQueue (seg : Segment) (a : Fin p.K)
      (hsegment : segment = some seg)
  | excludedComplementChoice (seg : Segment) (a : Fin p.K)
      (hsegment : segment = some seg)

/-- Read one queue only from the actual operation named by the site.  Each
branch leaves unavailable inputs absent, including missing registers,
non-complement arms, missing records/segments, and un-reached service calls. -/
def physicalQueueAt? (R : List Record) (b : ℕ) (W : List Record)
    (P : Payload) (segment : Option Segment)
    (site : CoordinatorQueueSite rate R b W P segment) : Option ℕ := by
  classical
  cases site with
  | birthInputCurrent a =>
      exact (R[b]?).bind fun r =>
        match r.input.state.coordinator with
        | .collection _ ledger _ =>
            (ledger.currentRegisters a).map CoordinatorCollectionLedger.CurrentRegister.queue
        | _ => none
  | birthInputCutoff a =>
      exact (R[b]?).bind fun r =>
        match r.input.state.coordinator with
        | .collection _ ledger _ =>
            (ledger.cutoffRegisters a).map CoordinatorCollectionLedger.CutoffRegister.queue
        | _ => none
  | birthReconstructionCurrent a =>
      exact (R[b]?).bind fun r =>
        match r.output.preparation.coordinator with
        | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ output _ _ _ _) =>
            some (output.reconstruction.registers.current a).queue
        | _ => none
  | birthReconstructionCutoff a =>
      exact (R[b]?).bind fun r =>
        match r.output.preparation.coordinator with
        | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ output _ _ _ _) =>
            some (output.reconstruction.registers.cutoff a).queue
        | _ => none
  | birthInstalledPayload a =>
      exact (R[b]?).bind fun r =>
        match r.output.preparation.coordinator with
        | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
            some (installed.registers.payload.queues a)
        | _ => none
  | birthInitialQueue a =>
      exact (R[b]?).bind fun r =>
        match r.output.preparation.coordinator with
        | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ output _ _ _ _) =>
            some (AssignmentScoreReconstruction.initialQueue output.reconstruction a)
        | _ => none
  | birthComplementChoice a =>
      exact (R[b]?).bind fun r =>
        match r.output.preparation.coordinator with
        | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
            if ha : a ∉ installed.registers.payload.slowSet.val then
              some (installed.ownedRegisters.queue
                ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩)
            else none
        | _ => none
  | birthServiceResidual a =>
      exact (R[b]?).bind fun r =>
        match r.output.preparation.coordinator with
        | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
            (r.output.coordinator.recording).bind fun recording =>
              reachedCoordinatorResidual? rate installed.registers installed.ownedRegisters
                recording a
        | _ => none
  | birthOutput a =>
      exact (R[b]?).bind fun r =>
        match r.output.next.coordinator with
        | .live registers owned _ =>
            if ha : a ∉ registers.payload.slowSet.val then
              some (owned.queue ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩) else none
        | _ => none
  | liveInput i a =>
      exact (some (W[i])).bind fun r =>
        match r.input.state.coordinator with
        | .live registers owned _ =>
            if ha : a ∉ registers.payload.slowSet.val then
              some (owned.queue ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩)
            else none
        | _ => none
  | liveChoice i a =>
      exact (some (W[i])).bind fun r =>
        match r.output.preparation.coordinator with
        | .live registers owned _ (.continuingChosen _ _ _ _) =>
            let liveRegisters := ReferenceActivePhysicalStep.liveRegistersAt registers r.input.time
            let liveOwned := ReferenceActivePhysicalStep.liveOwnedAt registers owned r.input.time
            if ha : a ∉ liveRegisters.payload.slowSet.val then
              some (liveOwned.queue
                ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩)
            else none
        | _ => none
  | liveServiceResidual i a =>
      exact (some (W[i])).bind fun r =>
        match r.output.preparation.coordinator with
        | .live registers owned _ (.continuingChosen _ _ _ _) =>
            let liveRegisters := ReferenceActivePhysicalStep.liveRegistersAt registers r.input.time
            let liveOwned := ReferenceActivePhysicalStep.liveOwnedAt registers owned r.input.time
            (r.output.coordinator.recording).bind fun recording =>
              reachedCoordinatorResidual? rate liveRegisters liveOwned recording a
        | _ => none
  | liveOutput i a =>
      exact (some (W[i])).bind fun r =>
        match r.output.next.coordinator with
        | .live registers owned _ =>
            if ha : a ∉ registers.payload.slowSet.val then
              some (owned.queue ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩)
            else none
        | _ => none
  | cutoffInput seg a _hsegment =>
      exact match seg.entry.input.state.coordinator with
      | .live registers owned _ =>
          if ha : a ∉ registers.payload.slowSet.val then
            some (owned.queue ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩) else none
      | _ => none
  | knownQueue a field q _hsegment _hsite => exact some q
  | excludedInstalledPayload seg a _hsegment =>
      exact seg.remaining.head?.bind fun r =>
        match r.output.preparation.coordinator with
        | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
            some (installed.registers.payload.queues a)
        | _ => none
  | excludedInitialQueue seg a _hsegment =>
      exact seg.remaining.head?.bind fun r =>
        match r.output.preparation.coordinator with
        | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ output _ _ _ _) =>
            some (AssignmentScoreReconstruction.initialQueue output.reconstruction a)
        | _ => none
  | excludedComplementChoice seg a _hsegment =>
      exact seg.remaining.head?.bind fun r =>
        match r.output.preparation.coordinator with
        | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
            if ha : a ∉ installed.registers.payload.slowSet.val then
              some (installed.ownedRegisters.queue
                ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩)
            else none
        | _ => none

/-- Literal threshold event for actual first-corrected-assignment coordinator
queue fields and reached service residuals.  The birth, live tail, retained
segment, and first-excluded record are the original source objects. -/
def coordinatorQueueOverflowEvent (u t : Fin p.T) : Set X :=
  {z | z ∈ correctedCell rate rewards C_star C_h u t ∧
    let R := sourceRecords rate rewards C_star C_h z
    let b := birthIndex rate rewards C_star C_h z
    let W := liveTail rate rewards C_star C_h z
    let e := b + 1 + W.length
    ∃ birth : Record, R[b]? = some birth ∧
    ∃ P : Payload, ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧
      ∃ site : CoordinatorQueueSite rate R b W P
          (ReferenceCollectionSegmentExtraction.segmentAt R e),
        ∃ q : ℕ, physicalQueueAt? rate R b W P
          (ReferenceCollectionSegmentExtraction.segmentAt R e) site = some q ∧
          (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)}

private theorem replayPrefixOverflow_mem_precallOverflow (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : ReferenceFirstCollectionCurrentRetainedGate.pastCells?
      rate rewards C_star C_h t z = some L)
    (n : ℕ) (hn : n ≤ L.length) (a : Fin p.K)
    (hcross :
      ((UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L n a).2 : ℝ) /
          (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCollectionPrecallOverflowBound.precallOverflow
      rate rewards C_star C_h := by
  classical
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have hcrossQ : UnstoppedRecordedQueueComparison.replay_crosses_overflow
      Q L n := by
    apply (UnstoppedRecordedQueueComparison.replay_crosses_overflow_iff_normalized
      Q L n).2
    refine ⟨a, ?_⟩
    simpa only [Q, ReferenceFirstLaunchNumericalCell.queueParameters] using hcross
  have hpositive : 0 < n := by
    by_contra hnot
    have hzero : n = 0 := Nat.eq_zero_of_not_pos hnot
    have hcrossZero := hcross
    simp [UnstoppedRecordedQueueComparison.unstoppedReplay, QueueReplay.replay, hzero]
      at hcrossZero
    have hpositiveThreshold :
        0 < (rate.eta.val)⁻¹ * (32 : ℝ)⁻¹ :=
      mul_pos (inv_pos.mpr rate.eta.property) (inv_pos.mpr (by norm_num))
    exact (not_lt_of_ge (le_of_lt hpositiveThreshold)) hcrossZero
  have hcrossExists : ∃ m, 1 ≤ m ∧ m ≤ L.length ∧
      UnstoppedRecordedQueueComparison.replay_crosses_overflow Q L m :=
    ⟨n, hpositive, hn, hcrossQ⟩
  have hfirst : UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L ≤ L.length := by
    dsimp [UnstoppedRecordedQueueComparison.firstOverflowPrefix]
    rw [dite_eq_left hcrossExists]
    exact le_trans (Nat.find_min' hcrossExists ⟨hpositive, hn, hcrossQ⟩) hn
  have hrun : (RecordedQueueRun.run Q L).overflow = true := by
    have hprefix :=
      UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        Q L L.length (by rfl)
    have h := hprefix.mpr hfirst
    simpa only [List.take_length] using h
  have hterminal :
      ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
        rate rewards C_star C_h p.T z = some L := by
    rw [ReferenceFirstCollectionPrecallOverflowBound.precallCells_terminal_eq_pastCells_on_firstCell
      rate rewards C_star C_h u t z hz.1, hL]
  exact ⟨p.T, le_rfl, L, hterminal, hrun⟩

private theorem replayOverflow_mem_precallOverflow (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : ReferenceFirstCollectionCurrentRetainedGate.pastCells?
      rate rewards C_star C_h t z = some L) (a : Fin p.K)
    (hcross : ((UnstoppedRecordedQueueComparison.unstoppedReplay
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2 : ℝ) /
        (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCollectionPrecallOverflowBound.precallOverflow
      rate rewards C_star C_h :=
  replayPrefixOverflow_mem_precallOverflow rate rewards C_star C_h u t z hz L hL
    L.length le_rfl a hcross

private theorem replay_arrivals
    {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p} (a : Fin p.K)
    (L : List (RecordedQueueRun.RoundInput p.K)) (initial : ℕ × ℕ) :
    QueueReplay.replay (4 * rate.n) initial
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a L) =
      QueueReplay.replay (4 * rate.n) initial
        (L.map fun c => UnstoppedRecordedQueueComparison.unstoppedRecord
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) := by
  induction L generalizing initial with
  | nil => rfl
  | cons c L ih =>
      simp only [ReferenceFirstCollectionAllArmNumericalStream.arrivals,
        List.map_cons, QueueReplay.replay, List.foldl_cons]
      have he : QueueReplay.transition (4 * rate.n) initial
          (c.enabled, RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) =
        QueueReplay.transition (4 * rate.n) initial
          (UnstoppedRecordedQueueComparison.unstoppedRecord (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) := by
        cases hc : c.enabled <;>
          simp only [UnstoppedRecordedQueueComparison.unstoppedRecord, hc,
            Bool.false_eq_true, ite_false, ite_true, QueueReplay.transition]
      rw [he]
      exact ih _

private theorem replay_arrivals_eq_unstopped
    {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p} (a : Fin p.K)
    (L : List (RecordedQueueRun.RoundInput p.K)) :
    QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a L) =
      UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a := by
  simpa only [UnstoppedRecordedQueueComparison.unstoppedReplay,
    List.take_length, ReferenceFirstLaunchNumericalCell.queueParameters] using replay_arrivals (rate := rate) a L (0, 0)

private theorem stream_output_ledger_eq
    {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (count : ℕ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hk : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) source rewards C_star C_h hc count hs).records).length < count)

    (d f : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hc hs hk)
    (i : Fin d.stream.ell) (j : Fin f.stream.ell) (hij : i.val = j.val) :
    d.stream.payload = f.stream.payload ∧
      d.stream.ledgers i = f.stream.ledgers j ∧ d.stream.saved = f.stream.saved := by
  have hw : d.stream.window = f.stream.window :=
    d.stream.windowIsActual.trans f.stream.windowIsActual.symm
  obtain ⟨r, hr, _, hd, _⟩ := d.stream.output_properties i
  obtain ⟨q, hq, _, hf, _⟩ := f.stream.output_properties j
  have he : r = q := by
    rw [hw, hij, hq] at hr
    exact Option.some.inj hr.symm
  have hh := hd.symm.trans (he ▸ hf)
  exact ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj hh

/-- Compare actual output records before identifying either existential ledger. -/
private theorem stream_endpoint_eq
    {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (count : ℕ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceFirstCollectionReadyStream.startTime (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hk : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) source rewards C_star C_h hc count hs).records).length < count)

    (d f : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hc hs hk)
    (hfull : f.stream.ell = f.stream.window.length)
    :
    d.stream.ell = f.stream.ell ∧ d.record = f.record ∧
      d.stream.payload = f.stream.payload ∧ d.ledger = f.ledger ∧
      d.stream.saved = f.stream.saved := by
  have hw : d.stream.window = f.stream.window :=
    d.stream.windowIsActual.trans f.stream.windowIsActual.symm
  have hle : d.stream.ell ≤ f.stream.ell := by
    rw [hfull, ← hw]
    exact d.stream.withinWindow
  have hlen : d.stream.ell = f.stream.ell := by
    by_contra hne
    have hlt : d.stream.ell < f.stream.ell := by omega
    cases hd : d.outcome with
    | exhausted hp hex hservice hinc boundary =>
        rw [hw, ← hfull] at hex
        omega
    | empty e =>
        let j : Fin f.stream.ell := ⟨d.last.val, by
          have h := d.last.isLt
          omega⟩
        have hj : j.val + 1 < f.stream.ell := by
          have h := d.lastIsLast
          change d.last.val + 1 < f.stream.ell
          omega
        have hledger := (stream_output_ledger_eq source rewards C_star C_h count hc hs hk
          d f d.last j rfl).2.1
        have hp := f.allEarlierNonempty j hj
        rw [← hledger, ← d.ledgerIsLast, e.pendingEmpty] at hp
        exact Finset.not_nonempty_empty hp
  have hlast : d.last.val = f.last.val := by
    have hd := d.lastIsLast
    have hf := f.lastIsLast
    omega
  have hrecord : d.record = f.record := by
    have h := d.recordAt
    rw [hw, hlast, f.recordAt] at h
    exact Option.some.inj h.symm
  have hledger := stream_output_ledger_eq source rewards C_star C_h count hc hs hk
    d f d.last f.last hlast
  rw [← d.ledgerIsLast, ← f.ledgerIsLast] at hledger
  exact ⟨hlen, hrecord, hledger⟩


/-- The incoming cutoff is the original first-LIVE endpoint, a prefix of
    the same complete strict-past word. It is not bounded by the birth queue. -/
theorem firstCell_birth_input_cutoff_replay (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (birth : Record)
    (hbirth : (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? = some birth) :
    ∃ (L L0 : List (RecordedQueueRun.RoundInput p.K))
      (old : Payload) (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool)),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t z = some L ∧
      L0 <+: L ∧ birth.input.state.coordinator = .collection old ledger saved ∧
      ∀ a, (ledger.cutoffRegisters a).map CoordinatorCollectionLedger.CutoffRegister.queue =
        some (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L0.length a).2 := by
  classical
  obtain ⟨n, birth0, theta, hb, ht, har, hcall, hrows, hselected, hrewards,
      hearlier, htime, hc, hs, hrecords, hk, f, empty, hf, hu, hn,
      hlast, hnext, hcoord, hcut, hcursor, hpending, hknown, hservice, hinc, hdispatch⟩ :=
    ReferenceFirstCollectionCallStoredBounds.firstCell_stored_bounds
      rate rewards C_star C_h u t z hz.1
  let R := sourceRecords rate rewards C_star C_h z
  let s := ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let b := birthIndex rate rewards C_star C_h z
  have hbtime := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
    rate rewards C_star C_h u t z hz
  change s + b = t.val at hbtime
  change s + n = t.val at htime
  have hnb : n = b := by omega
  have hsame : birth0 = birth := by
    rw [hnb] at hb
    exact Option.some.inj (hb.symm.trans hbirth)
  subst birth0
  have hfull : f.stream.ell = f.stream.window.length := by
    have hw := f.stream.windowIsActual
    change f.stream.window = ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
        hc (p.T - s) hs).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
          hc (p.T - s) hs).records).length at hw
    change R = (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      z rewards C_star C_h hc (p.T - s) hs).records at hrecords
    rw [← hrecords] at hw
    rw [hw]
    change f.stream.ell = (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    change n = w + f.stream.ell at hn
    change n = w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length at hnb
    omega
  obtain ⟨hc0, hs0, hk0, g, head0, valid0, D0, L,
      hsu, hut, hu0, hgt, hgp, hglast, hhead0, hD0len, hD0zero, hD0read,
      hLjoin, hL, hLlen, hcoverage⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
      rate rewards C_star C_h u t z hz.1
  have hfg : f.stream.ell = g.stream.ell := by
    change u.val = s + w at hu
    change s + w + g.stream.ell = t.val at hgt
    change n = w + f.stream.ell at hn
    omega
  have hfullg : g.stream.ell = g.stream.window.length := by
    have hw : f.stream.window = g.stream.window :=
      f.stream.windowIsActual.trans g.stream.windowIsActual.symm
    rw [← hw, ← hfg]
    exact hfull
  obtain ⟨_, _, hfgpay, hfgledger, hfgsaved⟩ :=
    stream_endpoint_eq z rewards C_star C_h _ hc hs _ f g hfullg
  rw [hfgpay, hfgledger, hfgsaved] at hcoord
  obtain ⟨d, head, initializer, valid, DD, hhead, hpay, hinit, hchecked,
      hDlen, hDzero, hCells, hPrefix, hRecords, hEndpoint, hVpre, hBoundary⟩ :=
    ReferenceFirstCollectionNumericalStartReconstruction.actual_first_collection_numerical_next_start_reconstruction
      rate z rewards C_star C_h _ hc hs _
  obtain ⟨_, _, _, hdgledger, _⟩ :=
    stream_endpoint_eq z rewards C_star C_h _ hc hs _ d g hfullg
  have hnum := hEndpoint (by rw [hdgledger]; exact hgp)
  rw [hdgledger] at hnum
  let L0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z rewards C_star C_h hc (p.T - s) hs
  have hjoin : L = L0 ++ D0 := hLjoin
  refine ⟨L, L0, g.stream.payload, g.ledger, g.stream.saved, hL, ?_, hcoord, ?_⟩
  · rw [hjoin]
    exact List.prefix_append _ _
  · intro a
    rw [(hnum a).1]
    simp only [Option.map_some]
    apply congrArg some
    change (QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a L0)).2 = _
    rw [replay_arrivals_eq_unstopped]
    simp only [UnstoppedRecordedQueueComparison.unstoppedReplay, hjoin, List.take_left,
      List.take_length]

private theorem collection_input_register_copy (r : Record)
    (old : Payload) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : r.input.state.coordinator = .collection old ledger saved) (a : Fin p.K) :
    match r.output.preparation.coordinator with
    | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ output _ _ _ _) =>
        (ledger.currentRegisters a).map CoordinatorCollectionLedger.CurrentRegister.queue =
          some (output.reconstruction.registers.current a).queue ∧
        (ledger.cutoffRegisters a).map CoordinatorCollectionLedger.CutoffRegister.queue =
          some (output.reconstruction.registers.cutoff a).queue
    | _ => True := by
  classical
  have hcarried : match ReferenceActivePhysicalStep.dispatch r.input with
      | .collection _ l _ _ _ => l = ledger | _ => True := by
    unfold ReferenceActivePhysicalStep.dispatch
    simp only [hstate]
    by_cases hcut : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · simp only [dite_eq_left hcut, CoordinatorRoundDispatch.dispatch]
      rfl
    · simp only [dite_eq_right hcut]
  rw [← r.output.preparation.coordinator_eq] at hcarried
  cases hd : r.output.preparation.coordinator <;>
    simp only [hd] at hcarried ⊢
  rename_i payload carried clock cutoff outcome
  cases outcome <;> simp only
  rename_i core consistent started hstart instruction hi output hlocal clockData installed selection
  have hcurrent := output.reconstruction.registers.current_eq a
  have hcutoff := output.reconstruction.registers.cutoff_eq a
  change carried.currentRegisters a = some (output.reconstruction.registers.current a) at hcurrent
  change carried.cutoffRegisters a = some (output.reconstruction.registers.cutoff a) at hcutoff
  have hc0 := (congrArg (fun l : ReferenceActivePhysicalStep.Ledger rate =>
    l.currentRegisters a) hcarried).symm.trans hcurrent
  have hf0 := (congrArg (fun l : ReferenceActivePhysicalStep.Ledger rate =>
    l.cutoffRegisters a) hcarried).symm.trans hcutoff
  rw [hc0, hf0]
  exact ⟨rfl, rfl⟩

/-- Both reconstructed birth queue vectors are copies of the actual optional
incoming registers. The actual call supplies their availability. -/
theorem firstCell_birth_input_queues_eq_reconstruction (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (birth : Record)
    (hbirth : (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? =
      some birth) (P : Payload) (a : Fin p.K) :
    let R := sourceRecords rate rewards C_star C_h z
    let b := birthIndex rate rewards C_star C_h z
    let W := liveTail rate rewards C_star C_h z
    let read := physicalQueueAt? rate R b W P (segmentAt R (b + 1 + W.length))
    read (.birthInputCurrent a) = read (.birthReconstructionCurrent a) ∧
      read (.birthInputCutoff a) = read (.birthReconstructionCutoff a) := by
  obtain ⟨L, L0, old, ledger, saved, _, _, hstate, _⟩ :=
    firstCell_birth_input_cutoff_replay rate rewards C_star C_h u t z hz birth hbirth
  obtain ⟨Lc, c, actualBirth, _, _, _, _, _, _, _, hb, _, _, _, _, _, hseed, _⟩ :=
    ReferenceFirstCollectionCorrectedCurrentNumericalOutput.firstCell_current_output
      rate rewards C_star C_h u t z hz
  have heq : actualBirth = birth := Option.some.inj (hb.symm.trans hbirth)
  subst actualBirth
  have hcopy := collection_input_register_copy rate birth old ledger saved hstate a
  cases hd : birth.output.preparation.coordinator <;> simp only [hd] at hseed
  rename_i payload carried clock cutoff outcome
  cases outcome <;> simp only at hseed
  rename_i core consistent started hstart instruction hi output hlocal clockData installed selection
  simpa only [physicalQueueAt?, hbirth, Option.bind_some, hstate, hd] using hcopy

/-- An incoming cutoff crossing is charged at its original earlier prefix,
including when later collection service has drained it before birth. -/
theorem birthInputCutoffOverflow_mem_precallOverflow (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (birth : Record)
    (hbirth : (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? =
      some birth) (P : Payload) (a : Fin p.K) (q : ℕ)
    (hphysical : physicalQueueAt? rate (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z) (liveTail rate rewards C_star C_h z) P
      (segmentAt (sourceRecords rate rewards C_star C_h z)
        (birthIndex rate rewards C_star C_h z + 1 +
          (liveTail rate rewards C_star C_h z).length)) (.birthInputCutoff a) = some q)
    (hcross : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h := by
  obtain ⟨L, L0, old, ledger, saved, hL, hprefix, hstate, hqueue⟩ :=
    firstCell_birth_input_cutoff_replay rate rewards C_star C_h u t z hz birth hbirth
  have hread : (ledger.cutoffRegisters a).map CoordinatorCollectionLedger.CutoffRegister.queue =
      some q := by
    simpa only [physicalQueueAt?, hbirth, Option.bind_some, hstate] using hphysical
  have heq := Option.some.inj ((hqueue a).symm.trans hread)
  apply replayPrefixOverflow_mem_precallOverflow rate rewards C_star C_h u t z hz
    L hL L0.length hprefix.length_le a
  rw [heq]
  exact hcross

/-- The actual installed birth queue is the endpoint of the same retained
past-cell replay, so its crossing yields a positive first crossing in the
literal terminal pre-call prefix. -/
theorem birthInstalledPayloadOverflow_mem_precallOverflow (u t : Fin p.T)
    (z : X) (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (birth : Record)
    (hbirth : (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? =
      some birth)
    (P : Payload) (_hinstall : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (_hPsigma : P.sigma = t) (a : Fin p.K) (q : ℕ)
    (hphysical : physicalQueueAt? rate (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z) (liveTail rate rewards C_star C_h z)
      P (ReferenceCollectionSegmentExtraction.segmentAt
        (sourceRecords rate rewards C_star C_h z)
        (birthIndex rate rewards C_star C_h z + 1 +
          (liveTail rate rewards C_star C_h z).length))
      (.birthInstalledPayload a) = some q)
    (hcross : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCollectionPrecallOverflowBound.precallOverflow
      rate rewards C_star C_h := by
  obtain ⟨L, c, actualBirth, hL, hc, hprefix, hLlen, hb, hstart,
      hcenabled, hactualBirth, hactual, htime, hrows, hselected, hrewards,
      hseedFull⟩ :=
    ReferenceFirstCollectionCorrectedCurrentNumericalOutput.firstCell_current_output
      rate rewards C_star C_h u t z hz
  rcases hseedFull with ⟨hseed, _hnext⟩
  have hsambirth : actualBirth = birth := Option.some.inj (hactualBirth.symm.trans hbirth)
  subst actualBirth
  cases hcoord : birth.output.preparation.coordinator <;>
    simp only [hcoord] at hseed
  rename_i old ledger clock cutoff outcome
  cases outcome <;> simp only at hseed
  rename_i core consistent started startResult instruction inputInfo output localFrame
    clockData installed selection
  rcases hseed with ⟨_, _, _, _, _, _, _, _, hqueues, _⟩
  have hphysicalEq : some (installed.registers.payload.queues a) = some q := by
    simpa only [physicalQueueAt?, hbirth, hcoord, Option.bind_some] using hphysical
  have hphysical' : installed.registers.payload.queues a = q := Option.some.inj hphysicalEq
  have hqueueReplay :
      installed.registers.payload.queues a =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2 :=
    (hqueues a).2.2.2
  have hcrossReplay :
      ((UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2 : ℝ) /
          (rate.n : ℝ) > 1 / (32 * rate.eta.val) := by
    rw [← hqueueReplay, hphysical']
    exact hcross
  exact replayOverflow_mem_precallOverflow rate rewards C_star C_h u t z hz L hL a
    hcrossReplay

/-- The actual installed complement queue at the birth choice is the same
strict-past replay on every genuinely owned arm, so a crossing is charged to
the literal pre-call source prefix. -/
theorem birthComplementChoiceOverflow_mem_precallOverflow (u t : Fin p.T)
    (z : X) (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (birth : Record)
    (hbirth : (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? =
      some birth)
    (P : Payload) (_hinstall : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (_hPsigma : P.sigma = t) (a : Fin p.K) (q : ℕ)
    (hphysical : physicalQueueAt? rate (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z) (liveTail rate rewards C_star C_h z)
      P (ReferenceCollectionSegmentExtraction.segmentAt
        (sourceRecords rate rewards C_star C_h z)
        (birthIndex rate rewards C_star C_h z + 1 +
          (liveTail rate rewards C_star C_h z).length))
      (.birthComplementChoice a) = some q)
    (hcross : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCollectionPrecallOverflowBound.precallOverflow
      rate rewards C_star C_h := by
  obtain ⟨L, c, actualBirth, hL, hc, hprefix, hLlen, hcenabled,
      hactualBirth, hactual, htime, hrows, hselected, hrewards, hprepared⟩ :=
    ReferenceFirstCorrectedBirthComputedOverflowCover.firstCell_birth_computed_outside_projection
      rate rewards C_star C_h u t z hz
  have hsambirth : actualBirth = birth := Option.some.inj (hactualBirth.symm.trans hbirth)
  subst actualBirth
  cases hcoord : birth.output.preparation.coordinator <;>
    simp only [hcoord] at hprepared
  rename_i old ledger clock cutoff outcome
  cases outcome <;> simp only at hprepared
  rename_i core consistent started startResult instruction inputInfo output localFrame
    clockData installed selection
  rcases hprepared with ⟨hinstTime, hkind, hinstallLater, hpayload, hsigma,
      hvector, hrate, hco, hconfiguration, recording, serviced, hrun,
      hdiagRecording, hservice, hqueueReplay, hprecomputed, hcrossing, hreturns⟩
  have ha : a ∉ installed.registers.payload.slowSet.val := by
    by_contra hslow
    simp [physicalQueueAt?, hbirth, hcoord, hslow] at hphysical
  let j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet :=
    ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩
  have hphysicalEq : some (installed.ownedRegisters.queue j) = some q := by
    simpa [physicalQueueAt?, hbirth, hcoord, Option.bind_some, j, ha] using hphysical
  have hphysical' : installed.ownedRegisters.queue j = q := Option.some.inj hphysicalEq
  have hqueueReplay :
      installed.ownedRegisters.queue j =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2 :=
    congrArg Prod.snd (hvector j).1
  have hcrossReplay :
      ((UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2 : ℝ) /
          (rate.n : ℝ) > 1 / (32 * rate.eta.val) := by
    rw [← hqueueReplay, hphysical']
    exact hcross
  exact replayOverflow_mem_precallOverflow rate rewards C_star C_h u t z hz L hL a
    hcrossReplay

/-- The reconstructed current-register queue exposes the same value as the
initialQueue field and is therefore covered by the same positive first
crossing in the original pre-call prefix. -/
theorem birthReconstructionCurrentOverflow_mem_precallOverflow (u t : Fin p.T)
    (z : X) (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (birth : Record)
    (hbirth : (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? =
      some birth)
    (P : Payload) (_hinstall : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P)
    (_hPsigma : P.sigma = t) (a : Fin p.K) (q : ℕ)
    (hphysical : physicalQueueAt? rate (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z) (liveTail rate rewards C_star C_h z)
      P (ReferenceCollectionSegmentExtraction.segmentAt
        (sourceRecords rate rewards C_star C_h z)
        (birthIndex rate rewards C_star C_h z + 1 +
          (liveTail rate rewards C_star C_h z).length))
      (.birthReconstructionCurrent a) = some q)
    (hcross : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ ReferenceFirstCollectionPrecallOverflowBound.precallOverflow
      rate rewards C_star C_h := by
  obtain ⟨L, c, actualBirth, hL, hc, hprefix, hLlen, hb, hstart,
      hcenabled, hactualBirth, hactual, htime, hrows, hselected, hrewards,
      hseedFull⟩ :=
    ReferenceFirstCollectionCorrectedCurrentNumericalOutput.firstCell_current_output
      rate rewards C_star C_h u t z hz
  rcases hseedFull with ⟨hseed, _hnext⟩
  have hsambirth : actualBirth = birth := Option.some.inj (hactualBirth.symm.trans hbirth)
  subst actualBirth
  cases hcoord : birth.output.preparation.coordinator <;>
    simp only [hcoord] at hseed
  rename_i old ledger clock cutoff outcome
  cases outcome <;> simp only at hseed
  rename_i core consistent started startResult instruction inputInfo output localFrame
    clockData installed selection
  rcases hseed with ⟨_, _, _, _, _, _, _, _, hqueues, _⟩
  have hphysicalEq : some ((output.reconstruction.registers.current a).queue) = some q := by
    simpa only [physicalQueueAt?, hbirth, hcoord, Option.bind_some] using hphysical
  have hphysical' : (output.reconstruction.registers.current a).queue = q :=
    Option.some.inj hphysicalEq
  have hqueueReplay :
      (output.reconstruction.registers.current a).queue =
        (UnstoppedRecordedQueueComparison.unstoppedReplay
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2 := by
    simpa only [AssignmentScoreReconstruction.initialQueue] using (hqueues a).2.1
  have hcrossReplay :
      ((UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L L.length a).2 : ℝ) /
          (rate.n : ℝ) > 1 / (32 * rate.eta.val) := by
    rw [← hqueueReplay, hphysical']
    exact hcross
  exact replayOverflow_mem_precallOverflow rate rewards C_star C_h u t z hz L hL a
    hcrossReplay

private theorem continuing_input (r : Record)
    (ht : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = true) :
    ∃ (rv : Registers) (qv : Owned rv) (base : Fin (p.m - 1) → ℕ),
      r.input.state.coordinator = .live rv qv base := by
  classical
  have htest := ht
  unfold ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen at htest
  rw [r.output.preparation.coordinator_eq] at htest
  cases hs : r.input.state.coordinator with
  | live rv qv base => exact ⟨rv, qv, base, rfl⟩
  | first =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs,
        CoordinatorRoundDispatch.dispatch] at htest
      change false = true at htest
      cases htest
  | dagger =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs] at htest
      cases htest
  | collection old ledger saved =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs] at htest
      split_ifs at htest
      · simp only [CoordinatorRoundDispatch.dispatch] at htest
        change false = true at htest
        cases htest

private theorem livePostChoice_residual_eq_output
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (rv : Registers) (qv : Owned rv) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) (a : Fin p.K)
    (hf : (ReferenceActivePhysicalStep.livePostChoice prepared rv qv base started).failure = none) :
    ((ReferenceActivePhysicalStep.livePostChoice prepared rv qv base started).recording).bind
        (fun o => reachedCoordinatorResidual? rate rv qv o a) =
      match (ReferenceActivePhysicalStep.livePostChoice prepared rv qv base started).configuration with
      | .live rout qout _ =>
          if ha : a ∉ rout.payload.slowSet.val then
            some (qout.queue ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩) else none
      | _ => none := by
  classical
  unfold ReferenceActivePhysicalStep.livePostChoice at hf ⊢
  cases hr : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared rv started) with
  | none => simp only [hr, ReferenceActivePhysicalStep.coordinatorFailure, reduceCtorEq] at hf
  | some o =>
      simp only [hr] at hf ⊢
      cases hs : CoordinatorLiveServiceFinish.servicePass rv qv o with
      | error reason =>
          simp only [hs, ReferenceActivePhysicalStep.coordinatorFailure, reduceCtorEq] at hf
      | ok serviced =>
          simp only [hs] at hf ⊢
          cases hc : CoordinatorLocalArmChoice.confirmationUpdate rv.payload started.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none =>
              simp only [hc, ReferenceActivePhysicalStep.coordinatorFailure, reduceCtorEq] at hf
          | some pending =>
              simp only [hc] at hf ⊢
              cases he : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock pending x.row with
              | error reason =>
                  simp only [he, ReferenceActivePhysicalStep.coordinatorFailure, reduceCtorEq] at hf
              | ok finished =>
                  simp only [Option.bind_some]
                  by_cases ha : a ∉ rv.payload.slowSet.val
                  · rw [reachedCoordinatorResidual?_eq_serviced rate rv qv o serviced hs a ha]
                    simp only [ha, not_false_eq_true, dite_true]
                  · simp only [reachedCoordinatorResidual?, ha, dite_false]

/-- The actual continuing call preserves its INPUT queue at CHOICE and
identifies the reached pre-output residual with the same actual OUTPUT.
All recorder and service rejection branches remain in the evaluator; the
complete-source phase producer excludes them inside this proof. -/
theorem firstCell_live_sites (u t : Fin p.T) (z : X)
    (_hz : z ∈ correctedCell rate rewards C_star C_h u t) (P : Payload)
    (i : Fin (liveTail rate rewards C_star C_h z).length) (a : Fin p.K) :
    let R := sourceRecords rate rewards C_star C_h z
    let b := birthIndex rate rewards C_star C_h z
    let W := liveTail rate rewards C_star C_h z
    let read := physicalQueueAt? rate R b W P (segmentAt R (b + 1 + W.length))
    read (.liveChoice i a) = read (.liveInput i a) ∧
      read (.liveServiceResidual i a) = read (.liveOutput i a) := by
  classical
  let R := sourceRecords rate rewards C_star C_h z
  let b := birthIndex rate rewards C_star C_h z
  let W := liveTail rate rewards C_star C_h z
  let r := W[i]
  have hget : R[b + 1 + i.val]? = some r :=
    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R b i
  obtain ⟨hk, hrecord⟩ := List.getElem?_eq_some_iff.mp hget
  have ht : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = true :=
    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_mem R b r (List.getElem_mem i.isLt)
  obtain ⟨rv, qv, base, hstate⟩ := continuing_input rate r ht
  have hprepared : r.output.preparation.coordinator = .live rv qv base
      (CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput r.input rv qv base)) := by
    rw [r.output.preparation.coordinator_eq]
    simp only [ReferenceActivePhysicalStep.dispatch, hstate, CoordinatorRoundDispatch.dispatch]
    rfl
  have hphase := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
    rate rewards C_star C_h z).1 ⟨b + 1 + i.val, hk⟩
  change R[b + 1 + i.val] = r at hrecord
  change (R[b + 1 + i.val]).input.state.coordinator ≠ .dagger ∧
    (R[b + 1 + i.val]).output.preparation.coordinator.selection ≠ none ∧
    (R[b + 1 + i.val]).output.coordinator.failure = none ∧
    (R[b + 1 + i.val]).output.next.coordinator ≠ .first ∧
    (R[b + 1 + i.val]).output.next.coordinator ≠ .dagger at hphase
  rw [hrecord] at hphase
  have hsel := hphase.2.1
  have hfailure := hphase.2.2.1
  cases ho : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput r.input rv qv base) with
  | continuingChosen dispatched hstart continuation selection =>
      rw [ho] at hprepared
      have hco : r.output.coordinator = ReferenceActivePhysicalStep.livePostChoice
          r.output.preparation (ReferenceActivePhysicalStep.liveRegistersAt rv r.input.time)
          (ReferenceActivePhysicalStep.liveOwnedAt rv qv r.input.time) base dispatched.startResult := by
        have he : r.output.coordinator = r.output.preparation.observeCoordinator := by
          rw [r.output_eq]; rfl
        rw [he]
        unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
        rw [dite_eq_right hsel, hprepared]
      have hnext : r.output.next.coordinator = r.output.coordinator.configuration := by
        rw [r.output_eq]; rfl
      have hres := livePostChoice_residual_eq_output rate r.output.preparation
        (ReferenceActivePhysicalStep.liveRegistersAt rv r.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt rv qv r.input.time) base dispatched.startResult a
        (hco ▸ hfailure)
      dsimp only [r, W] at hprepared hstate hco hnext hres
      constructor
      · simp only [physicalQueueAt?, Option.bind_some, hprepared, hstate,
          ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.liveOwnedAt]
        rfl
      · simp only [physicalQueueAt?, Option.bind_some, hprepared, hnext, hco]
        cases hconfig : (ReferenceActivePhysicalStep.livePostChoice r.output.preparation
          (ReferenceActivePhysicalStep.liveRegistersAt rv r.input.time)
          (ReferenceActivePhysicalStep.liveOwnedAt rv qv r.input.time) base dispatched.startResult).configuration <;>
          dsimp only [r, W] at hconfig <;> simpa only [hconfig] using hres
  | cutoffChosen | clockFailure | initializerFailure | localFailure =>
      rw [ho] at hprepared
      simp only [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hprepared,
        Bool.false_eq_true] at ht

/-- A thresholded known-site constructor is covered by the already accepted
seven-site source proof.  No known-site partition is re-derived here. -/
theorem knownSite_threshold_subset_allArmCollectionOverflowEvent
    (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (seg : Segment)
    (hseg : segmentAt (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length) = some seg)
    (a : Fin p.K) (field : QueueRegisterField) (q : ℕ)
    (site : KnownQueueSourceSite rate seg a field q)
    (hcross : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ allArmCollectionOverflowEvent rate rewards C_star C_h := by
  exact firstCollectionKnownQueueOverflowEvent_subset_allArmCollectionOverflowEvent
    rate rewards C_star C_h u t ⟨hz, seg, hseg, a, field, q, site, hcross⟩

/-- Birth service crossings use the accepted computed-queue producer and then
extend its unchanged first-collection overflow prefix through the actual
collection endpoint. -/
theorem birthComputedOutsideOverflowEvent_subset_allArmCollectionOverflowEvent
    (u t : Fin p.T) :
    ReferenceFirstCorrectedBirthComputedOverflowCover.birthComputedOutsideOverflowEvent
        rate rewards C_star C_h u t ⊆
      ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent
        rate rewards C_star C_h := by
  intro z hz
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp
    (ReferenceFirstCorrectedBirthComputedOverflowCover.birthComputedOutsideOverflowEvent_subset_allArmOverflowEvent
      rate rewards C_star C_h u t hz)
  have hcollection :=
    ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.oldOverflowEvent_subset_collectionOverflowEvent
      rate rewards C_star C_h u t a ha
  change z ∈ ⋃ a : Fin p.K, ⋃ u : Fin p.T, ⋃ t : Fin p.T,
    ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionOverflowEvent
      rate rewards C_star C_h u t a
  exact Set.mem_iUnion.mpr ⟨a,
    Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨t, hcollection⟩⟩⟩

private theorem storedOutsideOverflow_mem_collection (u t : Fin p.T) (z : X)
    (h : z ∈ ReferenceFirstCollectionCorrectedStoredOutsideOverflowCover.storedOutsideOverflowEvent
      rate rewards C_star C_h u t) :
    z ∈ allArmCollectionOverflowEvent rate rewards C_star C_h := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp
    (ReferenceFirstCollectionCorrectedStoredOutsideOverflowCover.storedOutsideOverflowEvent_subset_arm_union
      rate rewards C_star C_h u t h)
  exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨t,
    ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.oldOverflowEvent_subset_collectionOverflowEvent
      rate rewards C_star C_h u t a ha⟩⟩⟩

private theorem liveOutputOverflow_mem_collection (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) (P : Payload)
    (i : Fin (liveTail rate rewards C_star C_h z).length) (a : Fin p.K) (q : ℕ)
    (hphysical : physicalQueueAt? rate (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z) (liveTail rate rewards C_star C_h z) P
      (segmentAt (sourceRecords rate rewards C_star C_h z)
        (birthIndex rate rewards C_star C_h z + 1 +
          (liveTail rate rewards C_star C_h z).length)) (.liveOutput i a) = some q)
    (hcross : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ allArmCollectionOverflowEvent rate rewards C_star C_h := by
  let R := sourceRecords rate rewards C_star C_h z
  let b := birthIndex rate rewards C_star C_h z
  let W := liveTail rate rewards C_star C_h z
  have hget : R[b + 1 + i.val]? = some W[i] :=
    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R b i
  apply storedOutsideOverflow_mem_collection rate rewards C_star C_h u t z
  refine ⟨hz, b + 1 + i.val, W[i], a, q, hget, by omega, ?_, ?_, hcross⟩
  · have hi := i.isLt
    change i.val < W.length at hi
    change b + 1 + i.val < b + 1 + W.length + _
    omega
  · cases hout : W[i].output.next.coordinator <;>
      simp only [physicalQueueAt?, Option.bind_some, ← show W[i] =
        (liveTail rate rewards C_star C_h z)[i] from rfl, hout, reduceCtorEq] at hphysical
    simpa only [ReferenceFirstCollectionCorrectedStoredOutsideOverflowCover.storedOutsideQueue, hout]
      using hphysical

private theorem inputOverflow_mem_collection (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) (k : ℕ) (r : Record)
    (hget : (sourceRecords rate rewards C_star C_h z)[k]? = some r)
    (hmin : birthIndex rate rewards C_star C_h z < k)
    (hmax : k ≤ birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length)
    (a : Fin p.K) (q : ℕ)
    (hqueue : (match r.input.state.coordinator with
      | .live rv qv _ => if ha : a ∉ rv.payload.slowSet.val then
          some (qv.queue ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩) else none
      | _ => none) = some q)
    (hcross : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ allArmCollectionOverflowEvent rate rewards C_star C_h := by
  let R := sourceRecords rate rewards C_star C_h z
  obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp hget
  change k < R.length at hk
  change R[k] = r at heq
  have hprev : k - 1 < R.length := by omega
  let prev := R[k - 1]
  have hprevious : R[k - 1]? = some prev := List.getElem?_eq_getElem hprev
  have hindex : k - 1 + 1 = k := by omega
  have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
    (rate := rate) rewards C_star C_h z (k - 1)
    (by change k - 1 + 1 < R.length; omega)
  change (R[k - 1 + 1]).input.state = prev.output.next at hadj
  have hadj' : r.input.state = prev.output.next := by simpa only [hindex, heq] using hadj
  have hco := congrArg ReferenceActivePhysicalStep.State.coordinator hadj'
  rw [hco] at hqueue
  apply storedOutsideOverflow_mem_collection rate rewards C_star C_h u t z
  refine ⟨hz, k - 1, prev, a, q, hprevious, by omega, by omega, ?_, hcross⟩
  cases hout : prev.output.next.coordinator <;> simp only [hout, reduceCtorEq] at hqueue
  simpa only [ReferenceFirstCollectionCorrectedStoredOutsideOverflowCover.storedOutsideQueue, hout]
    using hqueue

private theorem cutoffInputOverflow_mem_collection (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) (P : Payload) (seg : Segment)
    (hseg : segmentAt (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length) = some seg)
    (a : Fin p.K) (q : ℕ)
    (hphysical : physicalQueueAt? rate (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z) (liveTail rate rewards C_star C_h z) P
      (segmentAt (sourceRecords rate rewards C_star C_h z)
        (birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length))
      (.cutoffInput seg a hseg) = some q)
    (hcross : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ allArmCollectionOverflowEvent rate rewards C_star C_h := by
  let R := sourceRecords rate rewards C_star C_h z
  let e := birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length
  have he : e < R.length := by
    by_contra hn
    have hd : R.drop e = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hb := (segmentAt_branch R e seg hseg).1
    rw [hd] at hb
    contradiction
  obtain ⟨L, B, c, birth, payload, seg0, D, _, _, _, _, _, _, _, _, hseg0, hentry, _⟩ :=
    ReferenceFirstCorrectedCollectionKnownQueuePrefixReplay.firstCell_actual_segment_prefix_words
      rate rewards C_star C_h u t z hz he
  have heq : seg0 = seg := Option.some.inj (hseg0.symm.trans hseg)
  subst seg0
  have hget : R[e]? = some seg.entry := by
    rw [hentry]
    exact List.getElem?_eq_getElem he
  exact inputOverflow_mem_collection rate rewards C_star C_h u t z hz e seg.entry hget
    (by dsimp only [e]; omega) le_rfl a q hphysical hcross

private theorem birthServiceResidualOverflow_mem_collection (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (birth : Record) (hbirth : (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? = some birth) (P : Payload) (a : Fin p.K) (q : ℕ)
    (hphysical : physicalQueueAt? rate (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z) (liveTail rate rewards C_star C_h z) P
      (segmentAt (sourceRecords rate rewards C_star C_h z)
        (birthIndex rate rewards C_star C_h z + 1 +
          (liveTail rate rewards C_star C_h z).length)) (.birthServiceResidual a) = some q)
    (hcross : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    z ∈ allArmCollectionOverflowEvent rate rewards C_star C_h := by
  obtain ⟨L, c, birth0, _, _, _, _, _, hb, har, _, _, _, _, hprepared⟩ :=
    ReferenceFirstCorrectedBirthComputedOverflowCover.firstCell_birth_computed_outside_projection
      rate rewards C_star C_h u t z hz
  have heq : birth0 = birth := Option.some.inj (hb.symm.trans hbirth)
  subst birth0
  cases hd : birth.output.preparation.coordinator <;> simp only [hd] at hprepared
  rename_i old ledger clock cutoff outcome
  cases outcome <;> simp only at hprepared
  rename_i core consistent started hstart instruction hi output hlocal clockData installed selection
  obtain ⟨_, _, _, _, _, _, _, _, _, o, serviced, _, hrecording, hs, _, hcomputed, _⟩ := hprepared
  have ha : a ∉ installed.registers.payload.slowSet.val := by
    by_contra hslow
    simp only [physicalQueueAt?, hbirth, Option.bind_some, hd, hrecording,
      reachedCoordinatorResidual?, hslow, not_true_eq_false, dite_false,
      reduceCtorEq] at hphysical
  have hraw := reachedCoordinatorResidual?_eq_serviced rate installed.registers
    installed.ownedRegisters o serviced hs a ha
  have hq : some (serviced.queue ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩) = some q := by
    simpa only [physicalQueueAt?, hbirth, Option.bind_some, hd, hrecording, hraw] using hphysical
  apply birthComputedOutsideOverflowEvent_subset_allArmCollectionOverflowEvent
    rate rewards C_star C_h u t
  exact ⟨hz, birth, hbirth, har, a, q, (hcomputed a ha).trans hq, hcross⟩

private theorem continuing_windows_eq (z : X) :
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z
      (birthIndex rate rewards C_star C_h z + 1) =
    liveTail rate rewards C_star C_h z := by
  simp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail,
    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords]
  have htest :
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
          (p := p) (rate := rate) =
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
    funext r
    unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
      ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
    cases r.output.preparation.coordinator with
    | live rv qv base chosen => cases chosen <;> rfl
    | first _ | collection _ _ _ _ _ | invalidCollectionCutoff | dagger => rfl
  rw [htest]

private theorem firstCell_excluded_input (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) (seg : Segment)
    (hseg : segmentAt (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length) = some seg)
    (r : Record) (hhead : seg.remaining.head? = some r) :
    ∃ saved, r.input.state.coordinator = .collection seg.context.payload seg.final saved ∧
      ReferenceCollectionPhaseHistory.laterChosen r.input = true ∧
      ∀ c : Choice rate, choice r.input ≠ some c := by
  let R := sourceRecords rate rewards C_star C_h z
  let s := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart rate rewards C_star C_h z
  let b := birthIndex rate rewards C_star C_h z
  let e := b + 1 + (liveTail rate rewards C_star C_h z).length
  obtain ⟨A, D, _, hD, _, _, _, _, _, _, hremaining⟩ :=
    ReferenceFirstCorrectedCollectionKnownQueueSource.firstCell_collection_known_queue_source
      rate rewards C_star C_h u t z hz seg hseg
  obtain ⟨hindex, _, _, _⟩ := hremaining r hhead
  have hk : e + D.length < R.length := (List.getElem?_eq_some_iff.mp hindex).1
  have hbtime := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
    rate rewards C_star C_h u t z hz
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  change s + b = t.val at hbtime
  change R.length = p.T - s at hlen
  have hq : t.val + 1 < p.T := by dsimp only [e] at hk; omega
  have hactual := ReferenceFirstCorrectedCollectionBoundaryExclusion.firstCell_actual_collection_boundary_exclusion
    rate rewards C_star C_h u t z hz hq
  dsimp only at hactual
  rw [continuing_windows_eq rate rewards C_star C_h z] at hactual
  change e ≤ R.length ∧ (e = R.length ∨ ∃ seg0,
    ReferenceFirstCorrectedCollectionBoundaryExclusion.firstCellCollectionBoundaryExclusionResult
      rate rewards C_star C_h z e seg0) at hactual
  rcases hactual.2 with hterminal | ⟨seg0, hresult⟩
  · omega
  · have heq : seg0 = seg := Option.some.inj (hresult.1.symm.trans hseg)
    subst seg0
    obtain ⟨_, _, _, saved, _, _, hboundary⟩ := hresult
    rcases hboundary with hterminal | ⟨hv, _, hinput, _, hdrop, hlater, _, _, hnochoice⟩
    · change e + seg.records.length = R.length at hterminal
      omega
    · change R.drop (e + seg.records.length) = seg.remaining at hdrop
      have hr : R[e + seg.records.length] = r := by
        have hh : R[e + seg.records.length]? = some r := by
          simpa only [← hdrop, List.head?_drop] using hhead
        exact (List.getElem?_eq_some_iff.mp hh).2
      exact ⟨saved, hr ▸ hinput, hr ▸ hlater, hr ▸ hnochoice⟩

/-- At the first excluded INPUT, all three newly copied CHOICE seeds are
copies of the same old final current register. No new service is observed. -/
private theorem excluded_seed_site (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) (P : Payload) (seg : Segment)
    (hseg : segmentAt (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length) = some seg) (a : Fin p.K) :
    let R := sourceRecords rate rewards C_star C_h z
    let b := birthIndex rate rewards C_star C_h z
    let W := liveTail rate rewards C_star C_h z
    let read := physicalQueueAt? rate R b W P (segmentAt R (b + 1 + W.length))
    ∀ q, (read (.excludedInstalledPayload seg a hseg) = some q ∨
      read (.excludedInitialQueue seg a hseg) = some q ∨
      read (.excludedComplementChoice seg a hseg) = some q) →
      KnownQueueSourceSite rate seg a .current q := by
  classical
  dsimp only
  intro q hphysical
  cases hhead : seg.remaining.head? with
  | none =>
      simp only [physicalQueueAt?, hhead, Option.bind_none, reduceCtorEq, or_self] at hphysical
  | some r =>
      obtain ⟨saved, hstate, _hlater, _hnochoice⟩ :=
        firstCell_excluded_input rate rewards C_star C_h u t z hz seg hseg r hhead
      have hcopy := collection_input_register_copy rate r seg.context.payload seg.final saved hstate a
      have hprov := ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance r.input
      rw [← r.output.preparation.coordinator_eq] at hprov
      cases hd : r.output.preparation.coordinator <;>
        simp only [physicalQueueAt?, hhead, Option.bind_some, hd, reduceCtorEq, or_self] at hphysical
      rename_i old ledger clock cutoff outcome
      cases outcome <;> simp only [reduceCtorEq, or_self] at hphysical
      rename_i core consistent started hstart instruction hi output hlocal clockData installed selection
      simp only [hd] at hcopy hprov
      obtain ⟨hinstall, hpay, _⟩ := hprov
      have hqueue : ReferenceFirstCorrectedCollectionKnownQueueSource.knownSiteQueue?
          seg.final a .current = some q := by
        rw [ReferenceFirstCorrectedCollectionKnownQueueSource.knownSiteQueue?_current, hcopy.1]
        rcases hphysical with hp | hi | hc
        · rw [hpay, output.payload_queues] at hp
          exact hp
        · exact hi
        · by_cases ha : a ∉ installed.registers.payload.slowSet.val
          · simp only [ha, not_false_eq_true, dite_true] at hc
            have howned : installed.ownedRegisters.queue
                ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩ =
                (output.reconstruction.registers.current a).queue := by
              subst installed
              exact CoordinatorAssignmentRegisterInstall.later_reconstruction_queue_check output clockData _
            rw [howned] at hc
            exact hc
          · simp only [ha, dite_false, reduceCtorEq] at hc
      exact .firstExcludedInput r hhead saved hstate hqueue

/-- Exhaustive coordinator-only partition on the original corrected cell.
Every operation is charged to the same pre-call or collection event. -/
theorem coordinatorQueueOverflowEvent_subset_precall_union_collection (u t : Fin p.T) :
    coordinatorQueueOverflowEvent rate rewards C_star C_h u t ⊆
      ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h ∪
        allArmCollectionOverflowEvent rate rewards C_star C_h := by
  intro z h
  rcases h with ⟨hz, birth, hbirth, P, hinstall, hPsigma, site, q, hphysical, hcross⟩
  cases site with
  | birthInputCurrent a =>
      have hcopy := (firstCell_birth_input_queues_eq_reconstruction
        rate rewards C_star C_h u t z hz birth hbirth P a).1
      exact Or.inl (birthReconstructionCurrentOverflow_mem_precallOverflow
        rate rewards C_star C_h u t z hz birth hbirth P hinstall hPsigma a q
          (hcopy.symm.trans hphysical) hcross)
  | birthInputCutoff a =>
      exact Or.inl (birthInputCutoffOverflow_mem_precallOverflow
        rate rewards C_star C_h u t z hz birth hbirth P a q hphysical hcross)
  | birthReconstructionCurrent a =>
      exact Or.inl (birthReconstructionCurrentOverflow_mem_precallOverflow
        rate rewards C_star C_h u t z hz birth hbirth P hinstall hPsigma a q hphysical hcross)
  | birthReconstructionCutoff a =>
      have hcopy := (firstCell_birth_input_queues_eq_reconstruction
        rate rewards C_star C_h u t z hz birth hbirth P a).2
      exact Or.inl (birthInputCutoffOverflow_mem_precallOverflow
        rate rewards C_star C_h u t z hz birth hbirth P a q (hcopy.trans hphysical) hcross)
  | birthInstalledPayload a =>
      exact Or.inl (birthInstalledPayloadOverflow_mem_precallOverflow
        rate rewards C_star C_h u t z hz birth hbirth P hinstall hPsigma a q hphysical hcross)
  | birthInitialQueue a =>
      exact Or.inl (birthReconstructionCurrentOverflow_mem_precallOverflow
        rate rewards C_star C_h u t z hz birth hbirth P hinstall hPsigma a q
          (by simpa only [physicalQueueAt?, AssignmentScoreReconstruction.initialQueue] using hphysical)
          hcross)
  | birthComplementChoice a =>
      exact Or.inl (birthComplementChoiceOverflow_mem_precallOverflow
        rate rewards C_star C_h u t z hz birth hbirth P hinstall hPsigma a q hphysical hcross)
  | birthServiceResidual a =>
      exact Or.inr (birthServiceResidualOverflow_mem_collection
        rate rewards C_star C_h u t z hz birth hbirth P a q hphysical hcross)
  | birthOutput a =>
      apply Or.inr
      apply storedOutsideOverflow_mem_collection rate rewards C_star C_h u t z
      refine ⟨hz, _, birth, a, q, hbirth, le_rfl, by omega, ?_, hcross⟩
      cases hout : birth.output.next.coordinator <;>
        simp only [physicalQueueAt?, hbirth, Option.bind_some, hout, reduceCtorEq] at hphysical
      simpa only [ReferenceFirstCollectionCorrectedStoredOutsideOverflowCover.storedOutsideQueue, hout]
        using hphysical
  | liveInput i a =>
      exact Or.inr (inputOverflow_mem_collection rate rewards C_star C_h u t z hz _ _
        (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get _ _ i)
        (by omega) (by have hi := i.isLt; omega) a q hphysical hcross)
  | liveChoice i a =>
      have hcopy := (firstCell_live_sites rate rewards C_star C_h u t z hz P i a).1
      exact Or.inr (inputOverflow_mem_collection rate rewards C_star C_h u t z hz _ _
        (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get _ _ i)
        (by omega) (by have hi := i.isLt; omega) a q
        (hcopy.symm.trans hphysical) hcross)
  | liveServiceResidual i a =>
      have hcopy := (firstCell_live_sites rate rewards C_star C_h u t z hz P i a).2
      exact Or.inr (liveOutputOverflow_mem_collection
        rate rewards C_star C_h u t z hz P i a q (hcopy.symm.trans hphysical) hcross)
  | liveOutput i a =>
      exact Or.inr (liveOutputOverflow_mem_collection
        rate rewards C_star C_h u t z hz P i a q hphysical hcross)
  | cutoffInput seg a hseg =>
      exact Or.inr (cutoffInputOverflow_mem_collection
        rate rewards C_star C_h u t z hz P seg hseg a q hphysical hcross)
  | knownQueue a field q0 hseg sourceSite =>
      change some q0 = some q at hphysical
      cases Option.some.inj hphysical
      exact Or.inr (knownSite_threshold_subset_allArmCollectionOverflowEvent
        rate rewards C_star C_h u t z hz _ hseg a field _ sourceSite hcross)
  | excludedInstalledPayload seg a hseg =>
      exact Or.inr (knownSite_threshold_subset_allArmCollectionOverflowEvent
        rate rewards C_star C_h u t z hz seg hseg a .current q
          (excluded_seed_site rate rewards C_star C_h u t z hz P seg hseg a q
            (Or.inl hphysical)) hcross)
  | excludedInitialQueue seg a hseg =>
      exact Or.inr (knownSite_threshold_subset_allArmCollectionOverflowEvent
        rate rewards C_star C_h u t z hz seg hseg a .current q
          (excluded_seed_site rate rewards C_star C_h u t z hz P seg hseg a q
            (Or.inr (Or.inl hphysical))) hcross)
  | excludedComplementChoice seg a hseg =>
      exact Or.inr (knownSite_threshold_subset_allArmCollectionOverflowEvent
        rate rewards C_star C_h u t z hz seg hseg a .current q
          (excluded_seed_site rate rewards C_star C_h u t z hz P seg hseg a q
            (Or.inr (Or.inr hphysical))) hcross)

/-- All corrected cells share these same two source events. -/
theorem allCoordinatorQueueOverflowEvent_subset_precall_union_collection :
    (⋃ u : Fin p.T, ⋃ t : Fin p.T, coordinatorQueueOverflowEvent rate rewards C_star C_h u t) ⊆
      ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h ∪
        allArmCollectionOverflowEvent rate rewards C_star C_h := by
  intro z h
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp h
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hu
  exact coordinatorQueueOverflowEvent_subset_precall_union_collection rate rewards C_star C_h u t ht

/-- One original-source probability budget for every coordinator site and
corrected cell. This is an outer-measure estimate of the literal event; it
makes no Borel measurability assertion. -/
theorem coordinatorQueueOverflowUnion_measure_le (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (⋃ u : Fin p.T, ⋃ t : Fin p.T, coordinatorQueueOverflowEvent rate rewards C_star C_h u t) ≤
      3 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-CanonicalRecordingRates.beta p rate.eta.val / (32 * rate.eta.val)) := by
  have hscale := ReferenceFirstCollectionPrecallOverflowBound.beta_mul_cap_eq_Lstab rate
  have hexp : Real.exp (-(CanonicalRecordingRates.L_stab p : ℝ)) =
      Real.exp (-CanonicalRecordingRates.beta p rate.eta.val / (32 * rate.eta.val)) := by
    rw [← hscale]
    congr 1
    ring
  have hpre := ReferenceFirstCollectionPrecallOverflowBound.precallOverflow_measureReal_le_exp
    rate rewards C_star C_h control0
  rw [hexp] at hpre
  have hcol := ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent_measure_le
    rate rewards C_star C_h control0
  calc
    _ ≤ (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h ∪
          allArmCollectionOverflowEvent rate rewards C_star C_h) :=
      MeasureTheory.measureReal_mono
        (allCoordinatorQueueOverflowEvent_subset_precall_union_collection rate rewards C_star C_h)
        (by finiteness)
    _ ≤ (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          (ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h) +
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          (allArmCollectionOverflowEvent rate rewards C_star C_h) :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ (p.K : ℝ) * ((p.T : ℝ) + 1) *
          Real.exp (-CanonicalRecordingRates.beta p rate.eta.val / (32 * rate.eta.val)) +
        2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
          Real.exp (-CanonicalRecordingRates.beta p rate.eta.val / (32 * rate.eta.val)) :=
      add_le_add hpre hcol
    _ = _ := by ring

end Bandits.Support.ReferenceFirstCorrectedCoordinatorQueueOverflowCover

end
