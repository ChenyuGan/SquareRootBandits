/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDownThresholdDetection

import Lean.Elab.Tactic.Omega

/-!
# Actual first-collection DOWN physical boundary

Transport the generated successful follower records to the indexed actual
first-collection window, retaining the actual cutoff payload and both adjacent
prefix states.

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`sources/zip4/manuscript/05_binary_transport.tex:27-55,100-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionDownPhysicalBoundary

variable {p : Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem physical_callbacks_of_record_eq
    (i : Fin (p.m - 1))
    (left right : ReferenceCollectionPhaseHistory.Record p rate)
    (hrecord : left = right)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (s w j n : ℕ) (hindex : w + 1 + j = w + n)
    (downRecord : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hphysical :
      ∃ logged diagnostic post,
        ActiveFollowerLogging.checkedLogging i left.input.row
          (left.input.state.activations i) left.input.time
          ((left.output.preparation.followers.followers i).arm,
            left.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before =
            .ok logged ∧
        logged.buffer = before.buffer ++ ReferencePrelaunchFollower.logAt i
          left.input.row (left.input.state.activations i) left.input.time
          ((left.output.preparation.followers.followers i).arm,
            left.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
        diagnostic = ReferenceDownReception.referenceDownCut p
          left.output.preparation.coordinator.downView i left.input.row
          left.input.time
          (left.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
        (ReferenceActivePhysicalStep.recordFollower
          left.output.preparation.coordinator.downView i left.input.row
          (left.input.state.activations i) left.input.time (left.input.active i)
          (left.output.preparation.followers.followers i).arm
          (left.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before).result =
            .ok post ∧
        (ReferenceActivePhysicalStep.recordFollower
          left.output.preparation.coordinator.downView i left.input.row
          (left.input.state.activations i) left.input.time (left.input.active i)
          (left.output.preparation.followers.followers i).arm
          (left.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before).downInput =
            some logged ∧
        (ReferenceActivePhysicalStep.recordFollower
          left.output.preparation.coordinator.downView i left.input.row
          (left.input.state.activations i) left.input.time (left.input.active i)
          (left.output.preparation.followers.followers i).arm
          (left.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before).down =
            some diagnostic ∧
        DeclaredFollowerLocalRound.releaseAndFinish rate i left.input.row
          left.input.time
          (left.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before memory post =
            .ok (post, memory) ∧
        (left.output.followers i).configuration = .ordinary post memory ∧
        (left.output.followers i).failure = none ∧
        (left.output.followers i).downInput = some logged ∧
        (left.output.followers i).down = some diagnostic ∧
        post.status = .unoccupied ∧ post.S ≤ p.T * D p ∧ post.delta ≤ D p ∧
        post.backlog ≤ p.T * D p ∧ post.S + post.backlog ≤ w * D p ∧
        (∀ saved ∈ post.buffer,
          1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
        (post.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
        (∀ saved ∈ post.buffer, ∃ q : ℕ, q ≤ D p ∧
          saved.observation.val = (q : ℝ) / (D p : ℝ)) ∧
        post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        (∀ saved ∈ post.buffer, saved.calendarRound < s + (w + 1) + j + 2) ∧
        post.downBatch.pending.length < AffineBatchDecoder.quota p ∧
        (∀ batch ∈ post.downBatch.completed,
          batch.length = AffineBatchDecoder.quota p) ∧
        ((post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
          post.lastDown = some (downRecord)) ∧
        post.initializationFailure = before.initializationFailure) :
    ∃ logged cut post,
      ActiveFollowerLogging.checkedLogging i right.input.row
        (right.input.state.activations i) right.input.time
        ((right.output.preparation.followers.followers i).arm,
          right.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before =
          .ok logged ∧
      logged.buffer = before.buffer ++ ReferencePrelaunchFollower.logAt i
        right.input.row (right.input.state.activations i) right.input.time
        ((right.output.preparation.followers.followers i).arm,
          right.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
      cut = ReferenceDownReception.referenceDownCut p
        right.output.preparation.coordinator.downView i right.input.row
        right.input.time
        (right.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
      (ReferenceActivePhysicalStep.recordFollower
        right.output.preparation.coordinator.downView i right.input.row
        (right.input.state.activations i) right.input.time (right.input.active i)
        (right.output.preparation.followers.followers i).arm
        (right.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before).result =
          .ok post ∧
      (ReferenceActivePhysicalStep.recordFollower
        right.output.preparation.coordinator.downView i right.input.row
        (right.input.state.activations i) right.input.time (right.input.active i)
        (right.output.preparation.followers.followers i).arm
        (right.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before).downInput =
          some logged ∧
      (ReferenceActivePhysicalStep.recordFollower
        right.output.preparation.coordinator.downView i right.input.row
        (right.input.state.activations i) right.input.time (right.input.active i)
        (right.output.preparation.followers.followers i).arm
        (right.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before).down =
          some cut ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate i right.input.row
        right.input.time
        (right.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before memory post =
          .ok (post, memory) ∧
      (right.output.followers i).configuration = .ordinary post memory ∧
      (right.output.followers i).failure = none ∧
      (right.output.followers i).downInput = some logged ∧
      (right.output.followers i).down = some cut ∧
      post.status = .unoccupied ∧
      ActiveFollowerLifecycle.localStateDomainValid post ∧
      ActiveFollowerLifecycle.localBufferValid post ∧
      ActiveFollowerLifecycle.downDecoderStateValid post ∧ post.S ≤ p.T * D p ∧ post.delta ≤ D p ∧
      post.backlog ≤ p.T * D p ∧ post.S + post.backlog ≤ w * D p ∧
      (∀ saved ∈ post.buffer,
        1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
      (post.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
      (∀ saved ∈ post.buffer, ∃ q : ℕ, q ≤ D p ∧
        saved.observation.val = (q : ℝ) / (D p : ℝ)) ∧
      post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ post.buffer, saved.calendarRound < s + w + n + 2) ∧
      post.downBatch.pending.length < AffineBatchDecoder.quota p ∧
      (∀ batch ∈ post.downBatch.completed,
        batch.length = AffineBatchDecoder.quota p) ∧
      ((post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
        post.lastDown = some (downRecord)) ∧
      post.initializationFailure = before.initializationFailure := by
  cases hrecord
  rcases hphysical with ⟨logged, cut, post, hlogging, hloggedBuffer,
    hcut, hresult, hcallInput, hcallCut, hfinish, houtputConfig,
    hfailure, houtputInput, houtputCut, hpostStatus, hpostS, hpostDelta,
    hpostBacklog, hpostMass, hpostCalendar, hpostKeys, hpostQuant,
    hpostPair, hpostStamps, hpostPending, hpostCompleted, hpostLast,
    hinitializationFailure⟩
  have hdomainPost : ActiveFollowerLifecycle.localStateDomainValid post :=
    ⟨⟨hpostS, hpostDelta, hpostBacklog⟩,
      ⟨hpostCalendar, hpostKeys, hpostQuant⟩,
      ⟨hpostPending, hpostCompleted⟩⟩
  refine ⟨logged, cut, post, hlogging, hloggedBuffer, hcut, hresult,
    hcallInput, hcallCut, hfinish, houtputConfig, hfailure, houtputInput,
    houtputCut, hpostStatus, hdomainPost,
    ⟨hpostCalendar, hpostKeys, hpostQuant⟩, ⟨hpostPending, hpostCompleted⟩,
    hpostS, hpostDelta, hpostBacklog, hpostMass, hpostCalendar, hpostKeys,
    hpostQuant, hpostPair, ?_, hpostPending, hpostCompleted, hpostLast,
    hinitializationFailure⟩
  have hdate : s + (w + 1) + j + 2 = s + w + n + 2 := by omega
  simpa only [hdate] using hpostStamps

/-- Actual physical callbacks and adjacent prefix states at every positive
coordinate, with the same live payload as the actual cutoff record. -/
theorem actual_first_collection_down_physical_boundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
    ∃ (hB : 0 < B.length)
      (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
      (base : Fin (p.m - 1) → ℕ),
      (B[0]'hB).input.state.coordinator = .live r q base ∧
      r.payload.sigma.val = s ∧
      (∀ i : Fin (p.m - 1), (r.payload.downRecord i).val.q = 0) ∧
      ∀ (n : Fin B.length), 0 < n.val → ∀ i : Fin (p.m - 1),
      ∃ (hRun : s + (w + n.val) ≤ p.T)
        (hNext : s + (w + n.val + 1) ≤ p.T),
      let record := B[n.val]
      record.input.state = (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (w + n.val) hRun
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1).finalState ∧
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (w + n.val + 1) hNext
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1).finalState = record.output.next ∧
      ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        record.input.state.followers i = .ordinary before memory ∧
        (record.output.preparation.followers.followers i).configuration =
          .ordinary before memory ∧
        before.status = .unoccupied ∧
        ActiveFollowerLifecycle.localStateDomainValid before ∧
        ActiveFollowerLifecycle.localBufferValid before ∧
        ActiveFollowerLifecycle.downDecoderStateValid before ∧
        before.S ≤ p.T * D p ∧ before.delta ≤ D p ∧ before.backlog ≤ p.T * D p ∧
        before.S + before.backlog ≤ w * D p ∧
        (∀ saved ∈ before.buffer, 1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
        (before.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
        (∀ saved ∈ before.buffer, ∃ q : ℕ, q ≤ D p ∧
          saved.observation.val = (q : ℝ) / (D p : ℝ)) ∧
        before.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        (∀ saved ∈ before.buffer, saved.calendarRound < s + w + n.val + 1) ∧
        before.downBatch.pending.length < AffineBatchDecoder.quota p ∧
        (∀ batch ∈ before.downBatch.completed, batch.length = AffineBatchDecoder.quota p) ∧
        ((before.lastDown = none ∧ before.S = 0 ∧ before.delta = 0 ∧ before.backlog = 0) ∨
          before.lastDown = some (r.payload.downRecord i)) ∧
        ActiveFollowerLifecycle.startRound rate.eta record.input.time before memory =
          .ok (before, memory) ∧
        ∃ logged cut post,
          ActiveFollowerLogging.checkedLogging i record.input.row
            (record.input.state.activations i) record.input.time
            ((record.output.preparation.followers.followers i).arm,
              record.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before =
              .ok logged ∧
          logged.buffer = before.buffer ++ ReferencePrelaunchFollower.logAt i
            record.input.row (record.input.state.activations i) record.input.time
            ((record.output.preparation.followers.followers i).arm,
              record.output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
          cut = ReferenceDownReception.referenceDownCut p
            record.output.preparation.coordinator.downView i record.input.row
            record.input.time
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
          (ReferenceActivePhysicalStep.recordFollower
            record.output.preparation.coordinator.downView i record.input.row
            (record.input.state.activations i) record.input.time (record.input.active i)
            (record.output.preparation.followers.followers i).arm
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before).result =
              .ok post ∧
          (ReferenceActivePhysicalStep.recordFollower
            record.output.preparation.coordinator.downView i record.input.row
            (record.input.state.activations i) record.input.time (record.input.active i)
            (record.output.preparation.followers.followers i).arm
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before).downInput =
              some logged ∧
          (ReferenceActivePhysicalStep.recordFollower
            record.output.preparation.coordinator.downView i record.input.row
            (record.input.state.activations i) record.input.time (record.input.active i)
            (record.output.preparation.followers.followers i).arm
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before).down =
              some cut ∧
          DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row
            record.input.time
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) before memory post =
              .ok (post, memory) ∧
          (record.output.followers i).configuration = .ordinary post memory ∧
          (record.output.followers i).failure = none ∧
          (record.output.followers i).downInput = some logged ∧
          (record.output.followers i).down = some cut ∧
          post.status = .unoccupied ∧
          ActiveFollowerLifecycle.localStateDomainValid post ∧
          ActiveFollowerLifecycle.localBufferValid post ∧
          ActiveFollowerLifecycle.downDecoderStateValid post ∧ post.S ≤ p.T * D p ∧ post.delta ≤ D p ∧
          post.backlog ≤ p.T * D p ∧ post.S + post.backlog ≤ w * D p ∧
          (∀ saved ∈ post.buffer,
            1 ≤ saved.calendarRound ∧ saved.calendarRound ≤ p.T) ∧
          (post.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
          (∀ saved ∈ post.buffer, ∃ q : ℕ, q ≤ D p ∧
            saved.observation.val = (q : ℝ) / (D p : ℝ)) ∧
          post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
          (∀ saved ∈ post.buffer, saved.calendarRound < s + w + n.val + 2) ∧
          post.downBatch.pending.length < AffineBatchDecoder.quota p ∧
          (∀ batch ∈ post.downBatch.completed,
            batch.length = AffineBatchDecoder.quota p) ∧
          ((post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
            post.lastDown = some (r.payload.downRecord i)) ∧
          post.initializationFailure = before.initializationFailure := by
  classical
  intro s epoch w B
  let W := (epoch.records.drop (w + 1)).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  have hfirstActual : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source rewards C_star C_h hcross) s := by
    simpa only [s] using
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1
  have hm : 2 ≤ p.m := p.two_le_m
  have hseed := ReferenceFirstCollectionDownThresholdDetection.actual_first_collection_down_cutoff_seed
    rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨hB, r, q, base, old, memory, hcoord, hsigma, hzero,
    hheadInput, hreset, hoccupied, hdomain, hbuffer, hdecoder, hresetRound⟩ :=
      hseed ⟨0, by omega⟩
  change 0 < B.length at hB
  have hcount : epoch.records.length = count := by
    simpa [epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      ReferenceActivePhysicalHorizon.run_record_count
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s count hspan
        hfirstActual
  have hw : w < count := by
    simpa [epoch, w] using hshort
  have hwindowShort : w < epoch.records.length := by rw [hcount]; exact hw
  have hlenB : B.length = W.length + 1 := by
    dsimp only [B, ReferenceCollectionPhaseHistory.collectionWindow]
    rw [List.length_append, List.length_take]
    have hdrop : 1 ≤ (epoch.records.drop w).length := by
      rw [List.length_drop]
      omega
    rw [Nat.min_eq_left hdrop]
    change 1 + W.length = W.length + 1
    omega
  have hrecords := ReferenceFirstCollectionReadyStream.generatedFirstCutoffRun_records_eq
    (rate := rate) source rewards C_star C_h hcross count hspan
  have hrecords' :
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records = epoch.records := by
    simpa [ReferenceFirstCollectionReadyStream.startTime, epoch, s,
      ReferenceFirstCollectionReadyStream.actualEpoch] using hrecords
  have hshortGenerated := ReferenceFirstCollectionReadyStream.generatedFirstCutoffRun_short
    (rate := rate) source rewards C_star C_h hcross count hspan hshort
  have hshortGenerated' :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hcross s rfl count hspan).records).length < count := by
    simpa [ReferenceFirstCollectionReadyStream.startTime, epoch, s,
      ReferenceFirstCollectionReadyStream.actualEpoch] using hshortGenerated
  have hG := ReferenceGeneratedFirstCollectionFollowerPrefix.actual_first_collection_follower_prefix_boundary
    rate source rewards C_star C_h hcross s rfl count hspan hshortGenerated'
  rcases hG with ⟨rG, qG, baseG, hcoordG, _hsigmaG, _hzeroG,
    dispatched, hstartCut, ledger, hinit, hledger, hcutDomain, hclock,
    hpending, hnoAssignment, selected, hcutPrepared, hu, huT, huGrid,
    hledgerSigma, hledgerCutoff, hfirstCutoff, hcutNext,
    ⟨movingLedger, movingSaved, hmoving⟩, hboundaries, hrecordsG⟩
  have hcutAlignment := ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
    rate source rewards C_star C_h count hcross hspan hshort
    (⟨0, hB⟩ : Fin B.length)
  have hcutLookup : epoch.records[w]? = some (B[0]'hB) := by
    simpa [epoch, w, B] using hcutAlignment.1
  have hcutLookupG :
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records[w]? =
        some (B[0]'hB) := by
    rw [hrecords']
    exact hcutLookup
  have hcutIndex : w <
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records.length :=
    (List.getElem?_eq_some_iff.mp hcutLookupG).1
  have hcutRecord :
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records[w]'hcutIndex = B[0]'hB :=
    Option.some.inj ((List.getElem?_eq_getElem hcutIndex).symm.trans hcutLookupG)
  have hcoordG' : (B[0]'hB).input.state.coordinator = .live rG qG baseG := by
    exact (congrArg (fun record : ReferenceCollectionPhaseHistory.Record p rate =>
      record.input.state.coordinator) hcutRecord).symm.trans hcoordG
  have hsameLive :
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live rG qG baseG =
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live r q base :=
    hcoordG'.symm.trans hcoord
  cases hsameLive
  refine ⟨hB, r, q, base, hcoord, hsigma, hzero, ?_⟩
  intro n hn i
  let actualRecord := B[n.val]
  let j := n.val - 1
  have hj : j < W.length := by
    have hnB : n.val < B.length := n.isLt
    have hn' : n.val < W.length + 1 := by omega
    dsimp [j]
    omega
  have hindex : w + 1 + j = w + n.val := by dsimp [j]; omega
  have hrecordAlignment := ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
    rate source rewards C_star C_h count hcross hspan hshort n
  have hrecordLookup : epoch.records[w + n.val]? = some (B[n.val]) := by
    simpa [epoch, w, B] using hrecordAlignment.1
  have hrecordLookupG :
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records[w + n.val]? =
        some (B[n.val]) := by
    rw [hrecords']
    exact hrecordLookup
  have hrecordIndexG : w + 1 + j <
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records.length := by
    rw [hindex]
    exact (List.getElem?_eq_some_iff.mp hrecordLookupG).1
  have hrecordLookupG' :
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records[w + 1 + j]? =
        some (B[n.val]) := by
    rw [hindex]
    exact hrecordLookupG
  have hwindowLengthGenerated :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hcross s rfl count hspan).records).length = w := by
    rw [hrecords']
  have hrecordIndexG' :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hcross s rfl count hspan).records).length +
          1 + j <
        (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hcross s rfl count hspan).records.length := by
    rw [hwindowLengthGenerated]
    exact hrecordIndexG
  have hrecordLookupG'' :
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records[
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
              rate source rewards C_star C_h hcross s rfl count hspan).records).length +
            1 + j]? = some (B[n.val]) := by
    rw [hwindowLengthGenerated, hrecords', hindex]
    exact hrecordLookup
  have hrecordG' :
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records[
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
              rate source rewards C_star C_h hcross s rfl count hspan).records).length +
            1 + j]'hrecordIndexG' = B[n.val] :=
    Option.some.inj ((List.getElem?_eq_getElem hrecordIndexG').symm.trans hrecordLookupG'')
  have hGentry := hrecordsG j hj i
  rcases hGentry with ⟨before, memory, hcurrent, hstatus, hbeforeDomain,
    _hbeforeBufferValid, _hbeforeDecoderValid, _hbeforeSBound, _hbeforeDeltaBound,
    _hbeforeBacklogBound, hbeforeMass, _hbeforeCalendar, _hbeforeKeys,
    _hbeforeQuant, hbeforePair, hbeforeStamps, hbeforePending, hbeforeCompleted,
    hbeforeLast, hstartRound, hprepared, _hup, _hnoUp, _hdata, _hother,
    hphysical, hnext⟩
  have hpreparedActual := hrecordG' ▸ hprepared
  have hstartActual := hrecordG' ▸ hstartRound
  have hprefixEndpoints :=
    ReferenceFirstCollectionReadyStep.actual_collection_window_prefix_endpoints
      rate source rewards C_star C_h count hcross hspan hshort n
  have hWprefix : W <+: epoch.records.drop (w + 1) := by
    dsimp only [W]
    exact List.takeWhile_prefix _
  have hWlength : W.length ≤ count - (w + 1) := by
    have hlength := hWprefix.length_le
    simpa only [List.length_drop, hcount] using hlength
  have htail : w + 1 + W.length ≤ count := by omega
  have hnB : n.val < B.length := n.isLt
  have hn' : n.val < W.length + 1 := by omega
  have hindexBound : w + n.val + 1 ≤ count := by omega
  have hspan' : s + count ≤ p.T := by simpa only [s] using hspan
  have hRun : s + (w + n.val) ≤ p.T := by
    omega
  have hNext : s + (w + n.val + 1) ≤ p.T := by
    omega
  have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate source rewards C_star C_h hcross
  have hinitial : ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross =
        ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross := by
    unfold ReferenceFirstCollectionEpochAlignment.actualLaunchState
    exact (Option.get_of_eq_some
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).2 hcross) hlaunch).symm
  have hfirstLaunch : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross) s :=
    hinitial ▸ hfirstActual
  have hcurrentLaunch :
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (w + n.val) hRun hfirstLaunch).finalState.followers i =
      .ordinary before memory := by
    simpa only [hwindowLengthGenerated, hindex] using hcurrent
  have hrunEq :
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (w + n.val) hRun hfirstActual).finalState =
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (w + n.val) hRun hfirstLaunch).finalState := by
    cases hinitial
    rfl
  have hcurrent' :
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (w + n.val) hRun hfirstActual).finalState.followers i =
      .ordinary before memory := by
    exact (congrArg (fun state => state.followers i) hrunEq).trans hcurrentLaunch
  have hprefixFollower : (B[n.val]).input.state.followers i =
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards s (w + n.val) hRun hfirstActual).finalState.followers i := by
    exact congrArg (fun state => state.followers i) hprefixEndpoints.1
  have hinputOrdinary : (B[n.val]).input.state.followers i = .ordinary before memory :=
    hprefixFollower.trans hcurrent'
  refine ⟨hRun, hNext, hprefixEndpoints.1, hprefixEndpoints.2,
    before, memory, hinputOrdinary, hpreparedActual, hstatus, hbeforeDomain,
    _hbeforeBufferValid, _hbeforeDecoderValid, _hbeforeSBound, _hbeforeDeltaBound,
    _hbeforeBacklogBound, hbeforeMass, _hbeforeCalendar, _hbeforeKeys,
    _hbeforeQuant, hbeforePair, ?_, hbeforePending, hbeforeCompleted,
    hbeforeLast, hstartActual, ?_⟩
  · intro saved hsaved
    have hstamp := hbeforeStamps saved hsaved
    rw [hwindowLengthGenerated] at hstamp
    dsimp only [j] at hindex
    omega
  · have hphysicalAligned := physical_callbacks_of_record_eq
      i _ _ hrecordG' before memory s _ j n.val
      (by simpa only [hwindowLengthGenerated] using hindex)
      (r.payload.downRecord i) hphysical
    simpa only [hwindowLengthGenerated] using hphysicalAligned

end Bandits.Support.ReferenceFirstCollectionDownPhysicalBoundary

end
