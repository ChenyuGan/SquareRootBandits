/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionNumericalReplay
public import Bandits.Support.ReferenceCollectionAcceptedQueueContinuation
public import Bandits.Support.ReferenceFirstLaunchNumericalCell

import Lean.Elab.Tactic.Omega

/-!
# First assignment accepted-UP numerical queue continuation

Sources: `sources/zip4/manuscript/06_interruptions.tex:80-100,246-295`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:46-64`.

The generic result retains the actual first-assignment DOWN/UP numerical
replay witness and composes it with the accepted physical collection suffix
for every endpoint after that acceptance. Its queue values are expressed by
the existing replay streams. It does not identify them with a source-global
arrival or service sequence.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction
open ReferenceCollectionPhaseHistory
open CoordinatorCollectionLedger
open ReferenceFirstAcceptedUpNumericSnapshot
open ReferenceAcceptedUpFollowerHistory
open QueueReplay

namespace Bandits.Support.ReferenceFirstCollectionQueueContinuation

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem replay_add_score (capacity score backlog : ℕ)
    (records : List (Bool × ℕ)) :
    QueueReplay.replay capacity (score, backlog) records =
      (score + (QueueReplay.replay capacity (0, backlog) records).1,
        (QueueReplay.replay capacity (0, backlog) records).2) := by
  induction records generalizing score backlog with
  | nil => simp [QueueReplay.replay]
  | cons record rest ih =>
      have htransition :
          QueueReplay.transition capacity (score, backlog) record =
            (score + (QueueReplay.transition capacity (0, backlog) record).1,
              (QueueReplay.transition capacity (0, backlog) record).2) := by
        cases record with
        | mk enabled arrival => cases enabled <;> simp [QueueReplay.transition]
      change QueueReplay.replay capacity
          (QueueReplay.transition capacity (score, backlog) record) rest =
        (score + (QueueReplay.replay capacity
          (QueueReplay.transition capacity (0, backlog) record) rest).1,
          (QueueReplay.replay capacity
            (QueueReplay.transition capacity (0, backlog) record) rest).2)
      rw [htransition]
      rw [ih (score + (QueueReplay.transition capacity (0, backlog) record).1)
        (QueueReplay.transition capacity (0, backlog) record).2]
      rw [ih (QueueReplay.transition capacity (0, backlog) record).1
        (QueueReplay.transition capacity (0, backlog) record).2]
      simp only [Nat.add_assoc]

/-- Continue the same first-assignment accepted UP from its sender-local
numerical replay through each actual endpoint of the collection segment.
The first accepted round is included exactly once. Disabled physical records
remain those of the actual segment; replay equality follows from the checked
transition, not from equality with a locally filtered record list. -/
theorem actual_first_assignment_accepted_up_queue_suffix
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed memory)
    (hnone : seed.lastDown = none)
    (hunoccupied : seed.status = .unoccupied)
    (hvalid : ActiveFollowerLifecycle.localBufferValid seed)
    (hpair : seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ start)
    (offset : ℕ) (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records
      offset = some segment)
    (k : ℕ) (hk : k < segment.records.length)
    (completed : ReferenceCollectionSegmentExtraction.CompletedRound rate)
    (hextract : ReferenceCollectionSegmentExtraction.extractRound
      (segment.records[k]'hk) = some completed)
    (haccepted : completed.accepted = true)
    (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hparsed : completed.input.parsed = some M)
    (hselected : completed.input.selectedFollower = i)
    (hsigma : M.val.sigma = start + 1) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
    ∃ globalIndex : Fin E.records.length,
      globalIndex.val = offset + k ∧
      E.records[globalIndex.val] = segment.records[k]'hk ∧
      ReferenceCollectionPhaseHistory.AcceptedUp
        (E.records[globalIndex.val]).input i M ∧
      ∃ d : Fin E.records.length, d.val < globalIndex.val ∧
        ∃ message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord
            (p := p) (rate := rate),
          ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[d.val] i message ∧
          message.val.sigma = start + 1 ∧
          let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)
          let u := FollowerCutoffScan.firstCutoff p rate.eta.val
            (ActiveFollowerDownAcceptance.downStart p rate message) bits
          let m := u - (start + 1)
          let b := max m (d.val + 1)
          let V := fun r => QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              E.records i d.val message r)
          start + 1 < u ∧ u ≤ start + globalIndex.val + 1 ∧
          0 < m ∧ m ≤ globalIndex.val ∧ b ≤ globalIndex.val ∧
          M.val.S = (V m).1 ∧ M.val.q = (V m).2 ∧
          M.val.delta = (V m).1 - (V (m - 1)).1 ∧
          (∃ hb : b < E.records.length, ∃ boundary boundaryMemory,
            (ReferenceFollowerFixedReply.actualChoice E.records[b] i).configuration =
              .ordinary boundary boundaryMemory ∧
            boundary.status = .unoccupied ∧ boundary.lastDown = some message ∧
            boundary.S = (V m).1 ∧ boundary.backlog = (V m).2 ∧
            boundary.delta = (V m).1 - (V (m - 1)).1) ∧
          ∃ initializer : ReferenceCollectionSegmentExtraction.Initializer p,
            segment.context.initializer = some initializer ∧
            initializer.checkedStart rate = .success segment.context.preLedger ∧
            CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
              (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
              initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
              initializer.base initializer.outside segment.inputs =
                .success ⟨segment.context.preLedger, segment.accepted, segment.final⟩ ∧
            ∃ started : CoordinatorCollectionLedger.Ledger p rate.eta.val
                rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
                rate.n rate.n_scale,
              started.assignment = initializer.assignment ∧
              initializer.assignment.arm i = started.assignment.arm i ∧
              started.sigma = initializer.sigma ∧
              started.cutoff = initializer.cutoff ∧
              started.freezeAt = initializer.freezeAt ∧
            let arm := initializer.assignment.arm i
            let C := fun h => (segment.records.take h).map
              (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                segment.context.preLedger arm)
            let Q := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
              (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                E.records i d.val message m ++ C h)
            let L := fun h => ReferenceCollectionSegmentExtraction.endpointLedger
              segment.context.preLedger (segment.records.take h)
            (∀ h, k + 1 ≤ h → h ≤ segment.records.length →
              ∃ suffixAccepted,
                CollectionCheckedExecution.checkedRounds completed.final
                  ((segment.inputs.drop (k + 1)).take (h - (k + 1))) =
                    some (suffixAccepted, L h) ∧
                (L h).currentRegisters arm = some ⟨
                  (Q h).2, (Q h).1 - (Q (h - 1)).1⟩ ∧
                (L h).increment arm =
                  (QueueReplay.replay (4 * rate.n) (0, (V m).2) (C h)).1 ∧
                (V m).1 + (L h).increment arm = (Q h).1 ∧
                (L h).cutoffRegisters arm =
                  some ⟨initializer.base i + (V m).1, (V m).2,
                    (V m).1 - (V (m - 1)).1⟩ ∧
                (initializer.base i + (V m).1) + (L h).increment arm =
                  initializer.base i + (Q h).1 ∧
                (L h).assignment = initializer.assignment ∧
                (L h).sigma = initializer.sigma ∧
                (L h).cutoff = initializer.cutoff ∧
                (L h).freezeAt = initializer.freezeAt) ∧
            ∃ suffixAccepted,
              CollectionCheckedExecution.checkedRounds completed.final
                ((segment.inputs.drop (k + 1)).take
                  (segment.records.length - (k + 1))) =
                some (suffixAccepted, segment.final) := by
  classical
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  have hN := ReferenceFirstCollectionNumericalReplay.actual_first_collection_numerical_replay
    initial rows J rewards start count span active hfirst i seed memory hseed hnone
    hunoccupied hvalid hpair htime offset segment hsegment k hk completed hextract
    haccepted M hparsed hselected hsigma
  rcases hN with ⟨globalIndex, hglobalIndex, hrecord, hacceptedUp,
    d, hd, message, hretainedDown, hmessageSigma,
    huBound, huLast, hmPos, hmBound, hbBound, hMS, hMq, hMdelta,
    hboundary, initializerN, hinitializerN, hcheckedStartN, hNtail⟩
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val
    (ActiveFollowerDownAcceptance.downStart p rate message) bits
  let m := u - (start + 1)
  let b := max m (d.val + 1)
  let V := fun r => QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
      E.records i d.val message r)
  have hC :=
    _root_.Bandits.Support.ReferenceCollectionAcceptedQueueContinuation.actual_accepted_up_physical_queue_suffix_continuation
      initial rows J rewards start count span active hfirst offset segment hsegment k hk
      completed hextract haccepted M hparsed i hselected
  rcases hC with ⟨initializerC, hinitializerC, hcheckedStartC, hwholeRunC,
    prefixExecutionC, hprefixRunC, hprefixInitialC, hprefixFinalC,
    recordingC, startedC, decodedC, bankC, finishedC,
    hrecordingC, hrunRecorderC, hstartC, hreceiveC, hdecodeC, hfinishC,
    hfinishedC, hinputC, hboundC, lastIndexC, hsourceC, hlastC, hcursorC,
    hassignmentC, harmC, hsigmaC, hcutoffC, hfreezeC, hbaseC,
    hcutoffLowerC, hcutoffUpperC, hcursorUpperC, hprefixUnknownC,
    hstartedUnknownC, pastC, currentC, hpastC, hlastRecordC, hsuppliedC,
    hpastPhysicalC, hcurrentPhysicalC, hpastCurrentC, hphysicalAppendC,
    hfinishedCurrentC, hfinishedIncrementC, hfinishedCutoffC, hforallC, hfullC⟩
  have hinitializerEq : initializerN = initializerC :=
    Option.some.inj (hinitializerN.symm.trans hinitializerC)
  subst initializerC
  refine ⟨globalIndex, hglobalIndex, hrecord, hacceptedUp,
    d, hd, message, hretainedDown, hmessageSigma,
    huBound, huLast, hmPos, hmBound, hbBound, hMS, hMq, hMdelta,
    hboundary, initializerN, hinitializerN, hcheckedStartC, hwholeRunC,
    startedC, hassignmentC, harmC, hsigmaC, hcutoffC, hfreezeC, ?_, ?_⟩
  · intro h hh₁ hh₂
    rcases hforallC h hh₁ hh₂ with
      ⟨suffixAcceptedC, hcheckedSuffixC, hcurrentC, hincrementC, hcutoffRegistersC,
        hassignmentC', hsigmaC', hcutoffC', hfreezeC'⟩
    have hQ (r : ℕ) :
        QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              E.records i d.val message m ++
              (segment.records.take r).map
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                  segment.context.preLedger (initializerN.assignment.arm i))) =
          ((V m).1 +
              (QueueReplay.replay (4 * rate.n) (0, (V m).2)
                ((segment.records.take r).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                    segment.context.preLedger (initializerN.assignment.arm i)))).1,
            (QueueReplay.replay (4 * rate.n) (0, (V m).2)
              ((segment.records.take r).map
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                  segment.context.preLedger (initializerN.assignment.arm i)))).2) := by
      calc
        _ = QueueReplay.replay (4 * rate.n)
              (QueueReplay.replay (4 * rate.n) (0, 0)
                (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                  E.records i d.val message m))
              ((segment.records.take r).map
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                  segment.context.preLedger (initializerN.assignment.arm i))) := by
          rw [QueueReplay.replay_append]
        _ = _ := replay_add_score (4 * rate.n) (V m).1 (V m).2
          ((segment.records.take r).map
            (ReferenceCollectionRawBufferHistory.physicalQueueRecord
              segment.context.preLedger (initializerN.assignment.arm i)))
    have hcurrent :
        (ReferenceCollectionSegmentExtraction.endpointLedger segment.context.preLedger
          (segment.records.take h)).currentRegisters (initializerN.assignment.arm i) =
          some ⟨(QueueReplay.replay (4 * rate.n) (0, (V m).2)
              ((segment.records.take h).map
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                  segment.context.preLedger (initializerN.assignment.arm i)))).2,
            (QueueReplay.replay (4 * rate.n) (0, (V m).2)
              ((segment.records.take h).map
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                  segment.context.preLedger (initializerN.assignment.arm i)))).1 -
            (QueueReplay.replay (4 * rate.n) (0, (V m).2)
              ((segment.records.take (h - 1)).map
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                  segment.context.preLedger (initializerN.assignment.arm i)))).1⟩ := by
      simpa [hMq] using hcurrentC
    have hcurrentQ :
        (ReferenceCollectionSegmentExtraction.endpointLedger segment.context.preLedger
          (segment.records.take h)).currentRegisters (initializerN.assignment.arm i) =
          some ⟨
            (QueueReplay.replay (4 * rate.n) (0, 0)
              (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                E.records i d.val message m ++
                (segment.records.take h).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                    segment.context.preLedger (initializerN.assignment.arm i)))).2,
            (QueueReplay.replay (4 * rate.n) (0, 0)
              (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                E.records i d.val message m ++
                (segment.records.take h).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                    segment.context.preLedger (initializerN.assignment.arm i)))).1 -
            (QueueReplay.replay (4 * rate.n) (0, 0)
              (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                E.records i d.val message m ++
                (segment.records.take (h - 1)).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                    segment.context.preLedger (initializerN.assignment.arm i)))).1⟩ := by
      rw [hQ h, hQ (h - 1)]
      rw [hcurrent]
      simp only [Option.some.injEq, CoordinatorCollectionLedger.CurrentRegister.mk.injEq]
      constructor
      · trivial
      · omega
    have hincrement :
        (ReferenceCollectionSegmentExtraction.endpointLedger segment.context.preLedger
          (segment.records.take h)).increment (initializerN.assignment.arm i) =
          (QueueReplay.replay (4 * rate.n) (0, (V m).2)
            ((segment.records.take h).map
              (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                segment.context.preLedger (initializerN.assignment.arm i)))).1 := by
      simpa [hMq] using hincrementC
    have hsum :
        (V m).1 +
            (ReferenceCollectionSegmentExtraction.endpointLedger segment.context.preLedger
              (segment.records.take h)).increment (initializerN.assignment.arm i) =
          (QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              E.records i d.val message m ++
              (segment.records.take h).map
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                  segment.context.preLedger (initializerN.assignment.arm i)))).1 := by
      rw [hincrement]
      exact (congrArg Prod.fst (hQ h)).symm
    have hcutoffRegisters :
        (ReferenceCollectionSegmentExtraction.endpointLedger segment.context.preLedger
          (segment.records.take h)).cutoffRegisters (initializerN.assignment.arm i) =
          some ⟨initializerN.base i + (V m).1, (V m).2,
            (V m).1 - (V (m - 1)).1⟩ := by
      simpa [hMS, hMq, hMdelta] using hcutoffRegistersC
    have hcutoffSum :
        (initializerN.base i + (V m).1) +
            (ReferenceCollectionSegmentExtraction.endpointLedger segment.context.preLedger
              (segment.records.take h)).increment (initializerN.assignment.arm i) =
          initializerN.base i +
            (QueueReplay.replay (4 * rate.n) (0, 0)
              (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                E.records i d.val message m ++
                (segment.records.take h).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                    segment.context.preLedger (initializerN.assignment.arm i)))).1 := by
      omega
    refine ⟨suffixAcceptedC, hcheckedSuffixC, hcurrentQ, hincrement, hsum,
      hcutoffRegisters, hcutoffSum,
      ?_, ?_, ?_, ?_⟩
    · simpa using hassignmentC'
    · simpa using hsigmaC'
    · simpa using hcutoffC'
    · simpa using hfreezeC'
  · exact hfullC

/-- Specialize the numerical continuation to the actual crossing launch.
The selected row is the source input's original selected index, and the rows
and reward table remain the original complete arrays. All launch seed, active,
first-coordinator, buffer, DOWN, and calendar premises are produced from the
crossing branch; the accepted segment and first-sigma selectors remain
explicit inputs. -/
theorem actual_first_assignment_accepted_up_queue_suffix_from_crossing
    (source : ReferenceFirstLaunchNumericalCell.SourceInput p)
    (rewards : ReferenceFirstLaunchNumericalCell.RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (span : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
      + count ≤ p.T)
    (i : Fin (p.m - 1))
    (offset : ℕ) (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
        count span
        (ReferenceFirstLaunchNumericalCell.launchState_allActiveAtStart
          rate source rewards C_star C_h hc)).records offset = some segment)
    (k : ℕ) (hk : k < segment.records.length)
    (completed : ReferenceCollectionSegmentExtraction.CompletedRound rate)
    (hextract : ReferenceCollectionSegmentExtraction.extractRound
      (segment.records[k]'hk) = some completed)
    (haccepted : completed.accepted = true)
    (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hparsed : completed.input.parsed = some M)
    (hselected : completed.input.selectedFollower = i)
    (hsigma : M.val.sigma = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
      + 1) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    let s := ReferenceInitializationRun.elapsed p b.completed
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
    let E := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count span
      (ReferenceFirstLaunchNumericalCell.launchState_allActiveAtStart
        rate source rewards C_star C_h hc)
    ∃ globalIndex : Fin E.records.length,
      globalIndex.val = offset + k ∧
      E.records[globalIndex.val] = segment.records[k]'hk ∧
      ReferenceCollectionPhaseHistory.AcceptedUp
        (E.records[globalIndex.val]).input i M ∧
      ∃ d : Fin E.records.length, d.val < globalIndex.val ∧
        ∃ message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord
            (p := p) (rate := rate),
          ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[d.val] i message ∧
          message.val.sigma = s + 1 ∧
          let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
          let u := FollowerCutoffScan.firstCutoff p rate.eta.val
            (ActiveFollowerDownAcceptance.downStart p rate message) bits
          let m := u - (s + 1)
          let b := max m (d.val + 1)
          let V := fun r => QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              E.records i d.val message r)
          s + 1 < u ∧ u ≤ s + globalIndex.val + 1 ∧
          0 < m ∧ m ≤ globalIndex.val ∧ b ≤ globalIndex.val ∧
          M.val.S = (V m).1 ∧ M.val.q = (V m).2 ∧
          M.val.delta = (V m).1 - (V (m - 1)).1 ∧
          (∃ hb : b < E.records.length, ∃ boundary boundaryMemory,
            (ReferenceFollowerFixedReply.actualChoice E.records[b] i).configuration =
              .ordinary boundary boundaryMemory ∧
            boundary.status = .unoccupied ∧ boundary.lastDown = some message ∧
            boundary.S = (V m).1 ∧ boundary.backlog = (V m).2 ∧
            boundary.delta = (V m).1 - (V (m - 1)).1) ∧
          ∃ initializer : ReferenceCollectionSegmentExtraction.Initializer p,
            segment.context.initializer = some initializer ∧
            initializer.checkedStart rate = .success segment.context.preLedger ∧
            CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
              (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
              initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
              initializer.base initializer.outside segment.inputs =
                .success ⟨segment.context.preLedger, segment.accepted, segment.final⟩ ∧
            ∃ started : CoordinatorCollectionLedger.Ledger p rate.eta.val
                rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
                rate.n rate.n_scale,
              started.assignment = initializer.assignment ∧
              initializer.assignment.arm i = started.assignment.arm i ∧
              started.sigma = initializer.sigma ∧
              started.cutoff = initializer.cutoff ∧
              started.freezeAt = initializer.freezeAt ∧
            let arm := initializer.assignment.arm i
            let C := fun h => (segment.records.take h).map
              (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                segment.context.preLedger arm)
            let Q := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
              (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                E.records i d.val message m ++ C h)
            let L := fun h => ReferenceCollectionSegmentExtraction.endpointLedger
              segment.context.preLedger (segment.records.take h)
            (∀ h, k + 1 ≤ h → h ≤ segment.records.length →
              ∃ suffixAccepted,
                CollectionCheckedExecution.checkedRounds completed.final
                  ((segment.inputs.drop (k + 1)).take (h - (k + 1))) =
                    some (suffixAccepted, L h) ∧
                (L h).currentRegisters arm = some ⟨
                  (Q h).2, (Q h).1 - (Q (h - 1)).1⟩ ∧
                (L h).increment arm =
                  (QueueReplay.replay (4 * rate.n) (0, (V m).2) (C h)).1 ∧
                (V m).1 + (L h).increment arm = (Q h).1 ∧
                (L h).cutoffRegisters arm =
                  some ⟨initializer.base i + (V m).1, (V m).2,
                    (V m).1 - (V (m - 1)).1⟩ ∧
                (initializer.base i + (V m).1) + (L h).increment arm =
                  initializer.base i + (Q h).1 ∧
                (L h).assignment = initializer.assignment ∧
                (L h).sigma = initializer.sigma ∧
                (L h).cutoff = initializer.cutoff ∧
                (L h).freezeAt = initializer.freezeAt) ∧
            ∃ suffixAccepted,
              CollectionCheckedExecution.checkedRounds completed.final
                ((segment.inputs.drop (k + 1)).take
                  (segment.records.length - (k + 1))) =
                some (suffixAccepted, segment.final) := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  let s := ReferenceInitializationRun.elapsed p b.completed
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc
  have hlaunch := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate source rewards C_star C_h hc
  rcases hlaunch with ⟨_, _, _, hfirst, _, _, _, hfollower⟩
  rcases hfollower i with
    ⟨hfollowerSeed, hnoneSource, _, _, _, _, hunoccupiedSource, _,
      hvalidSource, hpairSource, htimeSource⟩
  have hseed : initial.followers i = .ordinary
      (ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i))
      (ActiveFollowerLifecycle.initialMemory p) := by
    simpa [initial, x, b] using hfollowerSeed
  have hnone :
      (ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i)).lastDown = none := by
    simpa [x, b] using hnoneSource
  have hunoccupied :
      (ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i)).status = .unoccupied := by
    simpa [x, b] using hunoccupiedSource
  have hvalid : ActiveFollowerLifecycle.localBufferValid
      (ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i)) := by
    simpa [x, b] using hvalidSource
  have hpair :
      (ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i)).buffer.Pairwise
          (fun a b => a.calendarRound < b.calendarRound) := by
    simpa [x, b] using hpairSource
  have htime : ∀ saved ∈
      (ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i)).buffer,
      saved.calendarRound ≤ s := by
    simpa [x, b, s] using htimeSource
  exact actual_first_assignment_accepted_up_queue_suffix
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards s count span
    (ReferenceFirstLaunchNumericalCell.launchState_allActiveAtStart
      rate source rewards C_star C_h hc)
    hfirst i
    (ReferenceInitializationRun.ordinary x b
      (ActualReferenceInitializationBlock.refFollower i))
    (ActiveFollowerLifecycle.initialMemory p)
    hseed hnone hunoccupied hvalid hpair htime offset segment hsegment k hk
    completed hextract haccepted M hparsed hselected hsigma

end Bandits.Support.ReferenceFirstCollectionQueueContinuation

end
