/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDownSecondPureBank
public import Bandits.Support.ReferenceGeneratedDownLaterCompletionDetector
public import Bandits.Support.ReferenceFirstLiveDecoderPastMeasurability

import Lean.Elab.Tactic.Omega

/-!
# Actual first-collection DOWN ambiguity readout

This adapter preserves the actual cutoff-relative pure second batch and joins
it to the existing retained DOWN diagnostic and strict-past flag.  It keeps
the original source input and whole reward table.  It does not identify this
batch with the launch-relative second-batch event or assert a stopped-law
bound.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-55,70-124`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`,
`sources/zip4/manuscript/06_interruptions.tex:477-481`, and
`sources/zip4/manuscript/08_main_theorem.tex:30-46`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFirstLiveDownCompletionReadout
open Bandits.Support.ReferenceFirstLiveDecoderPastMeasurability
open Bandits.Support.ReferenceGeneratedDownBatchCalendar

namespace Bandits.Support.ReferenceFirstCollectionDownAmbiguityDetector

variable {p : ConstructorDimensions.Parameters}

/-- The actual cutoff-relative pure DOWN ambiguity remains attached to its
physical detecting record, identified in the generated-source run at that
same round.  The earlier-reset interval and cohort-envelope joins remain for
a later adapter. -/
theorem actual_collection_down_pure_ambiguity_detector
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
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (control0 : ContinuousLearningRows.TimeControl p) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      ∃ (hwindow : out.window = B),
      ∀ (n : Fin out.ell) (hn : 0 < n.val)
        (i : Fin (p.m - 1))
        (before : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.state.followers i =
          .ordinary before memory →
        before.lastDown = none →
        ∃ hBlen : 0 < B.length,
          ∃ cutoffState : ReferencePrelaunchFollower.State p rate.eta,
          ∃ cutoffMemory : ActiveFollowerLifecycle.LocalMemory p,
            (B[0]'hBlen).input.state.followers i = .ordinary cutoffState cutoffMemory ∧
            (let W0 := cutoffState.downBatch
             let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
               B[n.val]'(by
                 have hnB : n.val < B.length := by
                   rw [← hwindow]
                   exact Nat.lt_of_lt_of_le n.isLt out.withinWindow
                 exact hnB)
             let word := CoordinatorLocalArmChoice.storedDownFlatWord out.payload i
             W0.pending.length < AffineBatchDecoder.quota p ∧
             ∀ hdown : ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time,
               ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
               ∃ choiceMemory : ActiveFollowerLifecycle.LocalMemory p,
               ∃ logged : ReferencePrelaunchFollower.State p rate.eta,
               ∃ cut : ReferenceDownReception.ReferenceDownCutOutput p rate,
                 (record.output.preparation.followers.followers i).configuration =
                   .ordinary choice choiceMemory ∧
                 choice.status = .unoccupied ∧
                 (record.output.followers i).downInput = some logged ∧
                 (record.output.followers i).down = some cut ∧
                 logged = choice ∧
                 cut.expectedWord = some word ∧
                 cut.rawComparison.isSome = true ∧
                 (∀ hpositive : 0 < (record.output.preparation.feedback.observations
                     (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val,
                   (ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take (n.val + 1))).length =
                     AffineBatchDecoder.quota p - W0.pending.length + AffineBatchDecoder.quota p →
                   cut.raw = none →
                   ∃ first pure :
                       List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
                     first.length = AffineBatchDecoder.quota p ∧
                     pure.length = AffineBatchDecoder.quota p ∧
                     (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row
                       record.input.time
                       (record.output.preparation.feedback.observations
                         (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate choice).1 =
                       ⟨[], W0.completed ++ [first, pure]⟩ ∧
                     cut.raw = AffineBatchDecoder.batchOutput pure ∧
                     cut.raw = none ∧
                     ∃ other : AffineChannelLaw.Word (AffineBatchDecoder.width p),
                       other ≠ word ∧
                       AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure) word ∧
                       AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure) other ∧
                     (∀ entry ∈ pure, AffineChannelLaw.affineHash entry.sample word = 1) ∧
                     cut.rawComparison = some false ∧
                     (∀ entry ∈ pure, s + w ≤ entry.time.val ∧
                       entry.time.val ≤ record.input.time.val) ∧
                     (∀ entry ∈ pure, entry.sample =
                       ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
                         entry.time).2 (0, i)) ∧
                     record.input.time.val = s + w + n.val ∧
                     ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
                       record.input.time source = some record ∧
              (∃ hs : s < p.T,
                ∃ x : ReferenceGeneratedDownBatchCalendar.LaunchSource
                    rate rewards C_star C_h s hs,
                  x.val = source ∧
                  ∃ N : Fin (p.T - s),
                    N.val = w + n.val ∧
                    (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                      rate rewards C_star C_h s hs x).records[N.val]'(by
                        rw [ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
                          ReferenceActiveHorizonMeasurability.runOfInput,
                          ReferenceActivePhysicalHorizon.run_record_count]
                        exact N.isLt) = record ∧
                    ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
                      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                        rate rewards C_star C_h s hs i x).2 N)) ∧
                     completedDownBatch record i = some pure ∧
                     completedAmbiguousAfterStart (s + w) record i ∧
                     completedAmbiguousAfterStart s record i ∧
                     retainedDecoderRecordFlag (s := s) record = true ∧
                     strictPastDecoderFlag rate rewards C_star C_h s
                       (record.input.time.val + 1) (by omega) source = true)) := by
  classical
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  let actualWindow := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
  obtain ⟨d, hwindow, _hsigma, _hrecords, hprefix⟩ :=
    ReferenceFirstCollectionDownSecondPureBank.actual_collection_unaccepted_down_second_pure_bank
      rate source rewards C_star C_h count hcross hspan hshort
  refine ⟨d, hwindow, ?_⟩
  let out := d.stream
  intro n hn i before memory hfi hnone
  have hfi' :
      (d.stream.window[n.val]'(Nat.lt_of_lt_of_le n.isLt d.stream.withinWindow)).input.state.followers i =
        .ordinary before memory := hfi
  obtain ⟨hprior, hcutoffExists⟩ := hprefix n hn i before memory hfi' hnone
  obtain ⟨hBlen, cutoffState, cutoffMemory, hcutoff, hbank, hcurrent⟩ :=
    hcutoffExists
  let W0 := cutoffState.downBatch
  have hwindowLength : out.window.length = actualWindow.length :=
    congrArg List.length hwindow
  have hwindowCanonical : out.window = actualWindow := by
    simpa [out, actualWindow, epoch, w] using hwindow
  let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
    actualWindow[n.val]'(by
      have hnB : n.val < actualWindow.length := by
        rw [← hwindowLength]
        exact Nat.lt_of_lt_of_le n.isLt out.withinWindow
      exact hnB)
  have hrecordCurrent :
      record = out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow) := by
    dsimp [record]
    exact (getElem_congr_coll hwindowCanonical).symm
  let word := CoordinatorLocalArmChoice.storedDownFlatWord out.payload i
  refine ⟨hBlen, cutoffState, cutoffMemory, hcutoff, ?_⟩
  change W0.pending.length < AffineBatchDecoder.quota p ∧
      ∀ hdown : ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time,
        ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
        ∃ choiceMemory : ActiveFollowerLifecycle.LocalMemory p,
        ∃ logged : ReferencePrelaunchFollower.State p rate.eta,
        ∃ cut : ReferenceDownReception.ReferenceDownCutOutput p rate,
          (record.output.preparation.followers.followers i).configuration = .ordinary choice choiceMemory ∧
          choice.status = .unoccupied ∧ (record.output.followers i).downInput = some logged ∧
          (record.output.followers i).down = some cut ∧ logged = choice ∧
          cut.expectedWord = some word ∧ cut.rawComparison.isSome = true ∧
          (∀ hpositive : 0 < (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val,
            (ReferenceFollowerDownDecoderReplay.actualDownPositives i
              (actualWindow.take (n.val + 1))).length =
              AffineBatchDecoder.quota p - W0.pending.length + AffineBatchDecoder.quota p →
            cut.raw = none →
            ∃ first pure : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
              first.length = AffineBatchDecoder.quota p ∧ pure.length = AffineBatchDecoder.quota p ∧
              (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
                (record.output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate choice).1 =
                ⟨[], W0.completed ++ [first, pure]⟩ ∧
              cut.raw = AffineBatchDecoder.batchOutput pure ∧ cut.raw = none ∧
              ∃ other : AffineChannelLaw.Word (AffineBatchDecoder.width p),
                other ≠ word ∧ AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure) word ∧
                AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure) other ∧
              (∀ entry ∈ pure, AffineChannelLaw.affineHash entry.sample word = 1) ∧
              cut.rawComparison = some false ∧
              (∀ entry ∈ pure, s + w ≤ entry.time.val ∧ entry.time.val ≤ record.input.time.val) ∧
              (∀ entry ∈ pure, entry.sample =
                ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
                  entry.time).2 (0, i)) ∧ record.input.time.val = s + w + n.val ∧
              ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
                record.input.time source = some record ∧
              (∃ hs : s < p.T,
                ∃ x : ReferenceGeneratedDownBatchCalendar.LaunchSource
                    rate rewards C_star C_h s hs,
                  x.val = source ∧
                  ∃ N : Fin (p.T - s),
                    N.val = w + n.val ∧
                    (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                      rate rewards C_star C_h s hs x).records[N.val]'(by
                        rw [ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
                          ReferenceActiveHorizonMeasurability.runOfInput,
                          ReferenceActivePhysicalHorizon.run_record_count]
                        exact N.isLt) = record ∧
                    ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
                      ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                        rate rewards C_star C_h s hs i x).2 N)) ∧
              completedDownBatch record i = some pure ∧
              completedAmbiguousAfterStart (s + w) record i ∧
              completedAmbiguousAfterStart s record i ∧
              retainedDecoderRecordFlag (s := s) record = true ∧
              strictPastDecoderFlag rate rewards C_star C_h s
                (record.input.time.val + 1) (by omega) source = true) at ⊢
  rcases hbank with ⟨hbefore, hcollected, hpending, hpendingTime, hcalendar,
    hposchron, hpostime, hsample, hcompleted, hcollectChron, hcollectTime,
    hcompletedFold⟩
  refine ⟨hpending, ?_⟩
  intro hdown
  have hdown' : ActiveFollowerDownAcceptance.downSelected p i
      (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.row
      (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.time := by
    rw [← hrecordCurrent]
    exact hdown
  obtain ⟨choice, choiceMemory, logged, cut, hconfiguration, hstatus,
    hdownInput, hcut, hexpected, hcomparison, hcompare, hLoggedChoice,
    hLoggedBefore, hLoggedFold, hdecode, hpositiveCount⟩ :=
    hcurrent hdown'
  have hlogged : (record.output.followers i).downInput = some logged := by
    rw [hLoggedChoice]
    exact hdownInput
  refine ⟨choice, choiceMemory, logged, cut, hconfiguration, hstatus, hlogged,
    hcut, hLoggedChoice, hexpected, hcomparison, ?_⟩
  intro hpositive hcount hrawNone
  obtain ⟨first, pure, hfirstEq, hpureEq, hfirst, hpure, hstep, hraw,
    hhashWord, hsatisfiesWord, hpureChron, hpureTimes, hpureSamples,
    hrawSomeOrNone⟩ :=
    hpositiveCount hpositive hcount
  rcases hrawSomeOrNone with ⟨hrawWord, _haccepted⟩ |
    ⟨hrawNoneP, other, hotherNe, hother⟩
  · rw [hrawNone] at hrawWord
    contradiction
  rcases hother with ⟨hsatisfiesOther, hcutComparisonFalse⟩
  have htimeAlign := ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
    rate source rewards C_star C_h count hcross hspan hshort
      ⟨n.val, by
        have hnB : n.val < actualWindow.length := by
          rw [← hwindowLength]
          exact Nat.lt_of_lt_of_le n.isLt out.withinWindow
        exact hnB⟩
  have htimeEq : record.input.time.val + 1 = s + w + 1 + n.val := by
    simpa [record, actualWindow, w, epoch, s] using htimeAlign.2.1
  have htime : record.input.time.val = s + w + n.val := by
    omega
  have hpureTimes' : ∀ entry ∈ pure,
      s + w ≤ entry.time.val ∧ entry.time.val ≤ record.input.time.val := by
    intro entry hentry
    have htimes := hpureTimes entry hentry
    have hlo : s + w ≤ entry.time.val := by
      simpa [ReferenceFirstCollectionReadyStream.startTime, s] using htimes.1
    have hhi : entry.time.val ≤ s + w + n.val := by
      simpa [ReferenceFirstCollectionReadyStream.startTime, s] using htimes.2
    exact ⟨hlo, by omega⟩
  have hrecordAlignment : epoch.records[w + n.val]? = some record := by
    simpa [record, actualWindow, w, epoch] using htimeAlign.1
  have hindexRecords : w + n.val < epoch.records.length :=
    (List.getElem?_eq_some_iff.mp hrecordAlignment).1
  have hindex : w + n.val < count := by
    simpa [epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
      ReferenceActivePhysicalHorizon.run_record_count] using hindexRecords
  have hmode := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  have hrunRecord := ReferenceLocalReleaseGateChronology.run_record_at
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
    hmode count hspan ⟨w + n.val, hindex⟩
  have hrecordCanonical : record =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
        (w + n.val) (by omega) hmode := by
    have hget : epoch.records[w + n.val]? =
        some (epoch.records[w + n.val]'(by
          exact hindexRecords)) :=
      List.getElem?_eq_getElem hindexRecords
    have hsame := Option.some.inj (hget.symm.trans hrecordAlignment)
    dsimp only [epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] at hrunRecord
    exact hsame.symm.trans hrunRecord
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
      some (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross) := by
    exact (Option.some_get ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).2 hcross)).symm
  have hphysicalStart : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput, s] using
      (show ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s from rfl)
  have hsourceRecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h record.input.time source
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
    hlaunch (by rw [hphysicalStart]; omega)
  have htimeOffset : record.input.time.val - s = w + n.val := by omega
  have hrecordFromLaunch :
      ReferenceAssignmentPayloadChronology.actualRunRecordAt
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (record.input.time.val - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (by omega) hmode = record := by
    simpa only [hphysicalStart, htimeOffset] using hrecordCanonical.symm
  have hsourceRecordEq :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        record.input.time source = some record := by
    rw [hsourceRecord]
    exact congrArg some hrecordFromLaunch
  have happended : appendedDownBatch record i logged = pure := by
    let trace := ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged)
    let appended := logged.downBatch.pending ++
      AffineBatchDecoder.positiveAt p trace record.input.time
    have helig : AffineBatchDecoder.eligible
        (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged) := by
      have hiff := ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p i
        record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged
      rw [hiff]
      have hstatus' : logged.status = .unoccupied := by
        rw [hLoggedChoice]
        exact hstatus
      have hpositive' : 0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation
          record i).val.val := by
        simpa [ReferenceFollowerDownDecoderReplay.preparedOwnObservation] using hpositive
      exact ⟨hdown, hstatus', hpositive'⟩
    have heligTrace : AffineBatchDecoder.eligible (trace record.input.time) := by
      simpa [trace, ActiveFollowerDownAcceptance.currentInputExtension] using helig
    have hpositiveAt : AffineBatchDecoder.positiveAt p trace record.input.time =
        [AffineBatchDecoder.entry p trace record.input.time] := by
      simp [trace, AffineBatchDecoder.positiveAt, heligTrace]
    have happendedNe : appended ≠ [] := by
      simp [appended, hpositiveAt]
    have happendedLength : appended.length = logged.downBatch.pending.length + 1 := by
      simp [appended, hpositiveAt]
    have hstate : AffineBatchDecoder.step p trace logged.downBatch record.input.time =
        ⟨[], W0.completed ++ [first, pure]⟩ := by
      simpa [trace, record, actualWindow, ActiveFollowerDownAcceptance.currentDecodeStep,
        w, epoch, s, ActiveFollowerDownAcceptance.currentInputExtension,
        ReferenceFollowerDownDecoderReplay.preparedOwnObservation,
        AffineBatchDecoder.decodeStep, hLoggedChoice] using hstep
    have hquota : AffineBatchDecoder.quota p ≤ appended.length := by
      by_contra hnot
      have hlt : appended.length < AffineBatchDecoder.quota p := by omega
      have hsmall : logged.downBatch.pending.length + 1 < AffineBatchDecoder.quota p := by
        omega
      have hpendingEquation := congrArg
        (fun st : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) => st.pending) hstate
      simp [AffineBatchDecoder.step, hpositiveAt, hsmall] at hpendingEquation
    have hcompleted := congrArg
      (fun st : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) => st.completed) hstate
    have hcompletedList : logged.downBatch.completed ++ [appended] = W0.completed ++ [first, pure] := by
      have hnotSmall : ¬ logged.downBatch.pending.length + 1 < AffineBatchDecoder.quota p := by
        omega
      simpa [AffineBatchDecoder.step, appended, hpositiveAt, hnotSmall] using hcompleted
    have hlast := congrArg List.getLast? hcompletedList
    have hlastEq : some appended = some pure := by
      simpa using hlast
    have happendedPure : appended = pure := Option.some.inj hlastEq
    change appended = pure
    exact happendedPure
  have hcompletedDown : completedDownBatch record i = some pure := by
    apply (completedDownBatch_eq_some_iff record i pure).2
    exact ⟨logged, cut, hlogged, hcut, hcomparison,
      (by rw [happended]; exact Nat.le_of_eq hpure.symm), happended⟩
  have hsourceRound :
      ∃ hs : s < p.T,
        ∃ x : ReferenceGeneratedDownBatchCalendar.LaunchSource
            rate rewards C_star C_h s hs,
          x.val = source ∧
          ∃ N : Fin (p.T - s),
            N.val = w + n.val ∧
            (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
              rate rewards C_star C_h s hs x).records[N.val]'(by
                rw [ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
                  ReferenceActiveHorizonMeasurability.runOfInput,
                  ReferenceActivePhysicalHorizon.run_record_count]
                exact N.isLt) = record ∧
            ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
              ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                rate rewards C_star C_h s hs i x).2 N) := by
    have hwindowShort : w < count := by
      simpa [w, epoch] using hshort
    have hs : s < p.T := by omega
    let x : ReferenceGeneratedDownBatchCalendar.LaunchSource
        rate rewards C_star C_h s hs := ⟨source, hcross, rfl⟩
    let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
      rate rewards C_star C_h s hs x
    have hseedSpec := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
      rate rewards C_star C_h s hs x
    have hseed :
        seed =
          ReferenceFirstCollectionEpochAlignment.actualLaunchState
            rate source rewards C_star C_h hcross := by
      exact Option.some.inj (hseedSpec.1.symm.trans hlaunch)
    have hmodeGenerated : ReferenceActivePhysicalHorizon.allActiveAtStart seed s :=
      hseedSpec.2.1
    clear hseedSpec
    have hseedRecord :
        ReferenceAssignmentPayloadChronology.actualRunRecordAt seed source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
          (w + n.val) (by omega) hmodeGenerated =
        ReferenceAssignmentPayloadChronology.actualRunRecordAt
          (ReferenceFirstCollectionEpochAlignment.actualLaunchState
            rate source rewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
          (w + n.val) (by omega) hmode := by
      simpa only [hseed]
    let N : Fin (p.T - s) := ⟨w + n.val, by
      have htime := record.input.time.isLt
      omega⟩
    have hN : N.val = w + n.val := rfl
    have hgeneratedAt := ReferenceLocalReleaseGateChronology.run_record_at
      seed
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
      hmodeGenerated (p.T - s) (by omega) N
    have hgeneratedRecord :
        (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
          rate rewards C_star C_h s hs x).records[N.val]'(by
            rw [ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
              ReferenceActiveHorizonMeasurability.runOfInput,
              ReferenceActivePhysicalHorizon.run_record_count]
            exact N.isLt) = record := by
      calc
        _ = ReferenceAssignmentPayloadChronology.actualRunRecordAt
            seed
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
            N.val (by omega) hmodeGenerated := by
          simpa [ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
            ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput,
            ReferenceActiveHorizonMeasurability.runOfInput] using hgeneratedAt
        _ = ReferenceAssignmentPayloadChronology.actualRunRecordAt
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState
              rate source rewards C_star C_h hcross)
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
            (w + n.val) (by omega) hmode := by
          simpa only [hN] using hseedRecord
        _ = record := hrecordCanonical.symm
    have hcompleteRecord :
        ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) := by
      apply (ReferenceGeneratedDownResetCompletionCensus.completedBatchAtRound_iff_executed_quota
        record i).2
      obtain ⟨logged', cut', hlogged', hcut', hcomparison', hquota', _happended'⟩ :=
        (completedDownBatch_eq_some_iff record i pure).1 hcompletedDown
      exact ⟨logged', cut', hlogged', hcut', hcomparison', hquota'⟩
    let input := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
      rate rewards C_star C_h s hs x
    let observation := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
      rate rewards C_star C_h s hs i x
    have hobsAt : observation.2 N =
        ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i := by
      have hprefixRecord :
          (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input).records[N.val]'(by
            rw [ReferenceActiveHorizonMeasurability.runOfInput,
              ReferenceActivePhysicalHorizon.run_record_count]
            exact N.isLt) =
          (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s N.val (by omega) input,
            ReferenceActivePhysicalStep.step
              (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s N.val (by omega) input), rfl⟩ :
            ReferenceFollowerDownDecoderReplay.Record p rate) := by
        have hrecordsEq := ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn
          s (p.T - s) (by omega) input
        have hrecordElem := getElem_congr_coll
          (c := (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input).records)
          (d := List.ofFn (fun k : Fin (p.T - s) =>
            (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) input,
              ReferenceActivePhysicalStep.step
                (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val (by omega) input), rfl⟩ :
              ReferenceFollowerDownDecoderReplay.Record p rate)))
          (i := N.val)
          (w := by
            rw [ReferenceActiveHorizonMeasurability.runOfInput,
              ReferenceActivePhysicalHorizon.run_record_count]
            exact N.isLt)
          hrecordsEq
        simpa only [List.getElem_ofFn] using hrecordElem
      have hgeneratedRunRecord :
          (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input).records[N.val]'(by
            rw [ReferenceActiveHorizonMeasurability.runOfInput,
              ReferenceActivePhysicalHorizon.run_record_count]
            exact N.isLt) = record := by
        simpa [ReferenceGeneratedDownBatchCalendar.generatedSourceRun] using hgeneratedRecord
      change ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s N.val (by omega) input) i =
        ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i
      have hinputEq := congrArg
        (fun r : ReferenceFollowerDownDecoderReplay.Record p rate => r.input)
        (hprefixRecord.symm.trans hgeneratedRunRecord)
      exact congrArg (fun roundInput =>
        ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation roundInput i) hinputEq
    have hcompleteObservation :
        ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (observation.2 N) := by
      simpa [hobsAt] using hcompleteRecord
    exact ⟨hs, x, rfl, N, hN, hgeneratedRecord, hcompleteObservation⟩
  have hambiguousAfter : completedAmbiguousAfterStart (s + w) record i := by
    refine ⟨pure, hcompletedDown, ?_, ?_⟩
    · intro entry hentry
      simpa [ReferenceFirstCollectionReadyStream.startTime, s, w, epoch] using
        (hpureTimes entry hentry).1
    · apply (multipleSolutions_iff pure).2
      exact ⟨word, other, hsatisfiesWord, hsatisfiesOther, hotherNe.symm⟩
  have hambiguousSince : completedAmbiguousAfterStart s record i := by
    refine ⟨pure, hcompletedDown, ?_, ?_⟩
    · intro entry hentry
      exact le_trans (Nat.le_add_right s w) (by
        simpa [ReferenceFirstCollectionReadyStream.startTime, s, w, epoch] using
          (hpureTimes entry hentry).1)
    · apply (multipleSolutions_iff pure).2
      exact ⟨word, other, hsatisfiesWord, hsatisfiesOther, hotherNe.symm⟩
  have hretained : retainedDecoderRecordFlag s record = true := by
    apply (ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag_eq_true_iff
      (s := s) record).2
    exact Or.inr ⟨i, hambiguousSince⟩
  have hstrict : strictPastDecoderFlag rate rewards C_star C_h s
      (record.input.time.val + 1) (by omega) source = true := by
    apply (ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag_eq_true_iff
      rate rewards C_star C_h s (record.input.time.val + 1) (by omega) source).2
    refine ⟨⟨record.input.time.val, by omega⟩, record, ?_, hretained⟩
    have hfin : (Fin.castLE (by omega : record.input.time.val + 1 ≤ p.T)
        ⟨record.input.time.val, by omega⟩ : Fin p.T) = record.input.time := by
      apply Fin.ext
      rfl
    simpa [hfin] using hsourceRecordEq
  exact ⟨first, pure, hfirst, hpure, hstep, hraw, hrawNoneP,
    other, hotherNe, hsatisfiesWord, hsatisfiesOther, hhashWord,
    hcutComparisonFalse, hpureTimes', hpureSamples, htime, hsourceRecordEq, hsourceRound,
    hcompletedDown,
    hambiguousAfter, hambiguousSince, hretained, hstrict⟩

end Bandits.Support.ReferenceFirstCollectionDownAmbiguityDetector

end
