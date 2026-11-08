/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDownGeneratedPrefix
public import Bandits.Support.ReferenceFirstCollectionDispatchIdentity

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

namespace Bandits.Support.ReferenceFirstCollectionDownAmbiguityEnvelope

variable {p : ConstructorDimensions.Parameters}

/-- The actual cutoff-relative pure DOWN ambiguity remains attached to its
physical detecting record, identified in the generated-source run at that
same round.  The earlier-reset interval and cohort-envelope joins remain for
a later adapter. -/
theorem actual_collection_down_pure_ambiguity_envelope
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
      ∀ (n : Fin out.ell) (_hn : 0 < n.val)
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
             ∀ _hdown : ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time,
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
                 (∀ _hpositive : 0 < (record.output.preparation.feedback.observations
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
                        rate rewards C_star C_h s hs i x).2 N) ∧
                    (let Y := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                        rate rewards C_star C_h s hs x
                     let R := ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                        rate rewards C_star C_h s hs x
                     let O := ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                        rate rewards C_star C_h s hs i x
                     let K := fun k : Fin (p.T - s) =>
                       (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val
                           (by omega) Y,
                         ReferenceActivePhysicalStep.step
                           (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val
                             (by omega) Y), rfl⟩ :
                         ReferenceFollowerDownDecoderReplay.Record p rate)
                     let Comp := fun k : Fin (p.T - s) =>
                       ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate (O.2 k)
                     K N = record ∧
                     ∃ m : Fin (p.T - s),
                       ∃ hmn : m < N,
                         Comp m ∧
                       (∀ k : Fin (p.T - s), k < N → Comp k → k ≤ m) ∧
                       (∀ k : Fin (p.T - s), m < k → k < N → ¬ Comp k) ∧
                       (∀ m' : Fin (p.T - s), m' < N → Comp m' →
                         (∀ k : Fin (p.T - s), k < N → Comp k → k ≤ m') → m' = m) ∧
                       (let a := m.val + 1
                        let alpha := s + a
                        s < alpha ∧ alpha ≤ s + N.val ∧ alpha < p.T ∧
                        ReferenceGeneratedDownBatchCalendar.generatedSourceBatchBoundary
                          rate rewards C_star C_h s hs i alpha (by omega) (by omega) x ∧
                        ∃ resetState : ReferencePrelaunchFollower.State p rate.eta,
                          ∃ resetMemory : ActiveFollowerLifecycle.LocalMemory p,
                            (ReferenceActiveHorizonMeasurability.runOfInput s a (by omega) Y).finalState.followers i =
                              .ordinary resetState resetMemory ∧
                            resetState.downBatch.pending = [] ∧
                        let tests := ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
                          rate rewards C_star C_h s hs i alpha x
                        let Tests := fun (a b : ℕ) =>
                          ((R.records.take b).drop a).filterMap (fun r =>
                            ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
                              (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
                                r.input i))
                        ∃ testN : ReferenceGeneratedDownBatchCalendar.ExecutedTest p,
                          tests = Tests a N.val ++ [testN] ∧
                          Tests a N.val ++ [testN] = Tests a (N.val + 1) ∧
                          tests.length = AffineBatchDecoder.quota p ∧
                          (Tests a N.val).length = AffineBatchDecoder.quota p - 1 ∧
                          tests.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
                          tests.map ReferenceGeneratedDownPrefixList.stampedTest = pure ∧
                          (∀ test ∈ tests,
                            test.sent = some word ∧
                            AffineChannelLaw.affineHash test.sample other = 1) ∧
                          ReferenceGeneratedDownBatchCalendar.generatedDownD
                            rate rewards C_star C_h s (AffineBatchDecoder.quota p) hs i alpha
                            (by omega) (by omega) other x ∧
                          x.val ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
                            rate rewards C_star C_h control0 (AffineBatchDecoder.quota p))) ∧
                     completedDownBatch record i = some pure ∧
                     completedAmbiguousAfterStart (s + w) record i ∧
                     completedAmbiguousAfterStart s record i ∧
                     retainedDecoderRecordFlag (s := s) record = true ∧
                     strictPastDecoderFlag rate rewards C_star C_h s
                       (record.input.time.val + 1) (by omega) source = true))) := by
  classical
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
  have hA := ReferenceFirstCollectionDownAmbiguityDetector.actual_collection_down_pure_ambiguity_detector
    rate source rewards C_star C_h count hcross hspan hshort control0
  dsimp only at hA
  rcases hA with ⟨dA, hwindowA, hpostA⟩
  have hP := ReferenceFirstCollectionDownSecondPureBank.actual_collection_unaccepted_down_second_pure_bank
    rate source rewards C_star C_h count hcross hspan hshort
  dsimp only at hP
  rcases hP with ⟨dP, hPbody⟩
  rcases hPbody with ⟨hwindowP, hPstart, hPdownRecords, hPprefix⟩
  have hJ := ReferenceFirstCollectionDispatchIdentity.actual_initialized_collection_dispatch_observables
    rate source rewards C_star C_h count hcross hspan hshort dA dP
  rcases hJ with ⟨hwindowDP, hpayloadDP, _hsavedDP, hellDP, _hledgersDP,
    _hcutDP, _hcutPayloadDP, _hcutLedgerDP, _hcutSavedDP, _hlastDP,
    _hledgerDP, _hrecordDP⟩
  have hG := ReferenceFirstCollectionDownGeneratedPrefix.actual_collection_down_generated_prefix
    rate source rewards C_star C_h count hcross hspan hshort
  dsimp only at hG
  rcases hG with ⟨hsG, xG, hxG, hseedG, hGbody⟩
  rcases hGbody with ⟨hGprefix, hGnext⟩
  refine ⟨dA, hwindowA, ?_⟩
  let out := dA.stream
  intro n hn i before memory hfi hnone
  obtain ⟨hBlen, cutoffState, cutoffMemory, hcutoff, hbank, hcurrent⟩ :=
    hpostA n hn i before memory hfi hnone
  refine ⟨hBlen, cutoffState, cutoffMemory, hcutoff, hbank, ?_⟩
  intro hdown
  rcases hcurrent hdown with ⟨choice, choiceMemory, logged, cut,
    hconfiguration, hstatus, hdownInput, hcut, hloggedChoice, hexpected,
    hcomparison, hpositiveCount⟩
  refine ⟨choice, choiceMemory, logged, cut, hconfiguration, hstatus,
    hdownInput, hcut, hloggedChoice, hexpected, hcomparison, ?_⟩
  intro hpositive hcount hrawNone
  rcases hpositiveCount hpositive hcount hrawNone with
    ⟨first, pure, hfirst, hpure, hstep, hraw, hrawNone', other, hotherNe,
      hsolvesWord, hsolvesOther, hhashWord, hcomparisonFalse, hpureTimes,
      hpureSamples, htime, hactualRecord, hsourceRound, hcompletedDown,
      hambiguousWindow, hambiguousStart, hretained, hstrict⟩
  rcases hsourceRound with ⟨hsA, xA, hxA, NA, hNA, hrecordA, hcompleteA⟩
  have hnB : n.val < B.length := by
    have hnWindow : n.val < out.window.length :=
      Nat.lt_of_lt_of_le n.isLt out.withinWindow
    have hlen : out.window.length = B.length := congrArg List.length hwindowA
    omega
  let nB : Fin B.length := ⟨n.val, hnB⟩
  rcases hGnext nB with
    ⟨NG, hNG, hK, hKtime, hprefixN, hprefixN1, hfori⟩
  rcases hfori i with ⟨htestProvenance, hstrictMap⟩
  have hxEq : xG = xA := by
    apply Subtype.ext
    exact hxG.trans hxA.symm
  subst xG
  have hNEq : NG = NA := by
    apply Fin.ext
    rw [hNG, hNA]
  have hsEq : hsG = hsA := Subsingleton.elim _ _
  subst hsG
  subst NG
  have hwindowRecord :
      out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow) =
        B[n.val]'hnB := by
    exact getElem_congr_coll hwindowA
  have hfiB : (B[nB.val]'nB.isLt).input.state.followers i =
      .ordinary before memory := by
    have hfi' := hfi
    rw [hwindowRecord] at hfi'
    simpa [nB] using hfi'
  rcases hstrictMap before memory hfiB with ⟨_hmapTests, _hmapInherited, hcountBound⟩
  refine ⟨first, pure, ?_⟩
  refine ⟨hfirst, hpure, hstep, hraw, hrawNone', ?_⟩
  refine ⟨other, ?_⟩
  refine ⟨hotherNe, hsolvesWord, hsolvesOther, hhashWord,
    hcomparisonFalse, hpureTimes, hpureSamples, htime, hactualRecord, ?_⟩
  refine ⟨hsA, ?_⟩
  refine ⟨xA, ?_⟩
  refine ⟨hxA, ?_⟩
  refine ⟨NA, ?_⟩
  refine ⟨hNA, hrecordA, hcompleteA, ?_⟩
  let Ylocal := ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
    rate rewards C_star C_h s hsA xA
  let Klocal := fun k : Fin (p.T - s) =>
    (⟨ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val
        (by omega) Ylocal,
      ReferenceActivePhysicalStep.step
        (ReferenceDownCompletedAmbiguityMeasurability.prefixInput s k.val
          (by omega) Ylocal), rfl⟩ : ReferenceFollowerDownDecoderReplay.Record p rate)
  let recordLocal : ReferenceFollowerDownDecoderReplay.Record p rate :=
    B[n.val]'(by
      have hn : n.val < B.length := hnB
      exact hn)
  have hKrecord : Klocal NA = recordLocal := by
    simpa [Klocal, nB, recordLocal] using hK
  constructor
  ·
    dsimp only
    constructor
    · exact hKrecord
    ·
      have hW0lt : cutoffState.downBatch.pending.length < AffineBatchDecoder.quota p := hbank
      have hUge :
          (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
            rate rewards C_star C_h s hsA i xA NA.val).length ≥ AffineBatchDecoder.quota p := by
        change (ReferenceFollowerDownDecoderReplay.actualDownPositives i
            (B.take (nB.val + 1))).length ≤
          (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
            rate rewards C_star C_h s hsA i xA NA.val).length + 1 at hcountBound
        have hcountAligned :
            (ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take (nB.val + 1))).length =
              AffineBatchDecoder.quota p - cutoffState.downBatch.pending.length +
                AffineBatchDecoder.quota p := by
          simpa [nB] using hcount
        omega
      have hL := ReferenceGeneratedDownLaterCompletionDetector.generated_down_later_completion_detector_of_good
        rate rewards C_star C_h s hsA xA i NA other control0 hcompleteA
      dsimp only at hL
      rcases hL with hnoEarlier | ⟨m, hmn, hcompm, hgreatest, hnoMiddle,
        hunique, hlater⟩
      · have hfirstIff :=
          ReferenceGeneratedInheritedDownFirstCompletion.generated_inherited_down_first_completion_iff
            rewards C_star C_h s hsA xA i NA.val NA.isLt
        have hfirst :
            ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
                ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                  rate rewards C_star C_h s hsA i xA).2 NA) ∧
              ∀ l (hl : l < NA.val),
                ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
                  ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
                    rate rewards C_star C_h s hsA i xA).2 ⟨l, Nat.lt_trans hl NA.isLt⟩) := by
          refine ⟨hcompleteA, ?_⟩
          intro l hl
          exact hnoEarlier ⟨l, by omega⟩ (Fin.mk_lt_mk.mpr hl)
        have hfirstCount := hfirstIff.mp hfirst
        have hcountSize :
            (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
              rate rewards C_star C_h s hsA i xA NA.val).length =
              AffineBatchDecoder.quota p -
                (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
                  rate rewards C_star C_h s hsA xA i).downBatch.pending.length - 1 :=
          hfirstCount.1
        have hinitial := ReferenceGeneratedInheritedDownCompletion.generated_inherited_down_initial_residual
          rate rewards C_star C_h s hsA xA i
        dsimp only at hinitial
        have hsmall :
            (ReferenceGeneratedInheritedDownCompletion.generatedInheritedDownTests
              rate rewards C_star C_h s hsA i xA NA.val).length < AffineBatchDecoder.quota p := by
          omega
        omega
      · have hinterval :=
          ReferenceGeneratedDownCompletionTestInterval.generated_down_completion_test_interval
            rate rewards C_star C_h s hsA xA i NA hcompleteA
        dsimp only at hinterval
        rcases hinterval with hintervalFirst | ⟨mI, hmnI, hcompI, hgreatestI,
          hnoMiddleI, huniqueI, hintervalLater⟩
        · exact False.elim (hintervalFirst m hmn hcompm)
        · have hmEq : mI = m := hunique mI hmnI hcompI hgreatestI
          subst mI
          rcases hlater with ⟨halpha, halphaN, _hspanN, halphaT, hboundary,
            callCodeN, loggedN, cutN, testN, hcallN, hactualN, hloggedN,
            hcutN, hcomparisonN, hpositiveN, hquotaN, htestN, hlistL⟩
          rcases hlistL with ⟨hlistA, hlistB, hlength, hlengthBefore,
            hbankL, hrawL, hchronL, hprovenanceL, hfinalL⟩
          have hloggedN' :
              (recordLocal.output.followers i).downInput = some loggedN := by
            have hloggedN'' := hloggedN
            change ((Klocal NA).output.followers i).downInput = some loggedN at hloggedN''
            rw [hKrecord] at hloggedN''
            exact hloggedN''
          have hcutN' : (recordLocal.output.followers i).down = some cutN := by
            have hcutN'' := hcutN
            change ((Klocal NA).output.followers i).down = some cutN at hcutN''
            rw [hKrecord] at hcutN''
            exact hcutN''
          have hcompletedDownLocal : completedDownBatch recordLocal i = some pure := by
            simpa [recordLocal] using hcompletedDown
          rcases (ReferenceFirstLiveDownCompletionReadout.completedDownBatch_eq_some_iff
              recordLocal i pure).mp hcompletedDownLocal with
            ⟨loggedA, cutA, hloggedA, hcutA, hcomparisonA, hquotaA, happended⟩
          have hloggedEqA : loggedA = logged :=
            Option.some.inj (hloggedA.symm.trans hdownInput)
          have hloggedEqN : loggedN = loggedA :=
            Option.some.inj (hloggedN'.symm.trans hloggedA)
          have hcutEq : cutN = cutA := Option.some.inj (hcutN'.symm.trans hcutA)
          have hactualN' :
              ReferenceFollowerDownDecoderReplay.actualDownCall i recordLocal =
                some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN) := by
            have hactualN'' := hactualN
            change ReferenceFollowerDownDecoderReplay.actualDownCall i (Klocal NA) =
              some (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN) at hactualN''
            rw [hKrecord] at hactualN''
            exact hactualN''
          have hcallFields :=
            ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
              recordLocal i _ hactualN'
          have hdownA : ActiveFollowerDownAcceptance.downSelected p i
              recordLocal.input.row recordLocal.input.time := by
            simpa [recordLocal] using hdown
          have hstatusA : loggedA.status = .unoccupied := by
            rw [hloggedEqA, hloggedChoice]
            exact hstatus
          have hpositiveA :
              0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation recordLocal i).val.val := by
            simpa [ReferenceFollowerDownDecoderReplay.preparedOwnObservation, recordLocal] using hpositive
          have heligibleA : AffineBatchDecoder.eligible
              (ActiveFollowerDownAcceptance.currentRoundInput p i recordLocal.input.row
                recordLocal.input.time
                (ReferenceFollowerDownDecoderReplay.preparedOwnObservation recordLocal i)
                rate loggedA) :=
            (ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p i recordLocal.input.row
              recordLocal.input.time
              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation recordLocal i)
              rate loggedA).2 ⟨hdownA, hstatusA, hpositiveA⟩
          have hBnAppend :
              loggedN.downBatch.pending ++
                  [⟨(Klocal NA).input.time,
                    (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN).2.sample⟩] =
                ReferenceFirstLiveDownCompletionReadout.appendedDownBatch recordLocal i loggedA := by
            rw [hloggedEqN]
            simp [ReferenceFirstLiveDownCompletionReadout.appendedDownBatch,
              ReferenceFollowerDownDecoderReplay.preparedOwnObservation,
              ActiveFollowerDownAcceptance.currentInputExtension,
              ActiveFollowerDownAcceptance.currentRoundInput,
              AffineBatchDecoder.positiveAt, AffineBatchDecoder.entry,
              hKrecord, hcallFields.2.1]
            exact heligibleA
          have hbankL' :
              loggedN.downBatch.pending ++
                  [⟨(Klocal NA).input.time,
                    (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN).2.sample⟩] =
                (ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
                  rate rewards C_star C_h s hsA i (s + (m.val + 1)) xA).map
                    ReferenceGeneratedDownPrefixList.stampedTest := by
            simpa [Klocal] using hbankL
          have hmapPure :
              (ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
                rate rewards C_star C_h s hsA i (s + (m.val + 1)) xA).map
                  ReferenceGeneratedDownPrefixList.stampedTest = pure := by
            calc
              _ = loggedN.downBatch.pending ++
                  [⟨(Klocal NA).input.time,
                    (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCodeN).2.sample⟩] :=
                hbankL'.symm
              _ = ReferenceFirstLiveDownCompletionReadout.appendedDownBatch recordLocal i loggedA :=
                hBnAppend
              _ = pure := happended
          have hwindowP : dP.stream.window = B := hwindowDP.symm.trans hwindowA
          have hnPBound : n.val < dP.stream.ell := by
            rw [← hellDP]
            exact n.isLt
          let nP : Fin dP.stream.ell := ⟨n.val, hnPBound⟩
          have hwindowPRecord :
              dP.stream.window[nP.val]'(Nat.lt_of_lt_of_le nP.isLt dP.stream.withinWindow) =
                B[nB.val]'nB.isLt := by
            exact getElem_congr_coll hwindowP
          have hfiP :
              (dP.stream.window[nP.val]'(Nat.lt_of_lt_of_le nP.isLt dP.stream.withinWindow)).input.state.followers i =
                .ordinary before memory := by
            rw [hwindowPRecord]
            exact hfiB
          have hnPPositive : 0 < nP.val := by simpa [nP] using hn
          rcases hPprefix nP hnPPositive i before memory hfiP hnone with
            ⟨hpriorP, _hcutoffP⟩
          have hRrecords :
              (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                rate rewards C_star C_h s hsA xA).records = List.ofFn Klocal := by
            simpa [ReferenceGeneratedDownBatchCalendar.generatedSourceRun, Klocal] using
              ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn
                (p := p) (rate := rate) s (p.T - s) (by omega) Ylocal
          have hgood : ∀ test,
              test ∈ ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
                rate rewards C_star C_h s hsA i (s + (m.val + 1)) xA →
              test.sent = some (CoordinatorLocalArmChoice.storedDownFlatWord dA.stream.payload i) ∧
                AffineChannelLaw.affineHash test.sample other = 1 := by
            intro test htest
            have hstampMem :
                ReferenceGeneratedDownPrefixList.stampedTest test ∈ pure := by
              rw [← hmapPure]
              exact List.mem_map.mpr ⟨test, htest, rfl⟩
            have hstampTimes := hpureTimes _ hstampMem
            have htestTimeLower : s + w ≤ test.time.val := by
              simpa [ReferenceGeneratedDownPrefixList.stampedTest] using hstampTimes.1
            rcases hprovenanceL test htest with
              ⟨k, hka, hkN, hexecuted, htimeK, _hsampleK, hsentK, hcallK⟩
            have hKtime : (Klocal k).input.time.val = s + k.val := by
              simp [Klocal, ReferenceDownCompletedAmbiguityMeasurability.prefixInput,
                ReferenceActivePhysicalHorizon.roundInputAt]
            have hkLower : w ≤ k.val := by
              rw [htimeK, hKtime] at htestTimeLower
              omega
            let jval := k.val - w
            have hjle : jval ≤ n.val := by
              have hkN' : k.val ≤ w + n.val := by simpa [hNA] using hkN
              dsimp [jval]
              omega
            let jB : Fin (n.val + 1) := ⟨jval, by omega⟩
            let Rlocal := ReferenceGeneratedDownBatchCalendar.generatedSourceRun
              rate rewards C_star C_h s hsA xA
            have hRlocal : Rlocal.records = List.ofFn Klocal := by
              dsimp [Rlocal]
              exact hRrecords
            have hRlen : Rlocal.records.length = p.T - s := by
              rw [hRlocal]
              simp
            have hKmem : Klocal k ∈
                ((Rlocal.records.take (NA.val + 1)).drop w) := by
              have hbound : jval <
                  (((Rlocal.records.take (NA.val + 1)).drop w).length) := by
                simp only [List.length_drop, List.length_take]
                rw [hRlen]
                simp only [Nat.min_eq_left (show NA.val + 1 ≤ p.T - s by omega)]
                dsimp [jval]
                omega
              have hgetDrop :
                  ((Rlocal.records.take (NA.val + 1)).drop w)[jval]'hbound = Klocal k := by
                have hind : w + jval = k.val := by
                  dsimp [jval]
                  omega
                have hFin : (⟨w + jval,
                    by rw [hind]; exact k.isLt⟩ : Fin (p.T - s)) = k := by
                  apply Fin.ext
                  exact hind
                simp only [hRlocal, List.getElem_drop, List.getElem_take,
                  List.getElem_ofFn]
                exact congrArg Klocal hFin
              exact List.mem_iff_getElem.mpr ⟨jval, hbound, hgetDrop⟩
            have hexecutedK :
                ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
                  (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
                    (Klocal k).input i) = some test := by
              simpa [ReferenceGeneratedDownBatchCalendar.generatedSourceObservation,
                ReferenceDownCompletedAmbiguityMeasurability.runDownObservation, Klocal] using
                hexecuted
            have htestWindow : test ∈
                (((ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                  rate rewards C_star C_h s hsA xA).records.take (NA.val + 1)).drop w).filterMap
                    (fun r => ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
                      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation r.input i)) := by
              apply List.mem_filterMap.mpr
              exact ⟨Klocal k, hKmem, hexecutedK⟩
            rcases htestProvenance test htestWindow with
              ⟨j, kG, hkG, hKG, hexecutedG, htimeG, _hsampleG, hsentG, hcallG⟩
            have hjB : j.val < B.length := by omega
            have hjP : j.val < dP.stream.window.length := by
              rw [hwindowP]
              exact hjB
            have hwindowPRecordJ :
                dP.stream.window[j.val]'hjP = B[j.val]'hjB := by
              exact getElem_congr_coll hwindowP
            rcases hcallG with ⟨callG, hactualG, hEligibleG⟩
            have hcallFieldsG :=
              ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
                (Klocal kG) i callG hactualG
            have hselectedG : ActiveFollowerDownAcceptance.downSelected p i
                (Klocal kG).input.row (Klocal kG).input.time := by
              exact (hcallFieldsG.2.2).mp hEligibleG.1
            have hKGlocal : Klocal kG = B[j.val]'hjB := by
              simpa [Klocal] using hKG
            have hselectedB : ActiveFollowerDownAcceptance.downSelected p i
                (B[j.val]'hjB).input.row (B[j.val]'hjB).input.time := by
              simpa only [← hKGlocal] using hselectedG
            rcases hpriorP j with
              ⟨prior, priorMemory, _hpriorState, _hpriorNone, hselectedP⟩
            have hselectedP' : ActiveFollowerDownAcceptance.downSelected p i
                (dP.stream.window[j.val]'hjP).input.row
                (dP.stream.window[j.val]'hjP).input.time := by
              simpa only [hwindowPRecordJ] using hselectedB
            rcases hselectedP hselectedP' with
              ⟨selectedP, choiceP, choiceMemoryP, _hselectionP, _hpayloadP,
                _hpendingP, hsentP, _hrestP⟩
            have hsentPB :
                ReferenceActiveAffinePositiveTest.downSent (B[j.val]'hjB).input =
                  some (CoordinatorLocalArmChoice.storedDownFlatWord dP.stream.payload i) := by
              simpa only [hwindowPRecordJ] using hsentP
            have hsentPOnK' :
                ReferenceActiveAffinePositiveTest.downSent (Klocal kG).input =
                  some (CoordinatorLocalArmChoice.storedDownFlatWord dP.stream.payload i) := by
              simpa only [← hKGlocal] using hsentPB
            have hsentWord : test.sent =
                some (CoordinatorLocalArmChoice.storedDownFlatWord dA.stream.payload i) := by
              have hsentGLocal : test.sent =
                  ReferenceActiveAffinePositiveTest.downSent (Klocal kG).input := by
                simpa [Klocal, Ylocal] using hsentG
              rw [hsentGLocal, hsentPOnK', hpayloadDP.symm]
            have hequation :=
              (AffineBatchDecoder.satisfies_samples_iff pure other).mp hsolvesOther
                (ReferenceGeneratedDownPrefixList.stampedTest test) hstampMem
            have hequationSample : AffineBatchDecoder.equation test.sample other := by
              simpa [ReferenceGeneratedDownPrefixList.stampedTest] using hequation
            have hhash : AffineChannelLaw.affineHash test.sample other = 1 :=
              (AffineBatchDecoder.equation_iff_affineHash test.sample other).mp hequationSample
            exact ⟨hsentWord, hhash⟩
          have hgoodForL : ∀ test,
              test ∈ ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
                rate rewards C_star C_h s hsA i (s + (m.val + 1)) xA →
              ReferenceGeneratedDownBatchCalendar.ExecutedTest.good other test := by
            intro test htest
            have hpair := hgood test htest
            refine ⟨?_, hpair.2⟩
            intro hsentOther
            apply hotherNe
            exact (Option.some.inj (hpair.1.symm.trans hsentOther)).symm
          rcases hintervalLater with ⟨halphaI, halphaNI, halphaTI,
            hboundaryI, hafterReset⟩
          rcases hafterReset with ⟨resetState, resetMemory, callCodeM, loggedM,
            cutM, hresetOrdinary, hresetPending, _hcallM, _hactualM, _hloggedM,
            _hcutM, _hcomparisonM, _hpositiveM, _hquotaM, _hbatchM, hthroughN⟩
          rcases hthroughN with ⟨stateN, memoryN, callCodeNI, loggedNI, cutNI,
            testNI, _hordinaryN, _hcompletedN, _hpendingN, _hloggedBankN,
            _hcountBeforeN, _hcallNI, _hactualNI, _hloggedNI, _hcutNI,
            _hcomparisonNI, _hpositiveNI, _hquotaNI, _htestNI, _hlistFactsI⟩
          refine ⟨m, hmn, hcompm, hgreatest, hnoMiddle, hunique, ?_⟩
          refine ⟨halphaI, halphaNI, halphaTI, hboundaryI,
            resetState, resetMemory, hresetOrdinary, hresetPending, ?_⟩
          ·
            have hgoodAdjusted : ∀ test,
                test ∈ ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
                  rate rewards C_star C_h s hsA i
                    (ReferenceInitializationRun.elapsed p
                      (ReferenceInitializationRun.output
                        (ActualReferenceInitializationBlock.referenceInput
                          source rewards C_star C_h rate)).completed + (m.val + 1)) xA →
                ReferenceGeneratedDownBatchCalendar.ExecutedTest.good other test := by
              simpa [s, Nat.add_assoc] using hgoodForL
            rcases hfinalL hgoodAdjusted with ⟨hdetector, hmembership⟩
            refine ⟨testN, ?_⟩
            exact ⟨hlistA, hlistB, hlength, hlengthBefore, hchronL,
              hmapPure, hgood, hdetector, hmembership⟩
  · exact ⟨hcompletedDown, hambiguousWindow, hambiguousStart, hretained, hstrict⟩

end Bandits.Support.ReferenceFirstCollectionDownAmbiguityEnvelope
