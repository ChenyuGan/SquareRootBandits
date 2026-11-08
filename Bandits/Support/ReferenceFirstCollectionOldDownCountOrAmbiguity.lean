/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDownPhysicalThresholdJoin
public import Bandits.Support.ReferenceFirstCollectionDownThresholdAttainment
public import Bandits.Support.ReferenceFirstCollectionDownAmbiguityEnvelope

import Lean.Elab.Tactic.Omega

/-!
# First-collection OLD DOWN count or earlier real ambiguity

The actual first attaining positive uses the same initialized payload, cutoff
bank and physical callback. Acceptance contradicts the later ordinary OLD
endpoint by chronology of the original prefix. The remaining branch is the
actual completed pure-bank ambiguity in the existing source cohort event.

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`sources/zip4/manuscript/05_binary_transport.tex:27-55,100-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceFollowerDownDecoderReplay

namespace Bandits.Support.ReferenceFirstCollectionOldDownCountOrAmbiguity

variable {p : ConstructorDimensions.Parameters}

/-- The literal returned DOWN decoder bank on this retained physical
record and its actual logged local state. -/
def actualDownBankAfter
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceCollectionPhaseHistory.Record p rate)
    (i : Fin (p.m - 1)) (logged : ReferencePrelaunchFollower.State p rate.eta) :
    AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) :=
  (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
    (ReferenceFirstCollectionDownPhysicalThresholdJoin.localObservation record i) rate logged).1

private theorem actualDownBankAfter_of_physical_step
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceCollectionPhaseHistory.Record p rate) (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hstep : (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row
      record.input.time (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).1 = bank) :
    actualDownBankAfter record i logged = bank := by
  exact hstep

private theorem accepted_record_forces_nonold_connected_endpoint
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (sigma : ℕ)
    {suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    {final : ReferenceActivePhysicalStep.State p rate}
    (hconnected : ReferenceActivePhysicalHorizon.Connected record.output.next suffix final)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hnext : record.output.next.followers i = .ordinary next nextMemory)
    (last : ReferencePrelaunchFollower.State p rate.eta)
    (lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfinal : final.followers i = .ordinary last lastMemory)
    (hlast : last.lastDown = none)
    (haccepted : ReferenceFollowerReplyChronology.appliedDown record i sigma) : False := by
  obtain ⟨first, firstMemory, hfirst, hmono, -, -⟩ :=
    ReferenceFollowerReplyChronology.connected_ordinary_chronology
      hconnected i last lastMemory hfinal
  have hsame := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hfirst.symm.trans hnext)
  rcases hsame with ⟨rfl, rfl⟩
  obtain ⟨_choice, _choiceMemory, -, hstrict, hsigma⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict
      record i sigma haccepted first firstMemory hnext
  have hlastStart : ReferencePrelaunchFollower.acceptedStart last = 0 := by
    simp [ReferencePrelaunchFollower.acceptedStart, hlast]
  omega

/-- An actual accepted record cannot precede an ordinary OLD endpoint of
that same computed prefix. The OLD prepared state comes from its real input. -/
private theorem accepted_record_forces_nonold_prefix_endpoint
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (record : ReferenceCollectionPhaseHistory.Record p rate)
    (i : Fin (p.m - 1)) (sigma n : ℕ) (hn : n ≤ total)
    (hnSpan : start + n ≤ p.T)
    (current : ReferencePrelaunchFollower.State p rate.eta)
    (currentMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared : (ReferenceFirstCollectionDownPhysicalThresholdJoin.localPrepared
      record i).configuration = .ordinary current currentMemory)
    (hcurrent : current.lastDown = none)
    (next last : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hprefix : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start n hnSpan active).finalState = record.output.next)
    (hnext : record.output.next.followers i = .ordinary next nextMemory)
    (hlast : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start total hspan active).finalState.followers i = .ordinary last lastMemory)
    (hnone : last.lastDown = none)
    (haccepted : ReferenceFollowerReplyChronology.appliedDown record i sigma) : False := by
  obtain ⟨choice, choiceMemory, hchoice, hstrict, hsigma⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict
      record i sigma haccepted next nextMemory hnext
  have hchoiceSame : choice = current :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hchoice.symm.trans hprepared)).1
  have hchoiceZero : ReferencePrelaunchFollower.acceptedStart choice = 0 := by
    rw [hchoiceSame]
    simp only [ReferencePrelaunchFollower.acceptedStart, hcurrent]
  have hprefixNext : (ReferenceActivePhysicalHorizon.run initial rows selected
      rewards start n hnSpan active).finalState.followers i = .ordinary next nextMemory :=
    (congrArg (fun state => state.followers i) hprefix).trans hnext
  have hmono := (ReferenceFollowerReplyChronology.run_prefix_final_chronology
    initial rows selected rewards start total hspan active n hn i next last
    nextMemory lastMemory hprefixNext hlast).1
  have hlastZero : ReferencePrelaunchFollower.acceptedStart last = 0 := by
    simp only [ReferencePrelaunchFollower.acceptedStart, hnone]
  omega

/-- At an ordinary OLD endpoint, a real retained cut cannot have taken its
accepted branch earlier in the same original prefix. -/
private theorem cut_none_of_old_prefix
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (record : ReferenceCollectionPhaseHistory.Record p rate)
    (i : Fin (p.m - 1)) (n : ℕ) (hn : n ≤ total) (hnSpan : start + n ≤ p.T)
    (current : ReferencePrelaunchFollower.State p rate.eta)
    (currentMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared : (ReferenceFirstCollectionDownPhysicalThresholdJoin.localPrepared
      record i).configuration = .ordinary current currentMemory)
    (hcurrent : current.lastDown = none)
    (next last : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory lastMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hprefix : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start n hnSpan active).finalState = record.output.next)
    (hnext : record.output.next.followers i = .ordinary next nextMemory)
    (hlast : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start total hspan active).finalState.followers i = .ordinary last lastMemory)
    (hnone : last.lastDown = none)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (message : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hinput : (record.output.followers i).downInput = some logged)
    (hcut : (record.output.followers i).down = some cut)
    (hcases : (∃ after scan registers lastService,
      cut.outcome = ActiveFollowerDownAcceptance.LocalDownResult.accepted
        logged after raw message scan registers lastService) ∨ cut.raw = none) :
    cut.raw = none := by
  rcases hcases with ⟨after, scan, registers, lastService, haccepted⟩ | hnoneCut
  · have happlied : ReferenceFollowerReplyChronology.appliedDown record i message.val.sigma :=
      ⟨logged, cut, after, raw, message, scan, registers, lastService,
        hinput, hcut, haccepted, rfl⟩
    exact (accepted_record_forces_nonold_prefix_endpoint initial rows selected rewards
      start total hspan active record i message.val.sigma n hn hnSpan current currentMemory
      hprepared hcurrent next last nextMemory lastMemory hprefix hnext hlast hnone happlied).elim
  · exact hnoneCut

private theorem physical_result_of_record_eq
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (left right : ReferenceCollectionPhaseHistory.Record p rate) (heq : left = right)
    (i : Fin (p.m - 1)) (before after : ReferencePrelaunchFollower.State p rate.eta)
    (hresult : (ReferenceFirstCollectionDownPhysicalThresholdJoin.localPhysicalCall
      left i before).result = .ok after) :
    (ReferenceFirstCollectionDownPhysicalThresholdJoin.localPhysicalCall
      right i before).result = .ok after := by
  cases heq
  exact hresult

/-- Read the actual pure-bank ambiguity from the admitted envelope after
identifying its whole physical record and logged cut with the caller's. -/
private theorem ambiguity_after_actual_cut
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch
        (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count)
    (control0 : ContinuousLearningRows.TimeControl p)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
    let s := ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h
    let epoch := ReferenceFirstCollectionReadyStream.actualEpoch
      (rate := rate) source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let B := ReferenceFirstCollectionReadyStream.actualWindow
      (rate := rate) source rewards C_star C_h hcross count hspan
    let Q := AffineBatchDecoder.quota p
    ∀ (i : Fin (p.m - 1)) (k : Fin d.stream.ell) (_hkpos : 0 < k.val)
      (hkB : k.val < B.length) (hBlen : 0 < B.length)
      (cutoffState : ReferencePrelaunchFollower.State p rate.eta)
      (cutoffMemory : ActiveFollowerLifecycle.LocalMemory p),
      (B[0]'hBlen).input.state.followers i = .ordinary cutoffState cutoffMemory →
    let W0 := cutoffState.downBatch
    let q := Q - W0.pending.length + Q
    let record := B[k.val]'hkB
    ∀ (current : ReferencePrelaunchFollower.State p rate.eta)
      (currentMemory : ActiveFollowerLifecycle.LocalMemory p),
      record.input.state.followers i = .ordinary current currentMemory →
      current.lastDown = none →
      ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time →
      0 < (ReferenceFirstCollectionDownPhysicalThresholdJoin.localObservation record i).val.val →
      (actualDownPositives i (B.take (k.val + 1))).length = q →
    ∀ (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (post : ReferencePrelaunchFollower.State p rate.eta),
      (record.output.followers i).downInput = some logged →
      (record.output.followers i).down = some cut →
      cut.raw = none →
      post.downBatch = actualDownBankAfter record i logged →
    ∃ first pure : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
      first.length = Q ∧ pure.length = Q ∧
      actualDownBankAfter record i logged = ⟨[], W0.completed ++ [first, pure]⟩ ∧
      post.downBatch = ⟨[], W0.completed ++ [first, pure]⟩ ∧
      cut.raw = AffineBatchDecoder.batchOutput pure ∧ cut.raw = none ∧
      cut.rawComparison = some false ∧
    ∃ other : AffineChannelLaw.Word (AffineBatchDecoder.width p),
      other ≠ CoordinatorLocalArmChoice.storedDownFlatWord d.stream.payload i ∧
      AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure)
        (CoordinatorLocalArmChoice.storedDownFlatWord d.stream.payload i) ∧
      AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure) other ∧
      (∀ entry ∈ pure, AffineChannelLaw.affineHash entry.sample
        (CoordinatorLocalArmChoice.storedDownFlatWord d.stream.payload i) = 1) ∧
      (∀ entry ∈ pure, s + w ≤ entry.time.val ∧
        entry.time.val ≤ record.input.time.val) ∧
      (∀ entry ∈ pure, entry.sample =
        ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
          entry.time).2 (0, i)) ∧
      ReferenceFirstLiveDownCompletionReadout.completedDownBatch record i = some pure ∧
      ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart
        (s + w) record i ∧
      ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s record i ∧
      ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag
        (s := s) record = true ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        record.input.time source = some record ∧
      ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag
        rate rewards C_star C_h s (record.input.time.val + 1) (by omega) source = true ∧
      source ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
        rate rewards C_star C_h control0 Q ∧
    ∃ hs : s < p.T,
    ∃ x : ReferenceGeneratedDownBatchCalendar.LaunchSource
        rate rewards C_star C_h s hs,
      x.val = source ∧
    ∃ alpha : ℕ, ∃ halpha : s < alpha, ∃ halphaT : alpha < p.T,
      alpha ≤ record.input.time.val ∧
      ReferenceGeneratedDownBatchCalendar.generatedSourceBatchBoundary
        rate rewards C_star C_h s hs i alpha halpha halphaT x ∧
    ∃ hresetSpan : s + (alpha - s) ≤ p.T,
    ∃ resetState : ReferencePrelaunchFollower.State p rate.eta,
    ∃ resetMemory : ActiveFollowerLifecycle.LocalMemory p,
      (ReferenceActiveHorizonMeasurability.runOfInput s (alpha - s) hresetSpan
        (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
          rate rewards C_star C_h s hs x)).finalState.followers i =
            .ordinary resetState resetMemory ∧
      resetState.downBatch.pending = [] ∧
      (ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
        rate rewards C_star C_h s hs i alpha x).map
          ReferenceGeneratedDownPrefixList.stampedTest = pure ∧
      (ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
        rate rewards C_star C_h s hs i alpha x).length = Q ∧
      (∀ test ∈ ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
        rate rewards C_star C_h s hs i alpha x,
        test.sent = some (CoordinatorLocalArmChoice.storedDownFlatWord d.stream.payload i) ∧
        AffineChannelLaw.affineHash test.sample other = 1) := by
  classical
  intro s epoch w B Q i k hkpos hkB hBlen cutoffState cutoffMemory hcutoff W0 q record
    current currentMemory hcurrent hcurrentNone hdown hpositive hcount logged cut post
    hinputLogged hactualCut hrawNone hpostDecoder
  obtain ⟨dE, hwindowE, henvelope⟩ :=
    ReferenceFirstCollectionDownAmbiguityEnvelope.actual_collection_down_pure_ambiguity_envelope
      rate source rewards C_star C_h count hcross hspan hshort control0
  obtain ⟨-, hpayAE, -, hellAE, -, -, -, -, -, -, -, -⟩ :=
    ReferenceFirstCollectionDispatchIdentity.actual_initialized_collection_dispatch_observables
      rate source rewards C_star C_h count hcross hspan hshort d dE
  let kE : Fin dE.stream.ell := ⟨k.val, by rw [← hellAE]; exact k.isLt⟩
  have hinputE :
      (dE.stream.window[kE.val]'(Nat.lt_of_lt_of_le kE.isLt dE.stream.withinWindow)).input.state.followers i =
        .ordinary current currentMemory := by
    have hrecord :
        dE.stream.window[kE.val]'(Nat.lt_of_lt_of_le kE.isLt dE.stream.withinWindow) =
          record := by
      exact getElem_congr_coll hwindowE
    rw [hrecord]
    exact hcurrent
  obtain ⟨hBlenE, cutoffE, cutoffMemoryE, hcutoffE, -, hselectedE⟩ :=
    henvelope kE hkpos i current currentMemory hinputE hcurrentNone
  clear henvelope
  have hseedE : cutoffE = cutoffState :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hcutoffE.symm.trans hcutoff)).1
  subst cutoffE
  obtain ⟨choiceE, choiceMemoryE, loggedE, cutE, -, -,
      hdownInputE, hdownCutE, hloggedChoiceE, hexpectedE, -,
      hthresholdE⟩ := hselectedE hdown
  clear hselectedE
  have hloggedSame : loggedE = logged := Option.some.inj
    (hdownInputE.symm.trans hinputLogged)
  have hcutSame : cutE = cut := Option.some.inj
    (hdownCutE.symm.trans hactualCut)
  have hchoiceSame : choiceE = logged := hloggedChoiceE.symm.trans hloggedSame
  subst choiceE
  subst loggedE
  subst cutE
  obtain ⟨first, pure, hfirstLen, hpureLen, hstep, hbatch, hnoneCut,
      other, hother, hsolvesWord, hsolvesOther, hhashWord,
      hcomparisonFalse, hpureTimes, hpureSamples, hdate,
      hactualRecord, hsourceData⟩ :=
    hthresholdE hpositive hcount hrawNone
  clear hthresholdE
  have hstepActual : actualDownBankAfter record i logged =
      ⟨[], W0.completed ++ [first, pure]⟩ := hstep
  have hpostBank : post.downBatch = ⟨[], W0.completed ++ [first, pure]⟩ :=
    hpostDecoder.trans hstepActual
  refine ⟨first, pure, hfirstLen, hpureLen, hstepActual, hpostBank, hbatch,
    hnoneCut, hcomparisonFalse, other, ?_, ?_, hsolvesOther, ?_,
    hpureTimes, hpureSamples, ?_⟩
  · rw [hpayAE]
    exact hother
  · rw [hpayAE]
    exact hsolvesWord
  · rw [hpayAE]
    exact hhashWord
  rcases hsourceData with ⟨hs, x, hx, N, hN, -, -, hresetData,
      hcompleted, hambiguousWindow, hambiguousStart, hretained, hstrict⟩
  refine ⟨hcompleted, hambiguousWindow, hambiguousStart, hretained,
    hactualRecord, hstrict, ?_⟩
  rcases hresetData with ⟨-, m, hmN, hmRest⟩
  rcases hmRest with ⟨-, -, -, -, hresetInterval⟩
  rcases hresetInterval with ⟨_halphaStart, _halphaEnd, _halphaT, hboundary,
      resetState, resetMemory, hresetState, hresetPending, hbatchData⟩
  rcases hbatchData with ⟨testN, -, -, htestsLen, -,
      -, htestsMap, htestsSent, -, hcohort⟩
  refine ⟨?_, ?_⟩
  · rw [← hx]
    exact hcohort
  · refine ⟨hs, x, hx, s + (m.val + 1), _halphaStart, _halphaT, ?_, hboundary, ?_,
      resetState, resetMemory, ?_, hresetPending, htestsMap, htestsLen, ?_⟩
    · calc
        s + (m.val + 1) ≤ s + N.val := _halphaEnd
        _ = s + (w + k.val) := congrArg (s + ·) (show N.val = w + k.val from hN)
        _ = s + w + k.val := (Nat.add_assoc s w k.val).symm
        _ = record.input.time.val := hdate.symm
    · rw [Nat.add_sub_cancel_left]
      exact Nat.le_of_lt _halphaT
    · simpa only [Nat.add_sub_cancel_left] using hresetState
    · rw [hpayAE]
      exact htestsSent


/-- At every actual ordinary OLD boundary, either fewer than the inherited
second-bank threshold positives have occurred, or an earlier actual detecting
record belongs to the existing current DOWN ambiguity cohort. The dispatch,
payload and every ordinary endpoint are produced before the local OLD test. -/
theorem actual_first_collection_old_down_count_or_ambiguity
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch
        (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count)
    (control0 : ContinuousLearningRows.TimeControl p) :
    let s := ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h
    let epoch := ReferenceFirstCollectionReadyStream.actualEpoch
      (rate := rate) source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
    let B := ReferenceFirstCollectionReadyStream.actualWindow
      (rate := rate) source rewards C_star C_h hcross count hspan
    let Q := AffineBatchDecoder.quota p
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      ∃ hwindow : out.window = B,
        out.payload.sigma.val = s ∧
        (∀ i, (out.payload.downRecord i).val.sigma = s + 1 ∧
          (out.payload.downRecord i).val.q = 0) ∧
      ∀ i : Fin (p.m - 1),
        ∃ hBlen : 0 < B.length,
        ∃ cutoffState : ReferencePrelaunchFollower.State p rate.eta,
        ∃ cutoffMemory : ActiveFollowerLifecycle.LocalMemory p,
          (B[0]'hBlen).input.state.followers i = .ordinary cutoffState cutoffMemory ∧
          ActiveFollowerLifecycle.localStateDomainValid cutoffState ∧
          ActiveFollowerLifecycle.localBufferValid cutoffState ∧
          ActiveFollowerLifecycle.downDecoderStateValid cutoffState ∧
          ActiveFollowerLifecycle.startRound rate.eta (B[0]'hBlen).input.time
            cutoffState cutoffMemory =
              .ok ({cutoffState with status := .unoccupied}, cutoffMemory) ∧
          (let W0 := cutoffState.downBatch
           let q := Q - W0.pending.length + Q
           W0.pending.length < Q ∧ Q < q ∧ q ≤ 2 * Q ∧
           ∀ b : ℕ, ∀ hb : b ≤ out.ell,
             ∃ hbound : s + (w + b) ≤ p.T,
             ∃ before : ReferencePrelaunchFollower.State p rate.eta,
             ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
               (∀ hlt : b < B.length,
                 (ReferenceFirstCollectionDownThresholdAttainment.actualPrefix
                   rate source rewards C_star C_h hcross count hspan b hbound).finalState =
                     (B[b]'hlt).input.state) ∧
               (∀ hpos : 0 < b,
                 (ReferenceFirstCollectionDownThresholdAttainment.actualPrefix
                   rate source rewards C_star C_h hcross count hspan b hbound).finalState =
                     (B[b - 1]'(by
                       have hle : out.ell ≤ B.length := by
                         calc
                           out.ell ≤ out.window.length := out.withinWindow
                           _ = B.length := congrArg List.length hwindow
                       omega)).output.next) ∧
               (b = out.ell →
                 (ReferenceFirstCollectionDownThresholdAttainment.actualPrefix
                   rate source rewards C_star C_h hcross count hspan b hbound).finalState =
                     d.record.output.next) ∧
               (ReferenceFirstCollectionDownThresholdAttainment.actualPrefix
                 rate source rewards C_star C_h hcross count hspan b hbound).finalState.followers i =
                   .ordinary before memory ∧
               (b = 0 → before = cutoffState ∧ memory = cutoffMemory) ∧
               (before.lastDown = none → ∀ j : Fin b, ∃ prior priorMemory,
                 (B[j.val]'(by
                   have hle : out.ell ≤ B.length := by
                     calc
                       out.ell ≤ out.window.length := out.withinWindow
                       _ = B.length := congrArg List.length hwindow
                   omega)).input.state.followers i = .ordinary prior priorMemory ∧
                   prior.lastDown = none) ∧
               (before.lastDown = none →
                 (actualDownPositives i (B.take b)).length < q ∨
                 ∃ k : Fin out.ell, ∃ hkB : k.val < B.length,
                   0 < k.val ∧ k.val < b ∧
                   (actualDownPositives i (B.take (k.val + 1))).length = q ∧
                   (∀ j : ℕ, j ≤ k.val →
                     (actualDownPositives i (B.take j)).length < q) ∧
                   let record := B[k.val]'hkB
                   ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time ∧
                   0 < (ReferenceFirstCollectionDownPhysicalThresholdJoin.localObservation
                     record i).val.val ∧
                   record.input.time.val = s + w + k.val ∧
                   record.input.rows = source.1.2 ∧
                   record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                   record.input.rewards = rewards ∧
                   ∃ current currentMemory,
                     record.input.state.followers i = .ordinary current currentMemory ∧
                     current.lastDown = none ∧
                     current.downBatch = foldDownCalls
                       (actualDownCalls i (B.take k.val)) W0 ∧
                     AffineBatchDecoder.collected current.downBatch =
                       AffineBatchDecoder.collected W0 ++ actualDownPositives i (B.take k.val) ∧
                   ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
                     (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
                     (post : ReferencePrelaunchFollower.State p rate.eta),
                     logged = current ∧
                     (record.output.followers i).downInput = some logged ∧
                     (record.output.followers i).down = some cut ∧
                     cut = ReferenceFirstCollectionDownPhysicalThresholdJoin.localCut record i logged ∧
                     (ReferenceFirstCollectionDownPhysicalThresholdJoin.localPhysicalCall
                       record i current).result = .ok post ∧
                     record.output.next.followers i = .ordinary post currentMemory ∧
                     cut.expectedWord = some
                       (CoordinatorLocalArmChoice.storedDownFlatWord out.payload i) ∧
                   ∃ first pure : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
                     first.length = Q ∧ pure.length = Q ∧
                     actualDownBankAfter record i logged = ⟨[], W0.completed ++ [first, pure]⟩ ∧
                     post.downBatch = ⟨[], W0.completed ++ [first, pure]⟩ ∧
                     cut.raw = AffineBatchDecoder.batchOutput pure ∧ cut.raw = none ∧
                     cut.rawComparison = some false ∧
                   ∃ other : AffineChannelLaw.Word (AffineBatchDecoder.width p),
                     other ≠ CoordinatorLocalArmChoice.storedDownFlatWord out.payload i ∧
                     AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure)
                       (CoordinatorLocalArmChoice.storedDownFlatWord out.payload i) ∧
                     AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure) other ∧
                     (∀ entry ∈ pure, AffineChannelLaw.affineHash entry.sample
                       (CoordinatorLocalArmChoice.storedDownFlatWord out.payload i) = 1) ∧
                     (∀ entry ∈ pure, s + w ≤ entry.time.val ∧
                       entry.time.val ≤ record.input.time.val) ∧
                     (∀ entry ∈ pure, entry.sample =
                       ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
                         entry.time).2 (0, i)) ∧
                     ReferenceFirstLiveDownCompletionReadout.completedDownBatch record i = some pure ∧
                     ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart
                       (s + w) record i ∧
                     ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s record i ∧
                     ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag
                       (s := s) record = true ∧
                     ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
                       record.input.time source = some record ∧
                     ReferenceFirstLiveDecoderPastMeasurability.strictPastDecoderFlag
                       rate rewards C_star C_h s (record.input.time.val + 1) (by omega) source = true ∧
                     source ∈ ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
                       rate rewards C_star C_h control0 Q ∧
                   ∃ hs : s < p.T,
                   ∃ x : ReferenceGeneratedDownBatchCalendar.LaunchSource
                       rate rewards C_star C_h s hs,
                     x.val = source ∧
                   ∃ alpha : ℕ, ∃ halpha : s < alpha, ∃ halphaT : alpha < p.T,
                     alpha ≤ record.input.time.val ∧
                     ReferenceGeneratedDownBatchCalendar.generatedSourceBatchBoundary
                       rate rewards C_star C_h s hs i alpha halpha halphaT x ∧
                   ∃ hresetSpan : s + (alpha - s) ≤ p.T,
                   ∃ resetState : ReferencePrelaunchFollower.State p rate.eta,
                   ∃ resetMemory : ActiveFollowerLifecycle.LocalMemory p,
                     (ReferenceActiveHorizonMeasurability.runOfInput s (alpha - s) hresetSpan
                       (ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput
                         rate rewards C_star C_h s hs x)).finalState.followers i =
                           .ordinary resetState resetMemory ∧
                     resetState.downBatch.pending = [] ∧
                     (ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
                       rate rewards C_star C_h s hs i alpha x).map
                         ReferenceGeneratedDownPrefixList.stampedTest = pure ∧
                     (ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
                       rate rewards C_star C_h s hs i alpha x).length = Q ∧
                     (∀ test ∈ ReferenceGeneratedDownBatchCalendar.generatedDownBatchTests
                       rate rewards C_star C_h s hs i alpha x,
                       test.sent = some (CoordinatorLocalArmChoice.storedDownFlatWord out.payload i) ∧
                       AffineChannelLaw.affineHash test.sample other = 1))) := by
  classical
  intro s epoch w B Q
  have hA :=
    ReferenceFirstCollectionDownThresholdAttainment.actual_first_collection_down_boundaries_and_attainment
      rate source rewards C_star C_h hcross count hspan hshort
  have hJ :=
    ReferenceFirstCollectionDownPhysicalThresholdJoin.actual_first_collection_down_physical_threshold_join
      rate source rewards C_star C_h count hcross hspan hshort
  rcases hA with ⟨dA, hwindowA, hsigmaA, hrecordsA, hboundariesA⟩
  rcases hJ with ⟨dJ, hwindowJ, -, -, -, _r, _owned, _base,
      -, -, -, -, hjoin⟩
  obtain ⟨-, hpayAJ, -, hellAJ, -,
      -, -, -, -, -,
      -, -⟩ :=
    ReferenceFirstCollectionDispatchIdentity.actual_initialized_collection_dispatch_observables
      rate source rewards C_star C_h count hcross hspan hshort dA dJ
  refine ⟨dA, hwindowA, hsigmaA, hrecordsA, ?_⟩
  intro i
  obtain ⟨hBlen, cutoffState, cutoffMemory, hcutoff, hdomain, hbuffer,
      hdecoder, hreset, -, -, hpending,
      hQlt, hqUpper, -, hforallB⟩ := hboundariesA i
  refine ⟨hBlen, cutoffState, cutoffMemory, hcutoff, hdomain, hbuffer,
    hdecoder, hreset, hpending, hQlt, hqUpper, ?_⟩
  intro b hb
  obtain ⟨hbound, before, memory, hlt, hpos, hterminal, hordinary,
      -, -, -, hzero, -,
      hprior, hthreshold⟩ := hforallB b hb
  clear hforallB hboundariesA
  refine ⟨hbound, before, memory, hlt, hpos, hterminal, hordinary,
    (fun hz => ⟨(hzero hz).1, (hzero hz).2.1⟩), hprior, ?_⟩
  intro hnone
  let W0 := cutoffState.downBatch
  let q := Q - W0.pending.length + Q
  by_cases hsmall : (actualDownPositives i (B.take b)).length < q
  · exact Or.inl hsmall
  right
  have hreach : q ≤ (actualDownPositives i (B.take b)).length := Nat.le_of_not_gt hsmall
  obtain ⟨k, hkB, hkpos, hkb, hcount, hfirst, hdown, hpositive,
      hdate, hrows, hselected, hrewards, -, -, -,
      hcurrentData, -, -⟩ := hthreshold hnone hreach
  clear hthreshold
  rcases hcurrentData with ⟨current, currentMemory, hcurrent, hcurrentNone, hfold, hcollected⟩
  let record : ReferenceCollectionPhaseHistory.Record p rate := B[k.val]'hkB
  have hpositiveJ : 0 < (ReferenceFirstCollectionDownPhysicalThresholdJoin.localObservation
      record i).val.val := hpositive
  let kJ : Fin dJ.stream.ell := ⟨k.val, by rw [← hellAJ]; exact k.isLt⟩
  refine ⟨k, hkB, hkpos, hkb, hcount, hfirst, ?_⟩
  refine ⟨hdown, hpositiveJ, hdate, hrows, hselected, hrewards, ?_⟩
  refine ⟨current, currentMemory, hcurrent, hcurrentNone, hfold, hcollected, ?_⟩
  obtain ⟨nB, hnB, hRun, hNext, hprefixIn, hprefixOut,
      beforeJ, memoryJ, hinputJ, hpreparedJ, hstatusJ, -,
      loggedJ, cutJ, post, hloggingJ, -, hcutJ,
      hresultJ, -, -, -, houtConfigJ,
      -, houtInputJ, houtCutJ, -, -, holdJ⟩ :=
    hjoin kJ hkpos i
  clear hjoin
  have hnBEq : nB = ⟨k.val, hkB⟩ := Fin.ext hnB
  subst nB
  have hstates := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hinputJ.symm.trans hcurrent)
  rcases hstates with ⟨hbeforeEq, hmemoryEq⟩
  subst beforeJ
  subst memoryJ
  obtain ⟨-, hBlenJ, cutoffJ, cutoffMemoryJ, hcutoffJ, -, hselectedJ⟩ :=
    holdJ hcurrentNone
  clear holdJ
  have hseedJ : cutoffJ = cutoffState :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hcutoffJ.symm.trans hcutoff)).1
  subst cutoffJ
  have hdownJ : ActiveFollowerDownAcceptance.downSelected p i
      (dJ.stream.window[kJ.val]'(Nat.lt_of_lt_of_le kJ.isLt dJ.stream.withinWindow)).input.row
      (dJ.stream.window[kJ.val]'(Nat.lt_of_lt_of_le kJ.isLt dJ.stream.withinWindow)).input.time := by
    simpa only [hwindowJ, kJ, ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch] using hdown
  obtain ⟨choiceJ, choiceMemoryJ, logged, cut, hprepChoiceJ, -,
      hdownInputJ, hdownCutJ, hexpectedJ, -, -,
      hloggedChoiceJ, -, -, -,
      hchoiceJ, hchoiceMemoryJ, hloggedJ, hcutEqJ, hthresholdJ⟩ := hselectedJ hdownJ
  clear hselectedJ
  have hchoiceEq : choiceJ = current := hchoiceJ
  have hloggedEq : logged = current := hloggedChoiceJ.trans hchoiceEq
  have hcutEq : cut = cutJ := hcutEqJ
  have hinputLogged : (record.output.followers i).downInput = some logged := by
    rw [hloggedChoiceJ]
    exact hdownInputJ
  have hcutLogged : cut = ReferenceFirstCollectionDownPhysicalThresholdJoin.localCut
      record i logged := by
    rw [hloggedJ]
    exact hcutEq.trans hcutJ
  have hexpected : cut.expectedWord = some
      (CoordinatorLocalArmChoice.storedDownFlatWord dA.stream.payload i) := by
    simpa only [hpayAJ] using hexpectedJ
  obtain ⟨firstJ, pureJ, -, -, -,
      -, hstepJ, -, -, -, -,
      -, -, -, hphysicalCases⟩ :=
    hthresholdJ hpositiveJ hcount
  clear hthresholdJ
  let physicalRecord : ReferenceCollectionPhaseHistory.Record p rate :=
    (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length)[k.val]'hkB
  have hphysicalRecord : physicalRecord = record := rfl
  change actualDownBankAfter physicalRecord i choiceJ =
    ⟨[], W0.completed ++ [firstJ, pureJ]⟩ at hstepJ
  have hactualResult : (ReferenceFirstCollectionDownPhysicalThresholdJoin.localPhysicalCall
      record i current).result = .ok post :=
    physical_result_of_record_eq physicalRecord record hphysicalRecord i current post hresultJ
  have hactualCut : (record.output.followers i).down = some cut := hdownCutJ
  have hnext : record.output.next.followers i = .ordinary post currentMemory := by
    have hfields : record.output.next.followers i =
        (record.output.followers i).configuration := by rw [record.output_eq]; rfl
    exact hfields.trans houtConfigJ
  refine ⟨logged, cut, post, ?_⟩
  refine ⟨hloggedEq, ?_⟩
  refine ⟨hinputLogged, ?_⟩
  refine ⟨hactualCut, ?_⟩
  refine ⟨hcutLogged, ?_⟩
  refine ⟨hactualResult, hnext, hexpected, ?_⟩
  have hprefixOut' :
      (ReferenceFirstCollectionDownThresholdAttainment.actualPrefix
        rate source rewards C_star C_h hcross count hspan
        (k.val + 1) hNext).finalState = record.output.next := hprefixOut
  have hrawNone : cut.raw = none :=
    cut_none_of_old_prefix
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source rewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s (w + b) hbound
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1
      record i (w + (k.val + 1))
      (Nat.add_le_add_left (Nat.succ_le_of_lt hkb) w) hNext
      current currentMemory hpreparedJ hcurrentNone post before currentMemory memory
      hprefixOut' hnext hordinary hnone loggedJ cut
      (some (CoordinatorLocalArmChoice.storedDownFlatWord dJ.stream.payload i))
      (dJ.stream.payload.downRecord i) houtInputJ hactualCut
      (hphysicalCases.imp
        (fun ⟨_, after, scan, registers, lastService, ho, _, _⟩ =>
          ⟨after, scan, registers, lastService, ho⟩)
        (fun h => h.1))
  have hpostDecoder : post.downBatch = actualDownBankAfter record i logged := by
    rcases hphysicalCases with haccepted | ⟨-, -, otherJ, -, -, hbankJ⟩
    · have hsome := haccepted.1
      rw [hrawNone] at hsome
      cases hsome
    · have hbankLogged : actualDownBankAfter physicalRecord i logged =
          ⟨[], W0.completed ++ [firstJ, pureJ]⟩ := by
        rw [hloggedChoiceJ]
        exact hstepJ
      exact hbankJ.trans
        (hbankLogged.symm.trans
          (congrArg (fun r => actualDownBankAfter r i logged) hphysicalRecord))
  exact ambiguity_after_actual_cut rate source rewards C_star C_h count hcross hspan
    hshort control0 dA i k hkpos hkB hBlen cutoffState cutoffMemory hcutoff
    current currentMemory hcurrent hcurrentNone hdown hpositiveJ hcount
    logged cut post hinputLogged hactualCut hrawNone hpostDecoder

end Bandits.Support.ReferenceFirstCollectionOldDownCountOrAmbiguity

end
