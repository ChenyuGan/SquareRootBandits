/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionUpDetectedWaitingCost

import Lean.Elab.Tactic.Omega

/-!
# First-collection OLD-prefix awaited DOWN batch witness

This module joins the actual first OLD-prefix DOWN threshold crossing to the
same retained pure second batch and its full original-calendar awaited word.
Every source record is from the canonical initialized dispatch and its whole
original row table.  No continuation past the dispatch stream is asserted.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:33-55`,
`sources/zip4/manuscript/06_interruptions.tex:246-282,425-431,459-481`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-108,141-157`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams
open ReferenceFollowerDownDecoderReplay
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionAwaitedDownBatchWitness

variable {p : ConstructorDimensions.Parameters}

/-- The literal actual call clauses for one selected DOWN round.  This has no
positivity guard: zero-feedback selected calls remain part of an awaited word. -/
def actualDownAwaitedCall
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (word : AffineChannelLaw.Word (AffineBatchDecoder.width p)) : Prop :=
  ∃ logged : ReferencePrelaunchFollower.State p rate.eta,
    ∃ cut : ReferenceDownReception.ReferenceDownCutOutput p rate,
      (record.output.followers i).downInput = some logged ∧
      (record.output.followers i).down = some cut ∧
      cut.rawComparison.isSome = true ∧
      cut.expectedWord = some word ∧
      ReferenceDownReception.ordinaryLocalAcceptanceTest p rate record.input.time logged
        (ReferenceDownReception.ordinaryParse p rate (some word))

private theorem actual_down_positive_origin
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (i : Fin (p.m - 1))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hentry : entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i records) :
    ∃ record, record ∈ records ∧
      entry.time = record.input.time ∧
      ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time ∧
      entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [record] := by
  classical
  unfold ReferenceFollowerDownDecoderReplay.actualDownPositives
    ReferenceFollowerDownDecoderReplay.positiveCallEntries
    ReferenceFollowerDownDecoderReplay.actualDownCalls at hentry
  obtain ⟨call, hcallMem, hpositive⟩ := List.mem_flatMap.mp hentry
  obtain ⟨record, hrecord, hcall⟩ := List.mem_filterMap.mp hcallMem
  have hpositiveCall : AffineBatchDecoder.eligible
      ((ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1) := by
    by_contra hbad
    simp [AffineBatchDecoder.positiveAt, hbad] at hpositive
  have hcallTime : call.1 = record.input.time := by
    cases hchoice : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i with
    | dagger => simp [ReferenceFollowerDownDecoderReplay.actualDownCall, hchoice] at hcall
    | ordinary choice memory =>
        rw [ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary
          record i choice memory hchoice] at hcall
        cases hcall
        exact ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime record i
  have hentryEq : entry = ⟨call.1, call.2.sample⟩ := by
    unfold AffineBatchDecoder.positiveAt at hpositive
    rw [ite_eq_left hpositiveCall] at hpositive
    exact List.mem_singleton.mp hpositive
  have hchoice : ∃ choice memory,
      ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
        .ordinary choice memory := by
    cases hc : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i with
    | dagger => simp [ReferenceFollowerDownDecoderReplay.actualDownCall, hc] at hcall
    | ordinary choice memory => exact ⟨choice, memory, rfl⟩
  obtain ⟨choice, memory, hconfiguration⟩ := hchoice
  have hcallEq := ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary
    record i choice memory hconfiguration
  rw [hcallEq] at hcall
  have hcallPair := Option.some.inj hcall
  have hcallTimeEq :
      ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i = call.1 :=
    congrArg Prod.fst hcallPair
  have hcallInputEq :
      ActiveFollowerDownAcceptance.currentRoundInput p i
        (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice = call.2 :=
    congrArg Prod.snd hcallPair
  have heligible : AffineBatchDecoder.eligible
      (ActiveFollowerDownAcceptance.currentRoundInput p i
        (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice) := by
    simpa only [hcallInputEq.symm, ActiveFollowerDownAcceptance.currentInputExtension] using hpositiveCall
  have hselectedPrepared :=
    (ReferenceFollowerDownDecoderReplay.actualDownCall_eligible_iff record i choice).1 heligible
  have hselected : ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time := by
    have hrow : ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i = record.input.row :=
      (record.output.preparation.follower_alignment i).1
    have htime := ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime record i
    simpa only [hrow, htime] using hselectedPrepared.1
  have hsingle : entry ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [record] := by
    unfold ReferenceFollowerDownDecoderReplay.actualDownPositives
      ReferenceFollowerDownDecoderReplay.actualDownCalls
      ReferenceFollowerDownDecoderReplay.positiveCallEntries
    simp only [List.filterMap_cons, List.filterMap_nil, hcallEq,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simpa only [hcallInputEq.symm, hcallTimeEq.symm] using hpositive
  refine ⟨record, hrecord, ?_, hselected, hsingle⟩
  calc
    entry.time = call.1 := congrArg AffineBatchDecoder.Entry.time hentryEq
    _ = record.input.time := hcallTime

private theorem positive_entries_append
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (i : Fin (p.m - 1))
    (left right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    ReferenceFollowerDownDecoderReplay.actualDownPositives i (left ++ right) =
      ReferenceFollowerDownDecoderReplay.actualDownPositives i left ++
        ReferenceFollowerDownDecoderReplay.actualDownPositives i right := by
  simp only [ReferenceFollowerDownDecoderReplay.actualDownPositives,
    ReferenceFollowerDownDecoderReplay.actualDownCalls, List.filterMap_append,
    ReferenceFollowerDownDecoderReplay.positiveCallEntries, List.flatMap_append]

private theorem actual_down_positive_singleton
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfig : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration record i =
      .ordinary choice memory)
    (hstatus : choice.status = .unoccupied)
    (hselected : ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time)
    (hpositive : 0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i).val.val) :
    actualDownPositives i [record] =
      [⟨record.input.time, (record.input.row.2 record.input.time).2 (0, i)⟩] := by
  have hrow : ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i = record.input.row :=
    (record.output.preparation.follower_alignment i).1
  have htime := ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime record i
  have hprepared : AffineBatchDecoder.eligible
      (ActiveFollowerDownAcceptance.currentRoundInput p i
        (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate choice) := by
    apply (ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p i _ _ _ rate choice).2
    exact ⟨by rw [hrow, htime]; exact hselected, hstatus, hpositive⟩
  have hcall := ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary
    record i choice memory hconfig
  unfold actualDownPositives actualDownCalls positiveCallEntries
  simp only [List.filterMap_cons, List.filterMap_nil, hcall, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  rw [AffineBatchDecoder.positiveAt, ite_eq_left (by
    simpa only [ActiveFollowerDownAcceptance.currentInputExtension] using hprepared)]
  simp only [AffineBatchDecoder.entry, ActiveFollowerDownAcceptance.currentInputExtension,
    ActiveFollowerDownAcceptance.currentRoundInput, hrow, htime]

private theorem actual_selected_down_calls
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
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (k : Fin d.stream.ell) (hkpos : 0 < k.val)
    (i : Fin (p.m - 1)) (current : ReferencePrelaunchFollower.State p rate.eta)
    (currentMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hcurrent : (d.stream.window[k.val]'(Nat.lt_of_lt_of_le k.isLt
      d.stream.withinWindow)).input.state.followers i = .ordinary current currentMemory)
    (hnone : current.lastDown = none) :
    ∀ j : Fin (k.val + 1),
      let record := d.stream.window[j.val]'(Nat.lt_of_le_of_lt
        (Nat.le_of_lt_succ j.isLt) (Nat.lt_of_lt_of_le k.isLt d.stream.withinWindow))
      ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time →
      actualDownAwaitedCall rate record i
        (CoordinatorLocalArmChoice.storedDownFlatWord d.stream.payload i) := by
  classical
  obtain ⟨dNew, _hwindow, _hsigma, _hrecords, hcalls⟩ :=
    ReferenceFirstCollectionDownSecondPureBank.actual_collection_unaccepted_down_second_pure_bank
      rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨hwindow, hpayload, _, hell, _, _, _, _, _, _, _, _⟩ :=
    ReferenceFirstCollectionDispatchIdentity.actual_initialized_collection_dispatch_observables
      rate source rewards C_star C_h count hcross hspan hshort d dNew
  have hkNew : k.val < dNew.stream.ell := by rw [← hell]; exact k.isLt
  let kNew : Fin dNew.stream.ell := ⟨k.val, hkNew⟩
  have hrecordK :
      dNew.stream.window[kNew.val]'(Nat.lt_of_lt_of_le kNew.isLt dNew.stream.withinWindow) =
        d.stream.window[k.val]'(Nat.lt_of_lt_of_le k.isLt d.stream.withinWindow) :=
    getElem_congr_coll hwindow.symm
  have hcurrentNew :
      (dNew.stream.window[kNew.val]'(Nat.lt_of_lt_of_le kNew.isLt
        dNew.stream.withinWindow)).input.state.followers i = .ordinary current currentMemory := by
    rw [hrecordK]
    exact hcurrent
  obtain ⟨hprior, _hendpoint⟩ := hcalls kNew hkpos i current currentMemory hcurrentNew hnone
  intro j
  dsimp only
  intro hdown
  let jNew : Fin (kNew.val + 1) := ⟨j.val, j.isLt⟩
  obtain ⟨prior, priorMemory, _hpriorState, _hpriorNone, hcall⟩ := hprior jNew
  have hjNew : j.val < dNew.stream.window.length :=
    Nat.lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt)
      (Nat.lt_of_lt_of_le hkNew dNew.stream.withinWindow)
  let record := dNew.stream.window[j.val]'hjNew
  have hrecordJ : record = d.stream.window[j.val]'(Nat.lt_of_le_of_lt
      (Nat.le_of_lt_succ j.isLt) (Nat.lt_of_lt_of_le k.isLt d.stream.withinWindow)) :=
    getElem_congr_coll hwindow.symm
  have hdownNew : ActiveFollowerDownAcceptance.downSelected p i
      record.input.row record.input.time := by
    rw [hrecordJ]
    exact hdown
  obtain ⟨selected, choice, memory, _hselection, _hpayload, _hpending,
    _hsent, _hconfig, _hstatus, _hlast, _hdomain, _hlogging,
    hdownInput, hcut, _hregister, _hdecoder, _hbuffer, hexpected,
    hcomparisonSome, _hraw, _hfiltered, _hordinaryParse, _hordinaryAcceptance,
    _hcomparison, _hreject, _houtcome, hparseWord,
    _hacceptedStart, _hsigma, _htime, hlocal, _hhash⟩ := hcall hdownNew
  let cut := ReferenceDownReception.referenceDownCut p
    record.output.preparation.coordinator.downView i record.input.row record.input.time
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate choice
  have hlocalWord : ReferenceDownReception.ordinaryLocalAcceptanceTest
      p rate record.input.time choice (ReferenceDownReception.ordinaryParse p rate
        (some (CoordinatorLocalArmChoice.storedDownFlatWord dNew.stream.payload i))) := by
    rw [hparseWord]
    exact hlocal
  have hawait : actualDownAwaitedCall rate record i
      (CoordinatorLocalArmChoice.storedDownFlatWord dNew.stream.payload i) :=
    ⟨choice, cut, hdownInput, hcut, hcomparisonSome, hexpected, hlocalWord⟩
  rw [hrecordJ, ← hpayload] at hawait
  exact hawait

private theorem actual_pure_bank_prefix_membership
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
    (dOld : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (i : Fin (p.m - 1))
    (cutoffState : ReferencePrelaunchFollower.State p rate.eta)
    (cutoffMemory : ActiveFollowerLifecycle.LocalMemory p)
    (k : Fin dOld.stream.ell) (hkpos : 0 < k.val) :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let Q := AffineBatchDecoder.quota p
    let W0 := cutoffState.downBatch
    ∀ (hkB : k.val < B.length) (hBlen : 0 < B.length),
      (B[0]'hBlen).input.state.followers i = .ordinary cutoffState cutoffMemory →
    ∀ (current : ReferencePrelaunchFollower.State p rate.eta)
      (currentMemory : ActiveFollowerLifecycle.LocalMemory p),
      (B[k.val]'hkB).input.state.followers i = .ordinary current currentMemory →
      current.lastDown = none →
      ActiveFollowerDownAcceptance.downSelected p i (B[k.val]'hkB).input.row
        (B[k.val]'hkB).input.time →
      0 < (ReferenceFirstCollectionDownPhysicalThresholdJoin.localObservation
        (B[k.val]'hkB) i).val.val →
      (actualDownPositives i (B.take (k.val + 1))).length = Q - W0.pending.length + Q →
    ∀ (loggedOld : ReferencePrelaunchFollower.State p rate.eta),
      ((B[k.val]'hkB).output.followers i).downInput = some loggedOld →
    ∀ (firstOld pureOld : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))),
      ReferenceFirstCollectionOldDownCountOrAmbiguity.actualDownBankAfter
        (B[k.val]'hkB) i loggedOld = ⟨[], W0.completed ++ [firstOld, pureOld]⟩ →
      ∀ entry ∈ pureOld, entry ∈ actualDownPositives i (B.take (k.val + 1)) := by
  classical
  intro E w B Q W0 hkB hBlen hcutoff current currentMemory hcurrentState hcurrentNone
    hselected hpositive hcount loggedOld hdownInputOld firstOld pureOld hbankAfterOld
  obtain ⟨dBank, hwindowBank, _hsigmaBank, _hrecordsBank, hcallsBank⟩ :=
    ReferenceFirstCollectionDownSecondPureBank.actual_collection_unaccepted_down_second_pure_bank
      rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨_hWindowId, _hPayloadId, _, hEllId, _, _, _, _, _, _, _, _⟩ :=
    ReferenceFirstCollectionDispatchIdentity.actual_initialized_collection_dispatch_observables
      rate source rewards C_star C_h count hcross hspan hshort dOld dBank
  have hkDlt : k.val < dBank.stream.ell := by
    rw [← hEllId]
    exact k.isLt
  let kD : Fin dBank.stream.ell := ⟨k.val, hkDlt⟩
  have hkBlen : k.val < B.length := by
    exact hkB
  have hrecD : dBank.stream.window[kD.val]'(Nat.lt_of_lt_of_le kD.isLt dBank.stream.withinWindow) =
      B[k.val]'hkBlen := by
    exact getElem_congr_coll hwindowBank
  have hfiD :
      (dBank.stream.window[kD.val]'(Nat.lt_of_lt_of_le kD.isLt dBank.stream.withinWindow)).input.state.followers i =
        .ordinary current currentMemory := by
    rw [hrecD]
    exact hcurrentState
  have hdownD : ActiveFollowerDownAcceptance.downSelected p i
      (dBank.stream.window[kD.val]'(Nat.lt_of_lt_of_le kD.isLt dBank.stream.withinWindow)).input.row
      (dBank.stream.window[kD.val]'(Nat.lt_of_lt_of_le kD.isLt dBank.stream.withinWindow)).input.time := by
    rw [hrecD]
    exact hselected
  rcases hcallsBank kD hkpos i current currentMemory hfiD hcurrentNone with
    ⟨hpriorBank, hbankEndpoint⟩
  rcases hbankEndpoint with ⟨hBlenBank, cutoffStateBank, cutoffMemoryBank,
    hcutoffBank, hbankPrefix, hcallAt⟩
  have hcutoffStateEq : cutoffState = cutoffStateBank := by
    apply (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hcutoff.symm.trans hcutoffBank)).1
  have hW0Bank : cutoffStateBank.downBatch = W0 := by
    simpa only [W0] using
      congrArg ReferencePrelaunchFollower.State.downBatch hcutoffStateEq.symm
  have hBactual : B = ReferenceFirstCollectionReadyStream.actualWindow
      (rate := rate) source rewards C_star C_h hcross count hspan := by
    rfl
  have hcountBank :
      (ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take (k.val + 1))).length =
        Q - cutoffStateBank.downBatch.pending.length + Q := by
    simpa only [hW0Bank, W0, Q] using hcount
  rcases hcallAt hdownD with ⟨choice, choiceMemory, loggedBank, cutBank,
    hconfigBank, hstatusBank, hdownInputBank, hcutBank, hexpectedBank,
    hcomparisonSomeBank, hcomparisonBank, hloggedEqBank, hloggedBatchBank,
    hloggedFoldBank, hrawBank, hthresholdBank⟩
  have hkActual : k.val <
      (ReferenceFirstCollectionReadyStream.actualWindow
        (rate := rate) source rewards C_star C_h hcross count hspan).length := by
    simpa only [hBactual] using hkBlen
  have hrecordBactual : B[k.val]'hkBlen =
      (ReferenceFirstCollectionReadyStream.actualWindow
        (rate := rate) source rewards C_star C_h hcross count hspan)[k.val]'hkActual := by
    exact getElem_congr_coll hBactual
  have hpositiveB :
      0 < (ReferenceFirstCollectionDownPhysicalThresholdJoin.localObservation
        (B[k.val]'hkBlen) i).val.val := by
    rw [hrecordBactual]
    exact hpositive
  have hpositiveOwn :
      0 < ((B[k.val]'hkBlen).output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val := by
    simpa [ReferenceFirstCollectionDownPhysicalThresholdJoin.localObservation] using hpositiveB
  have hselectedB : ActiveFollowerDownAcceptance.downSelected p i
      (B[k.val]'hkBlen).input.row (B[k.val]'hkBlen).input.time := by
    rw [hrecordBactual]
    exact hselected
  have hthresholdData := hthresholdBank hpositiveOwn hcountBank
  rcases hthresholdData with ⟨contaminated, pureBank, hcontaminated,
    hpureBank, hcontaminatedLength, hpureBankLength, hdecodeBank,
    hrawPure, hhashPure, hsolvePure, hpairPure, htimePure, hsamplePure,
    hrawNonePure⟩
  have hloggedOldEq : loggedOld = choice :=
    Option.some.inj (hdownInputOld.symm.trans hdownInputBank)
  have hbankBoth :
      (⟨[], W0.completed ++ [firstOld, pureOld]⟩ :
        AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) =
      ⟨[], W0.completed ++ [contaminated, pureBank]⟩ := by
    calc
      _ = ReferenceFirstCollectionOldDownCountOrAmbiguity.actualDownBankAfter
            (B[k.val]'hkBlen) i loggedOld := hbankAfterOld.symm
      _ = (ActiveFollowerDownAcceptance.currentDecodeStep p i
            (B[k.val]'hkBlen).input.row (B[k.val]'hkBlen).input.time
            ((B[k.val]'hkBlen).output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate choice).1 := by
            simp only [ReferenceFirstCollectionOldDownCountOrAmbiguity.actualDownBankAfter,
              hloggedOldEq, ReferenceFirstCollectionDownPhysicalThresholdJoin.localObservation]
        _ = _ := by
          simpa only [B, w, E, kD, hW0Bank] using hdecodeBank
  have hcompletedLists := congrArg
    (fun state : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) => state.completed)
    hbankBoth
  have hpairLists : [firstOld, pureOld] = [contaminated, pureBank] :=
    List.append_cancel_left hcompletedLists
  have hpureEq : pureOld = pureBank := by
    injection hpairLists with _ htail
    injection htail with hEq _
  let recordK := B[k.val]'hkBlen
  have happendedPositive :
      ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take (k.val + 1)) =
        ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take k.val) ++
          [⟨recordK.input.time, (recordK.input.row.2 recordK.input.time).2 (0, i)⟩] := by
    rw [List.take_succ_eq_append_getElem hkBlen, positive_entries_append]
    have hconfigK : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration recordK i =
        .ordinary choice choiceMemory := hconfigBank
    have hpositiveK :
        0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation recordK i).val.val :=
      hpositiveOwn
    rw [actual_down_positive_singleton recordK i choice choiceMemory
      hconfigK hstatusBank hselectedB hpositiveK]
  have hrowK : ReferenceFollowerDownDecoderReplay.preparedChoiceRow recordK i =
      recordK.input.row := (recordK.output.preparation.follower_alignment i).1
  have htimeK := ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime recordK i
  have hentryK :
      (⟨(recordK.output.preparation.followers.followers i).time,
        ((recordK.output.preparation.followers.followers i).row.2
          (recordK.output.preparation.followers.followers i).time).2 (0, i)⟩ :
        AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) =
      ⟨recordK.input.time, (recordK.input.row.2 recordK.input.time).2 (0, i)⟩ := by
    change (⟨ReferenceFollowerDownDecoderReplay.preparedChoiceTime recordK i,
      ((ReferenceFollowerDownDecoderReplay.preparedChoiceRow recordK i).2
        (ReferenceFollowerDownDecoderReplay.preparedChoiceTime recordK i)).2 (0, i)⟩ :
        AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) = _
    rw [hrowK, htimeK]
  have hpureBankB : pureBank =
      (actualDownPositives i (B.take k.val)).drop (Q - W0.pending.length) ++
        [⟨recordK.input.time, (recordK.input.row.2 recordK.input.time).2 (0, i)⟩] := by
    have hpure' : pureBank =
        (actualDownPositives i (B.take k.val)).drop (Q - W0.pending.length) ++
          [⟨(recordK.output.preparation.followers.followers i).time,
            ((recordK.output.preparation.followers.followers i).row.2
              (recordK.output.preparation.followers.followers i).time).2 (0, i)⟩] := by
      simpa only [B, w, E, Q, recordK, kD, hW0Bank] using hpureBank
    rw [hentryK] at hpure'
    exact hpure'
  intro entry hentry
  have hentryBank : entry ∈ pureBank := by
    rw [← hpureEq]
    exact hentry
  rw [happendedPositive]
  rw [hpureBankB] at hentryBank
  rcases List.mem_append.mp hentryBank with hdrop | hlast
  · exact List.mem_append_left _ (List.mem_of_mem_drop hdrop)
  · exact List.mem_append_right _ hlast

private theorem original_calendar_awaited_witness
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (base k : ℕ) (hkB : k < B.length) (i : Fin (p.m - 1))
    (M : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (W : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hlookup : ∀ j : Fin B.length,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        (B[j.val]'j.isLt).input.time source = some (B[j.val]'j.isLt) ∧
      (B[j.val]'j.isLt).input.time.val = base + j.val)
    (hrows : ∀ j : Fin B.length, (B[j.val]'j.isLt).input.row =
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (hawait : ∀ j : Fin (k + 1),
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
          (B[j.val]'(by omega)).input.time).1 = some (0, i) →
      actualDownAwaitedCall rate (B[j.val]'(by omega)) i M)
    (hmember : ∀ e ∈ W, e ∈ actualDownPositives i (B.take (k + 1)))
    (htimes : ∀ e ∈ W, base ≤ e.time.val ∧ e.time.val ≤ (B[k]'hkB).input.time.val)
    (hsamples : ∀ e ∈ W, e.sample =
      ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 e.time).2 (0, i))
    (hsolve : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples W) M) :
    ∃ ha : base < p.T,
      let a : Fin p.T := ⟨base, ha⟩
      a.val ≤ (B[k]'hkB).input.time.val ∧
      (∀ e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p), e ∈ W →
        a.val ≤ e.time.val ∧ e.time.val ≤ (B[k]'hkB).input.time.val ∧
        AffineBatchDecoder.equation e.sample M ∧
        e.sample = ((source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 e.time).2 (0, i) ∧
        ∃ re : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h e.time source = some re ∧
          re.input.time = e.time ∧ e ∈ actualDownPositives i [re] ∧
          actualDownAwaitedCall rate re i M) ∧
      (∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ (B[k]'hkB).input.time.val →
        ReferenceSelectedAffinePairLaw.selectedChannel p
          ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v).1 =
            some (0, i) →
        ∃ rv : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h v source = some rv ∧
          rv.input.time = v ∧ actualDownAwaitedCall rate rv i M) := by
  have hdate : (B[k]'hkB).input.time.val = base + k := (hlookup ⟨k, hkB⟩).2
  have ha : base < p.T := by
    have ht := (B[k]'hkB).input.time.isLt
    rw [hdate] at ht
    omega
  refine ⟨ha, ?_⟩
  dsimp only
  refine ⟨by rw [hdate]; omega, ?_, ?_⟩
  · intro e he
    obtain ⟨re, hreTake, hetime, hdown, hsingle⟩ :=
      actual_down_positive_origin i (B.take (k + 1)) e (hmember e he)
    obtain ⟨j, hget⟩ := List.mem_iff_getElem?.mp hreTake
    have hjTake := (List.getElem?_eq_some_iff.mp hget).1
    have hjk : j ≤ k := by
      simp only [List.length_take] at hjTake
      omega
    have hjB : j < B.length := by omega
    have hgetB : B[j]? = some re := by
      rw [List.getElem?_take_of_lt (by omega)] at hget
      exact hget
    have hrecord : B[j]'hjB = re := (List.getElem?_eq_some_iff.mp hgetB).2
    let jB : Fin B.length := ⟨j, hjB⟩
    have hlookupRe : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h (B[j]'hjB).input.time source = some (B[j]'hjB) :=
      (hlookup jB).1
    rw [hrecord] at hlookupRe
    have hactualRe : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h e.time source = some re := by
      rw [hetime]
      exact hlookupRe
    have hdownB : ActiveFollowerDownAcceptance.downSelected p i
        (B[j]'hjB).input.row (B[j]'hjB).input.time := by
      rw [hrecord]
      exact hdown
    have hchannelB : ReferenceSelectedAffinePairLaw.selectedChannel p
        ((B[j]'hjB).input.row.2 (B[j]'hjB).input.time).1 = some (0, i) := by
      have hc := ReferenceSelectedAffinePairLaw.selectedChannel_of_down p
        ((B[j]'hjB).input.row.2 (B[j]'hjB).input.time).1 hdownB.1
      rw [hdownB.2] at hc
      exact hc
    have hchannelSource : ReferenceSelectedAffinePairLaw.selectedChannel p
        ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
          (B[j]'hjB).input.time).1 = some (0, i) := by
      rw [hrows jB] at hchannelB
      exact hchannelB
    have hawaitB : actualDownAwaitedCall rate (B[j]'hjB) i M :=
      hawait ⟨j, by omega⟩ hchannelSource
    rw [hrecord] at hawaitB
    exact ⟨(htimes e he).1, (htimes e he).2,
      (AffineBatchDecoder.satisfies_samples_iff W M).1 hsolve e he,
      hsamples e he, re, hactualRe, hetime.symm, hsingle, hawaitB⟩
  · intro v hstart hfinish hchannel
    let j := v.val - base
    have hjk : j ≤ k := by
      rw [hdate] at hfinish
      dsimp only [j]
      omega
    have hjB : j < B.length := by omega
    let jB : Fin B.length := ⟨j, hjB⟩
    let rv := B[j]'hjB
    have hcalendar : rv.input.time.val = base + j := (hlookup jB).2
    have htimeValue : rv.input.time.val = v.val := by
      dsimp only [j] at hcalendar
      omega
    have htime : rv.input.time = v := Fin.ext htimeValue
    have hchannelB : ReferenceSelectedAffinePairLaw.selectedChannel p
        ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
          rv.input.time).1 = some (0, i) := by
      rw [htime]
      exact hchannel
    have hawaitRv : actualDownAwaitedCall rate rv i M := hawait ⟨j, by omega⟩ hchannelB
    have hactualRv : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h v source = some rv := by
      rw [← htime]
      exact (hlookup jB).1
    exact ⟨rv, hactualRv, htime, hawaitRv⟩

/-- The old-prefix inclusive second-pure-DOWN detector has a full actual
awaited-word witness on the original finite calendar. -/
theorem actual_first_collection_old_down_awaited_batch_witness
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
    let s := ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let Q := AffineBatchDecoder.quota p
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      out.window = B ∧
      out.payload.sigma.val = s ∧
      (∀ i, (out.payload.downRecord i).val.sigma = s + 1 ∧
        (out.payload.downRecord i).val.q = 0) ∧
      ∀ i : Fin (p.m - 1),
        ∃ hBlen : 0 < B.length,
        ∃ cutoffState : ReferencePrelaunchFollower.State p rate.eta,
        ∃ cutoffMemory : ActiveFollowerLifecycle.LocalMemory p,
          (B[0]'hBlen).input.state.followers i = .ordinary cutoffState cutoffMemory ∧
          let W0 := cutoffState.downBatch
          let q := Q - W0.pending.length + Q
          W0.pending.length < Q ∧ Q < q ∧ q ≤ 2 * Q ∧
          ∀ b : ℕ, ∀ hb : b ≤ out.ell,
            ∃ hbound : s + (w + b) ≤ p.T,
            ∃ before : ReferencePrelaunchFollower.State p rate.eta,
            ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
              (ReferenceFirstCollectionDownThresholdAttainment.actualPrefix
                rate source rewards C_star C_h hcross count hspan b hbound).finalState.followers i =
                  .ordinary before memory ∧
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
                          _ = B.length := congrArg List.length out.windowIsActual
                      omega)).output.next) ∧
              (b = out.ell →
                (ReferenceFirstCollectionDownThresholdAttainment.actualPrefix
                  rate source rewards C_star C_h hcross count hspan b hbound).finalState =
                    d.record.output.next) ∧
              (b = 0 → before = cutoffState ∧ memory = cutoffMemory) ∧
              (before.lastDown = none →
                ∀ j : Fin b, ∃ prior priorMemory,
                  (B[j.val]'(by
                    have hle : out.ell ≤ B.length := by
                      calc
                        out.ell ≤ out.window.length := out.withinWindow
                        _ = B.length := congrArg List.length out.windowIsActual
                    omega)).input.state.followers i = .ordinary prior priorMemory ∧
                  prior.lastDown = none) ∧
              (before.lastDown = none →
                (ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take b)).length < q ∨
                  ∃ k : Fin out.ell, ∃ hkB : k.val < B.length,
                    0 < k.val ∧ k.val < b ∧
                    (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                      (B.take (k.val + 1))).length = q ∧
                    (∀ j : ℕ, j ≤ k.val →
                      (ReferenceFollowerDownDecoderReplay.actualDownPositives i (B.take j)).length < q) ∧
                    let r := B[k.val]'hkB
                    let t := r.input.time
                    let M := CoordinatorLocalArmChoice.storedDownFlatWord out.payload i
                    ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
                    r.input.time.val = s + w + k.val ∧
                    r.input.rows = source.1.2 ∧
                    r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                    r.input.rewards = rewards ∧
                    ReferenceSourcePrefixHistoryFiltration.actualRecord
                      rate rewards C_star C_h t source = some r ∧
                    ∃ W : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)),
                      ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i = some W ∧
                      ReferenceFirstLiveDownCompletionReadout.multipleSolutions W ∧
                      ∃ ha : s + w < p.T,
                        let a : Fin p.T := ⟨s + w, ha⟩
                        a.val ≤ t.val ∧
                        (∀ e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p), e ∈ W →
                          a.val ≤ e.time.val ∧ e.time.val ≤ t.val ∧
                          AffineBatchDecoder.equation e.sample M ∧
                          e.sample = ((source.1.2
                            (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 e.time).2 (0, i) ∧
                          ∃ re : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
                            ReferenceSourcePrefixHistoryFiltration.actualRecord
                              rate rewards C_star C_h e.time source = some re ∧
                            re.input.time = e.time ∧
                            e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [re] ∧
                            actualDownAwaitedCall rate re i M) ∧
                        (∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ t.val →
                          ReferenceSelectedAffinePairLaw.selectedChannel p
                            ((source.1.2
                              (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v).1 =
                                some (0, i) →
                          ∃ rv : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
                            ReferenceSourcePrefixHistoryFiltration.actualRecord
                              rate rewards C_star C_h v source = some rv ∧
                            rv.input.time = v ∧ actualDownAwaitedCall rate rv i M)) := by
  classical
  let s := ReferenceFirstCollectionReadyStream.startTime
    (rate := rate) source rewards C_star C_h
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let Q := AffineBatchDecoder.quota p
  have hOld := ReferenceFirstCollectionOldDownCountOrAmbiguity.actual_first_collection_old_down_count_or_ambiguity
    rate source rewards C_star C_h count hcross hspan hshort control0
  dsimp only [ReferenceFirstCollectionReadyStream.actualWindow,
    ReferenceFirstCollectionReadyStream.actualEpoch] at hOld
  rcases hOld with ⟨dOld, hwindowOld, hsigmaOld, hrecordsOld, hprefixOld⟩
  refine ⟨dOld, hwindowOld, hsigmaOld, hrecordsOld, ?_⟩
  intro i
  rcases hprefixOld i with ⟨hBlen, cutoffState, cutoffMemory, hcutoff,
    _hdomain, _hbuffer, _hdecoder, _hstartRound, hW0pending, hQbelow, hQupper,
    hprefix⟩
  refine ⟨hBlen, cutoffState, cutoffMemory, hcutoff, ?_⟩
  let W0 := cutoffState.downBatch
  let q := Q - W0.pending.length + Q
  change W0.pending.length < Q ∧ Q < q ∧ q ≤ 2 * Q ∧ _
  refine ⟨hW0pending, hQbelow, hQupper, ?_⟩
  intro b hb
  rcases hprefix b hb with ⟨hbound, before, memory, hInput, hOutput, hTerminal,
    hOrdinary, hAtZero, hPrior, hThreshold⟩
  refine ⟨hbound, before, memory, hOrdinary, hInput, hOutput, hTerminal, hAtZero, ?_⟩
  refine ⟨?_, ?_⟩
  · intro hnone
    exact hPrior hnone
  · intro hnone
    rcases hThreshold hnone with hsmall | hambiguous
    · exact Or.inl hsmall
    · rcases hambiguous with ⟨k, hkB, hkpos, hkb, hcount, hpriorCount, hrest⟩
      rcases hrest with ⟨hselected, hpositive, hdate, hrows, hselectedRow,
        hrewards, hstate⟩
      rcases hstate with ⟨current, currentMemory, hcurrentState, hcurrentNone,
        hcurrentBatch, hcurrentCollected, hcallData⟩
      rcases hcallData with ⟨loggedOld, cutOld, postOld, hloggedCurrent,
        hdownInputOld, hcutOld, hcutLocalOld, hphysicalOld, hpostOld,
        hExpectedOld, hbankOld⟩
      rcases hbankOld with ⟨firstOld, pureOld, hfirstLength, hpureLength,
        hbankAfterOld, hpostBankOld, hrawOld, hrawNone, hcomparisonFalse,
        hother⟩
      rcases hother with ⟨other, hotherNe, hsolveM, hsolveOther, _hhash,
        htimesOld, hsamplesOld, hcompletedOld, _hambigAfterStart, _hambigAfterInit,
        _hretainedFlag, hactualRecord, _hstrictFlag, _hcohort, _hlaunchData⟩
      have hMulti : ReferenceFirstLiveDownCompletionReadout.multipleSolutions pureOld := by
        apply (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff pureOld).2
        exact ⟨CoordinatorLocalArmChoice.storedDownFlatWord dOld.stream.payload i,
            other, hsolveM, hsolveOther, hotherNe.symm⟩
      have hkBlen : k.val < B.length := hkB
      have hselectedB : ActiveFollowerDownAcceptance.downSelected p i
          (B[k.val]'hkBlen).input.row (B[k.val]'hkBlen).input.time := hselected
      have hentries := actual_pure_bank_prefix_membership rate source rewards C_star C_h
        count hcross hspan hshort dOld i cutoffState cutoffMemory k hkpos hkB hBlen hcutoff
        current currentMemory hcurrentState hcurrentNone hselected hpositive hcount
        loggedOld hdownInputOld firstOld pureOld hbankAfterOld
      have hrecordOld : dOld.stream.window[k.val]'(Nat.lt_of_lt_of_le k.isLt
          dOld.stream.withinWindow) = B[k.val]'hkBlen := getElem_congr_coll hwindowOld
      have hfiOld : (dOld.stream.window[k.val]'(Nat.lt_of_lt_of_le k.isLt
          dOld.stream.withinWindow)).input.state.followers i = .ordinary current currentMemory := by
        rw [hrecordOld]
        exact hcurrentState
      have hcallsAwaited := actual_selected_down_calls rate source rewards C_star C_h
        count hcross hspan hshort dOld k (by omega) i current currentMemory hfiOld hcurrentNone
      have hAwaitedAtIndex :
          ∀ j : Fin (k.val + 1),
            ReferenceSelectedAffinePairLaw.selectedChannel p
              ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
                (B[j.val]'(by omega)).input.time).1 = some (0, i) →
            actualDownAwaitedCall rate (B[j.val]'(by omega)) i
              (CoordinatorLocalArmChoice.storedDownFlatWord dOld.stream.payload i) := by
        intro j hchannel
        have hjB : j.val < B.length := by omega
        let jB : Fin B.length := ⟨j.val, hjB⟩
        have hfields :=
          (ReferenceFirstCollectionFormedUpAwaitedFailure.actual_window_source_fields
            (rate := rate) (source := source) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) (count := count) (hcross := hcross) (hspan := hspan) hshort) jB
        have hrow : (B[j.val]'hjB).input.row =
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
          rw [ReferenceActivePhysicalStep.RoundInput.row, hfields.1, hfields.2.1]
        have hchannelRecord : ReferenceSelectedAffinePairLaw.selectedChannel p
            ((B[j.val]'hjB).input.row.2 (B[j.val]'hjB).input.time).1 = some (0, i) := by
          rw [hrow]
          exact hchannel
        have hdown : ActiveFollowerDownAcceptance.downSelected p i
            (B[j.val]'hjB).input.row (B[j.val]'hjB).input.time := by
          change PublicDiscreteDraws.slotDraw _ = PublicDiscreteDraws.downSlot ∧
            PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K _ = i
          unfold ReferenceSelectedAffinePairLaw.selectedChannel
            ReferenceSelectedAffinePairLaw.channelFromDraws at hchannelRecord
          split at hchannelRecord
          · exact ⟨by assumption, (Prod.mk.inj (Option.some.inj hchannelRecord)).2⟩
          · split at hchannelRecord <;> cases hchannelRecord
        let jD : Fin (k.val + 1) := ⟨j.val, j.isLt⟩
        have hjWindow : j.val < dOld.stream.window.length := by
          have := dOld.stream.withinWindow
          omega
        have hrecordJ : dOld.stream.window[j.val]'hjWindow = B[j.val]'hjB :=
          getElem_congr_coll hwindowOld
        have hdownD' : ActiveFollowerDownAcceptance.downSelected p i
            (dOld.stream.window[j.val]'hjWindow).input.row
            (dOld.stream.window[j.val]'hjWindow).input.time := by
          rw [hrecordJ]
          exact hdown
        have hawait := hcallsAwaited jD hdownD'
        change actualDownAwaitedCall rate (dOld.stream.window[j.val]'hjWindow) i
          (CoordinatorLocalArmChoice.storedDownFlatWord dOld.stream.payload i) at hawait
        rw [hrecordJ] at hawait
        exact hawait
      let kB : Fin B.length := ⟨k.val, hkBlen⟩
      have hlookupK :=
        (ReferenceFirstCollectionFormedUpAwaitedFailure.actual_window_lookup
          (rate := rate) (source := source) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (count := count) (hcross := hcross) (hspan := hspan) hshort) kB
      have hfieldsK :=
        (ReferenceFirstCollectionFormedUpAwaitedFailure.actual_window_source_fields
          (rate := rate) (source := source) (rewards := rewards) (C_star := C_star)
          (C_h := C_h) (count := count) (hcross := hcross) (hspan := hspan) hshort) kB
      have hdateB : (B[k.val]'hkBlen).input.time.val = s + w + k.val :=
        hlookupK.2
      have hrowsB : (B[k.val]'hkBlen).input.rows = source.1.2 := hfieldsK.1
      have hselectedRowB : (B[k.val]'hkBlen).input.selected =
          ActualInitializationPhysicalStep.selectedRowIndex p source := hfieldsK.2.1
      have hrewardsB : (B[k.val]'hkBlen).input.rewards = rewards := hfieldsK.2.2
      have hactualRecordB : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h (B[k.val]'hkBlen).input.time source =
            some (B[k.val]'hkBlen) := hlookupK.1
      have hcompletedB :
          ReferenceFirstLiveDownCompletionReadout.completedDownBatch (B[k.val]'hkBlen) i =
            some pureOld := hcompletedOld
      refine Or.inr ⟨k, hkBlen, hkpos, hkb, hcount, hpriorCount,
        hselectedB, hdateB, hrowsB, hselectedRowB, hrewardsB, hactualRecordB,
        pureOld, hcompletedB, hMulti, ?_⟩
      have hlookupAll : ∀ j : Fin B.length,
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
            (B[j.val]'j.isLt).input.time source = some (B[j.val]'j.isLt) ∧
          (B[j.val]'j.isLt).input.time.val = (s + w) + j.val :=
        ReferenceFirstCollectionFormedUpAwaitedFailure.actual_window_lookup
          rate source rewards C_star C_h count hcross hspan hshort
      have hrowsAll : ∀ j : Fin B.length, (B[j.val]'j.isLt).input.row =
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
        intro j
        have hfields :=
          (ReferenceFirstCollectionFormedUpAwaitedFailure.actual_window_source_fields
            (rate := rate) (source := source) (rewards := rewards) (C_star := C_star)
            (C_h := C_h) (count := count) (hcross := hcross) (hspan := hspan) hshort) j
        rw [ReferenceActivePhysicalStep.RoundInput.row, hfields.1, hfields.2.1]
      exact original_calendar_awaited_witness rate source rewards C_star C_h B (s + w)
        k.val hkBlen i (CoordinatorLocalArmChoice.storedDownFlatWord dOld.stream.payload i)
        pureOld hlookupAll hrowsAll hAwaitedAtIndex hentries htimesOld hsamplesOld hsolveM

end Bandits.Support.ReferenceFirstCollectionAwaitedDownBatchWitness

end
