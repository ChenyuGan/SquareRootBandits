/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFormedUpFirstThresholdReceiver
public import Bandits.Support.ReferenceCollectionUpFailureReadoutV2

/-!
# Actual formed UP replies and awaited failure

The witnesses here retain the original source, dispatch, reply and retained
DOWN origin. The interval includes every selected round, including zero
observations. These are internal compositions of the finite receiver facts.

Sources: `05_binary_transport.tex:27-55`, `06_interruptions.tex:476-481`,
and `appendix_a_local_protocol.tex:100-109,139-157` in the pinned manuscript.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceCollectionUpFailureReadoutV2

namespace Bandits.Support.ReferenceFirstCollectionFormedUpAwaitedFailure

variable {p : ConstructorDimensions.Parameters}

/-- A positive retained UP entry has the physical record's timestamp, and a
single record contributes at most one entry. -/
public theorem record_up_positive_origin
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) :
    (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i).length ≤ 1 ∧
    ∀ e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i,
      e.time = r.input.time ∧
      ∃ diagnostic, r.output.coordinator.up = some diagnostic ∧
        diagnostic.input.selectedFollower = i ∧
        AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input) ∧
        AffineBatchDecoder.positiveAt p (CoordinatorUpReception.traceAt diagnostic.input)
          diagnostic.input.time = [e] := by
  classical
  cases hd : r.output.coordinator.up with
  | none => simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd]
  | some diagnostic =>
    by_cases hi : diagnostic.input.selectedFollower = i
    · obtain ⟨L, hsite, hledger, hbank, htime, hrest⟩ :=
        ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r diagnostic hd
      by_cases he : AffineBatchDecoder.eligible
          (CoordinatorUpReception.roundInput diagnostic.input)
      · simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd,
          ReferenceCoordinatorUpDecoderReplay.retainedUpFollower,
          ReferenceCoordinatorUpDecoderReplay.retainedUpTime, hi,
          ite_true, AffineBatchDecoder.positiveAt,
          ReferenceCoordinatorUpDecoderReplay.constantInputTrace, he, List.length_singleton,
          Nat.le_refl, true_and, List.mem_singleton]
        intro e heq
        subst e
        refine ⟨htime, diagnostic, rfl, hi, he, ?_⟩
        simp only [CoordinatorUpReception.traceAt, he,
          ite_true, AffineBatchDecoder.entry,
          ReferenceCoordinatorUpDecoderReplay.constantInputTrace]
      · simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd,
          ReferenceCoordinatorUpDecoderReplay.retainedUpFollower,
          hi, AffineBatchDecoder.positiveAt,
          ReferenceCoordinatorUpDecoderReplay.constantInputTrace, he]
    · simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd,
        ReferenceCoordinatorUpDecoderReplay.retainedUpFollower, hi]

/-- A retained positive selects its actual physical UP channel. -/
public theorem record_up_positive_selected
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i) :
    ReferenceSelectedAffinePairLaw.selectedChannel p (r.input.row.2 r.input.time).1 =
      some (1, i) := by
  obtain ⟨htime, diagnostic, hd, hi, heligible, hpositive⟩ :=
    (record_up_positive_origin r i).2 e he
  obtain ⟨L, hsite, hledger, hbank, htime', hown, hselected, hsample, hslot, hrest⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r diagnostic hd
  have hgate := (CoordinatorUpReception.roundInput_selected_iff_gate diagnostic.input).mp
    heligible.1
  have hslotDraw : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
      PublicDiscreteDraws.upSlot := hslot.symm.trans hgate.2.1
  rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _ hslotDraw]
  have hselectedDraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 r.input.time).1 = i := by
    rw [← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
    exact hselected.symm.trans hi
  rw [hselectedDraw]
  rfl

/-- Dropping at least one positive removes the possible single contribution
of the first physical record, even if that record contributes no equation. -/
public theorem second_batch_origins
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (f b residual : ℕ) (hresidual : 0 < residual)
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : e ∈ (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
      ((records.drop f).take (b - f)) i).drop residual) :
    ∃ k : Fin records.length, max f 1 ≤ k.val ∧ k.val < b ∧
      e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries records[k.val] i := by
  classical
  let S := (records.drop f).take (b - f)
  have htail : e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (S.drop 1) i := by
    cases hs : S with
    | nil =>
      change e ∈ (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i).drop residual at he
      simp [hs, ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries] at he
    | cons head tail =>
      have hlen : (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries head i).length ≤
          residual := (record_up_positive_origin head i).1.trans (by omega)
      change e ∈ (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i).drop residual at he
      rw [hs] at he
      simp only [ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries,
        List.flatMap_cons, List.drop_append,
        List.drop_eq_nil_of_le hlen, List.nil_append] at he
      exact List.mem_of_mem_drop he
  obtain ⟨r, hr, heRecord⟩ := List.mem_flatMap.mp htail
  obtain ⟨a, ha, hr⟩ := List.mem_iff_getElem.mp hr
  have ha' : a + 1 < min (b - f) (records.length - f) := by
    simp only [S, List.length_drop, List.length_take] at ha
    omega
  have hk : f + (1 + a) < records.length := by omega
  have hrecord : records[f + (1 + a)] = r := by
    simpa only [S, List.getElem_drop, List.getElem_take] using hr
  refine ⟨⟨f + (1 + a), hk⟩, ?_, ?_, ?_⟩
  · change max f 1 ≤ f + (1 + a)
    omega
  · change f + (1 + a) < b
    omega
  · rw [hrecord]
    exact heRecord

section ActualWindow

variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (source : BootstrapPrivateRoundStreams.SourceInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ) (count : ℕ)
variable (hcross : (ReferenceInitializationRun.output
  (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
variable (hspan : ReferenceInitializationRun.elapsed p
  (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)

/-- The full original-source lookup agrees with every actual collection-window
record. This uses finite-run alignment and the full suffix on the same launch. -/
public theorem actual_window_lookup (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ k : Fin B.length,
    lookup rate rewards C_star C_h (B[k.val]'k.isLt).input.time source = some (B[k.val]'k.isLt) ∧
    (B[k.val]'k.isLt).input.time.val = s + w + k.val := by
  intro E w s B k
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  have halign := ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
    rate source rewards C_star C_h count hcross hspan hshort k
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some initial :=
    Option.eq_some_of_isSome
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).2 hcross)
  have hactive := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  have htime : (B[k.val]'k.isLt).input.time.val = s + w + k.val := by
    have ht := halign.2.1
    change B[k.val].input.time.val + 1 = s + w + 1 + k.val at ht
    omega
  have hcount : (E).records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hindex : w + k.val < count := by
    have hi := (List.getElem?_eq_some_iff.mp halign.1).1
    rwa [hcount] at hi
  have hrecord : (B[k.val]'k.isLt) = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s (w + k.val) (by omega) hactive := by
    have hat := ReferenceLocalReleaseGateChronology.run_record_at initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s hactive count
      hspan ⟨w + k.val, hindex⟩
    apply Option.some.inj
    calc
      some (B[k.val]'k.isLt) = (E).records[w + k.val]? := halign.1.symm
      _ = _ := by
        rw [List.getElem?_eq_getElem (by rw [hcount]; exact hindex)]
        simpa only [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
          initial] using congrArg some hat
  have hlookup := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h (B[k.val]'k.isLt).input.time source initial hlaunch
    (by change s ≤ (B[k.val]'k.isLt).input.time.val; omega)
  have hlookup' : lookup rate rewards C_star C_h (B[k.val]'k.isLt).input.time source =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
        (w + k.val) (by omega) hactive) := by
    simpa only [show ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = s by rfl,
      htime, Nat.add_assoc, Nat.add_sub_cancel_left] using hlookup
  exact ⟨hlookup'.trans (congrArg some hrecord.symm), htime⟩

/-- The window retains the original whole rows, private row index and reward
table. These equalities come from the canonical run's input theorem. -/
public theorem actual_window_source_fields
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ k : Fin B.length,
      B[k.val].input.rows = source.1.2 ∧
      B[k.val].input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      B[k.val].input.rewards = rewards := by
  intro E w B k
  have halign := ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
    rate source rewards C_star C_h count hcross hspan hshort k
  have hmem : B[k.val] ∈ E.records :=
    List.mem_iff_getElem?.mpr ⟨w + k.val, halign.1⟩
  exact ReferenceActivePhysicalHorizon.run_record_inputs
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards _ count hspan
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1 B[k.val] hmem

/-- Actual collection records are strictly ordered by their calendar stamps. -/
public theorem actual_window_chronological (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    B.Pairwise (fun earlier later => earlier.input.time.val < later.input.time.val) := by
  intro E w B
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  apply List.pairwise_iff_getElem.mpr
  intro a b ha hb hab
  have hta := (actual_window_lookup rate source rewards C_star C_h count
    hcross hspan hshort ⟨a, ha⟩).2
  have htb := (actual_window_lookup rate source rewards C_star C_h count
    hcross hspan hshort ⟨b, hb⟩).2
  change B[a].input.time.val = s + w + a at hta
  change B[b].input.time.val = s + w + b at htb
  omega

/-- Reconstruct awaiting for the same admissible reply and retained DOWN
origin, at every selected positive collection index. No positivity is assumed. -/
public theorem actual_formed_up_selected_rounds
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
    let out := d.stream
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let hB : out.ell ≤ (B).length := by
      calc
        out.ell ≤ out.window.length := out.withinWindow
        _ = B.length := congrArg List.length out.windowIsActual
    ∀ (n : Fin out.ell) (hn : 0 < n.val) (i : Fin (p.m - 1)),
      i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
    ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (B[n.val]'(n.isLt.trans_le hB)).input.state.followers i = .ordinary state memory →
      state.lastDown = some (out.payload.downRecord i) →
    ∀ (U : UP (p := p) (rate := rate)),
      U.val = ActiveFollowerQueueOperation.upOfferFields state →
    ∀ (j : Fin (E).records.length), j.val < w + n.val →
      ReferenceAcceptedUpFollowerHistory.RetainedDown ((E).records[j.val]'j.isLt) i
        (out.payload.downRecord i) →
    let f := if j.val < w then 0 else j.val - w + 1
    1 ≤ U.val.sigma ∧
      ∀ (k : Fin (B).length), max f 1 ≤ k.val → k.val ≤ n.val →
        ReferenceSelectedAffinePairLaw.selectedChannel p
          ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
            (B[k.val]'k.isLt).input.time).1 = some (1, i) →
        awaitedUpAt rate (B[k.val]'k.isLt) i U := by
  classical
  intro out E w B hB n hn i hi state memory hstate hdown U hU j hj hretained f
  obtain ⟨dO, registers, owned, base, cutRecord, hcut, hcutState,
    hcutPayload, hcutPending, hBpos, hBzero, hcutoff, hqueries⟩ :=
    ReferenceFirstCollectionFormedUpOfferReceiver.actual_initialized_first_collection_formed_up_offer_receiver
      rate source rewards C_star C_h count hcross hspan hshort
  let outO := dO.stream
  have hwindow : out.window = B := out.windowIsActual
  have hwindowO : outO.window = B := outO.windowIsActual
  let nB : Fin (B).length := ⟨n.val, n.isLt.trans_le hB⟩
  have hQ := ReferenceFirstCollectionPendingObservation.Q_window
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source count hcross hspan hshort d nB
  have hQO := ReferenceFirstCollectionPendingObservation.Q_window
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source count hcross hspan hshort dO nB
  change ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
    (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    B[n.val].input.time source =
      if n.val = 0 then Finset.univ else
        if hk : n.val < out.ell then (out.ledgers ⟨n.val - 1, by omega⟩).pending else ∅ at hQ
  change ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
    (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    B[n.val].input.time source =
      if n.val = 0 then Finset.univ else
        if hk : n.val < outO.ell then (outO.ledgers ⟨n.val - 1, by omega⟩).pending else ∅ at hQO
  have hQeq : ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      (B[n.val]'(n.isLt.trans_le hB)).input.time source = (out.ledgers ⟨n.val - 1, by omega⟩).pending := by
    simpa only [nB, show n.val ≠ 0 by omega, ite_false, n.isLt, dite_true] using hQ
  have hnO : n.val < outO.ell := by
    by_contra hnot
    have hempty : ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (B[n.val]'(n.isLt.trans_le hB)).input.time source = ∅ := by
      simpa only [nB, show n.val ≠ 0 by omega, ite_false, hnot, dite_false] using hQO
    rw [hempty] at hQeq
    have : i ∈ (∅ : Finset (Fin (p.m - 1))) := hQeq.symm ▸ hi
    exact Finset.notMem_empty i this
  let nO : Fin outO.ell := ⟨n.val, hnO⟩
  have hiO : i ∈ (outO.ledgers ⟨n.val - 1, by omega⟩).pending := by
    have heq : ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (B[n.val]'(n.isLt.trans_le hB)).input.time source = (outO.ledgers ⟨n.val - 1, by omega⟩).pending := by
      simpa only [nB, show n.val ≠ 0 by omega, ite_false, hnO, dite_true] using hQO
    rw [← heq, hQeq]
    exact hi
  obtain ⟨jR, rR, incomingR, cellR, hjR, hrR, hserviceR, hpreviousR⟩ :=
    out.cell_at n hn
  obtain ⟨rO, incomingO, cellO, stateO, memoryO, hrO, htimeO, hrowsO,
    hselectedO, hrewardsO, hpreviousO, hiIncomingO, hreadyO, hserviceO,
    hstateO, hstatusO, hdomainO, hSO, hdeltaO, hbacklogO, hmassO, hbankO,
    hcompletedO, hlastO, hformedO⟩ := hqueries nO hn i hiO
  have hrReq : rR = (B[n.val]'(n.isLt.trans_le hB)) := by
    rw [hwindow] at hrR
    exact (List.getElem?_eq_some_iff.mp hrR).2.symm
  have hrOeq : rO = (B[n.val]'(n.isLt.trans_le hB)) := by
    rw [hwindowO] at hrO
    exact (List.getElem?_eq_some_iff.mp hrO).2.symm
  have hpayload : outO.payload = out.payload := by
    have hcoordR := cellR.readyInput.1
    have hcoordO := cellO.readyInput.1
    rw [hrReq] at hcoordR
    rw [hrOeq] at hcoordO
    exact (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
      (hcoordO.symm.trans hcoordR)).1
  have hconfig : stateO = state ∧ memoryO = memory := by
    rw [hrOeq, hstate] at hstateO
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hstateO.symm)
  rcases hconfig with ⟨hstateEq, hmemoryEq⟩
  subst stateO
  subst memoryO
  have hdownO : state.lastDown = some (outO.payload.downRecord i) := by
    rw [hpayload]
    exact hdown
  obtain ⟨UO, hUO, hsigmaO, hpositive, hcurrentO, hdownSigmaO, hstartO,
    jO, hjOIndex, acceptedO, hjO, hacceptedO, hretainedO, hdiagnosticsO,
    hacceptedTimeO, hacceptedRowsO, hacceptedSelectedO, hacceptedRewardsO,
    huniqueO, hfO, hfnO, hdateO, hjwO, hjw1O, hnestedO, hAt⟩ := hformedO hdownO
  have hUeq : UO = U := Subtype.ext (hUO.trans hU.symm)
  subst UO
  have hjeq : j.val = jO := by
    apply huniqueO j.val j.isLt ((E).records[j.val]'j.isLt) hj
    · exact List.getElem?_eq_getElem j.isLt
    · rw [hpayload]
      exact hretained
  refine ⟨hpositive, ?_⟩
  intro k hfk hkn hchannel
  have hkpos : 0 < k.val := by omega
  have hfkO : (if jO < w then 0 else jO - w + 1) ≤ k.val := by
    rw [← hjeq]
    change f ≤ k.val
    omega
  obtain ⟨choice, choiceMemory, hchoice, hchoiceDomain, hchoiceStatus,
    hreply, hchoiceDown, hchoiceS, hchoiceDelta, hchoiceBacklog,
    hchoiceRow, hchoiceFollower, hchoiceActivation, hchoiceTime,
    before, beforeMemory, hbefore, hbeforeDomain, hstartBefore,
    hreplyBefore, hpendingCases, hoffers, hzero, hpositiveK⟩ := hAt k hfkO hkn
  obtain ⟨jK, recordK, incomingK, cellK, hjK, hrK, hserviceK, hpreviousK,
    hrecordK, hcoordK, htimeK, hrowsK, hselectedK, hrewardsK,
    hchoiceBefore, hmemoryBefore, tail, recording, L, diagnostic,
    htail, htailPayload, htailLedger, hrecording, hstarted, hL,
    hsite, hcheck, hdiagnostic, hinput, hreception, hnoninvalid,
    hdiagnosticTime, hsample, hown, hipending, haccept, haccepted⟩ := hpositiveK hkpos
  have hrecordKeq : recordK = (B[k.val]'k.isLt) := by
    exact hrecordK.symm
  have hdraw : PublicDiscreteDraws.slotDraw (recordK.input.row.2 recordK.input.time).1 =
        PublicDiscreteDraws.upSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (recordK.input.row.2 recordK.input.time).1 = i := by
    have hc : ReferenceSelectedAffinePairLaw.selectedChannel p
        (recordK.input.row.2 recordK.input.time).1 = some (1, i) := by
      change ReferenceSelectedAffinePairLaw.selectedChannel p
        ((recordK.input.rows recordK.input.selected).2 recordK.input.time).1 = some (1, i)
      rw [hrowsK, hselectedK, hrecordKeq]
      exact hchannel
    unfold ReferenceSelectedAffinePairLaw.selectedChannel
      ReferenceSelectedAffinePairLaw.channelFromDraws at hc
    split at hc
    · have hbad : (0 : Fin 2) = 1 := congrArg Prod.fst (Option.some.inj hc)
      exact ((by decide : (0 : Fin 2) ≠ 1) hbad).elim
    · split at hc
      · exact ⟨by assumption, congrArg Prod.snd (Option.some.inj hc)⟩
      · cases hc
  obtain ⟨L', hsite', hledger', hbank', htime', hown', hselected', hsample',
    hslot', hremaining⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
      recordK diagnostic hdiagnostic
  have hLL : L' = L := Option.some.inj (hsite'.symm.trans hsite)
  have hledger : diagnostic.input.ledger = L := hledger'.trans hLL
  have hselected : diagnostic.input.selectedFollower = i := by
    rw [hselected', CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
    exact hdraw.2
  have hslot : diagnostic.input.slot = PublicDiscreteDraws.upSlot :=
    hslot'.trans hdraw.1
  have hcheck' : CoordinatorUpReception.receptionInputCheck diagnostic.input = true := by
    rw [hinput]
    exact hcheck
  have hdomain := (CoordinatorUpReception.receptionInputCheck_eq_true_iff
    diagnostic.input).mp hcheck'
  have hgate : CoordinatorUpReception.receptionGate diagnostic.input := by
    refine ⟨?_, hslot, ?_⟩
    · exact hdomain.2.2.2.2.1.trans_eq hdomain.2.2.2.2.2.2.1
    · rw [hselected, hledger]
      exact hipending
  have hslotRecord : PublicDiscreteDraws.slotDraw
      ((ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B k).input.row.2
        (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B k).input.time).1 =
      PublicDiscreteDraws.upSlot := by
    rw [hrecordK]
    exact hdraw.1
  have hselectedRecord : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      ((ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B k).input.row.2
        (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B k).input.time).1 = i := by
    rw [hrecordK]
    exact hdraw.2
  have hoff := hoffers hslotRecord hselectedRecord
  have hpreparedExpected := hoff.2.2.2
  rw [hrecordK] at hpreparedExpected
  have hexpected : diagnostic.expected = some (enc rate U) := by
    calc
      diagnostic.expected = ReferenceActiveAffinePositiveTest.upSent recordK.input :=
        ReferenceGeneratedUpBatchPrefixEvent.actualRecordUpDiagnostic_expected
          recordK diagnostic hdiagnostic
      _ = some (enc rate U) := hpreparedExpected
  rw [← hrecordKeq]
  refine ⟨diagnostic, hdiagnostic, hselected, hcheck', hgate, hexpected, ?_⟩
  rw [hledger]
  exact haccept

/-- Collect the proved original-source window facts with the same dispatch's
formed-reply awaiting theorem, before introducing the finite second batch. -/
public theorem actual_formed_up_source_data
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
    let out := d.stream
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let hB : out.ell ≤ (B).length := by
      calc
        out.ell ≤ out.window.length := out.withinWindow
        _ = B.length := congrArg List.length out.windowIsActual
    ∀ (n : Fin out.ell) (hn : 0 < n.val) (i : Fin (p.m - 1)),
      i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
    ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (B[n.val]'(n.isLt.trans_le hB)).input.state.followers i = .ordinary state memory →
      state.lastDown = some (out.payload.downRecord i) →
    ∀ (U : UP (p := p) (rate := rate)),
      U.val = ActiveFollowerQueueOperation.upOfferFields state →
    ∀ (j : Fin (E).records.length), j.val < w + n.val →
      ReferenceAcceptedUpFollowerHistory.RetainedDown ((E).records[j.val]'j.isLt) i
        (out.payload.downRecord i) →
    let f := if j.val < w then 0 else j.val - w + 1
    (∀ k : Fin B.length,
      lookup rate rewards C_star C_h B[k.val].input.time source = some B[k.val] ∧
        B[k.val].input.time.val = s + w + k.val) ∧
    (∀ k : Fin B.length,
      B[k.val].input.rows = source.1.2 ∧
        B[k.val].input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
        B[k.val].input.rewards = rewards) ∧
    B.Pairwise (fun earlier later => earlier.input.time.val < later.input.time.val) ∧
    1 ≤ U.val.sigma ∧
      ∀ (k : Fin (B).length), max f 1 ≤ k.val → k.val ≤ n.val →
        ReferenceSelectedAffinePairLaw.selectedChannel p
          ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
            (B[k.val]'k.isLt).input.time).1 = some (1, i) →
        awaitedUpAt rate (B[k.val]'k.isLt) i U := by
  intro out E w s B hB n hn i hi state memory hstate hdown U hU j hj hretained f
  have hselected := actual_formed_up_selected_rounds
    rate source rewards C_star C_h count hcross hspan hshort d
    n hn i hi state memory hstate hdown U hU j hj hretained
  refine ⟨?_, ?_, ?_, hselected⟩
  · exact actual_window_lookup rate source rewards C_star C_h count hcross hspan hshort
  · exact actual_window_source_fields rate source rewards C_star C_h count hcross hspan hshort
  · exact actual_window_chronological rate source rewards C_star C_h count hcross hspan hshort

end ActualWindow

/-- Finite list assembly. Its original-source lookup, input-field and
awaiting inputs are all constructed by `actual_formed_up_source_data` at the
sole call below; none is an input to the public receiver theorem. -/
private theorem second_batch_failure_of_actual_window
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (B : List (Record (rate := rate))) (start : ℕ) (i : Fin (p.m - 1))
    (U : UP (p := p) (rate := rate)) (n f b : ℕ) (q : Fin B.length)
    (hqpos : 0 < q.val) (hfq : f ≤ q.val) (hqn : q.val ≤ n) (hqb : q.val + 1 = b)
    (hlookups : ∀ k : Fin B.length,
      lookup rate rewards C_star C_h B[k.val].input.time source = some B[k.val] ∧
        B[k.val].input.time.val = start + k.val)
    (hsourceFields : ∀ k : Fin B.length,
      B[k.val].input.rows = source.1.2 ∧
        B[k.val].input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
        B[k.val].input.rewards = rewards)
    (hchron : B.Pairwise (fun earlier later => earlier.input.time.val < later.input.time.val))
    (hUsigma : 1 ≤ U.val.sigma)
    (hawait : ∀ k : Fin B.length, max f 1 ≤ k.val → k.val ≤ n →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2
          B[k.val].input.time).1 = some (1, i) → awaitedUpAt rate B[k.val] i U) :
    let ch := (B[f]'(hfq.trans_lt q.isLt)).input.state.upDecoderBank i
    let Q := AffineBatchDecoder.quota p
    let S := (B.drop f).take (b - f)
    let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
    let P := AffineBatchDecoder.positives p tr (S.map (fun r => r.input.time))
    let W := P.drop (Q - ch.pending.length)
    ch.pending.length < Q → P.length = Q - ch.pending.length + Q →
    ∀ (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      B[q.val].output.coordinator.up = some diagnostic →
      last ∈ W → B[q.val].input.time = last.time →
      (diagnostic.input.upDecoderBank i).pending ++ [last] = W →
      (∀ e ∈ W, AffineBatchDecoder.equation e.sample (enc rate U)) →
      (∃ left right : AffineChannelLaw.Word (AffineBatchDecoder.width p),
        left ≠ right ∧ AffineBatchDecoder.satisfies (AffineBatchDecoder.samples W) left ∧
          AffineBatchDecoder.satisfies (AffineBatchDecoder.samples W) right) →
    let t := B[q.val].input.time
    ∃ a : Fin p.T,
      a.val = start + max f 1 ∧
      lookup rate rewards C_star C_h t source = some B[q.val] ∧
      completedUpBatch rate B[q.val] i = some W ∧ a.val ≤ t.val ∧
      1 ≤ U.val.sigma ∧ ReferenceFirstLiveDownCompletionReadout.multipleSolutions W ∧
      (∀ e ∈ W, a.val ≤ e.time.val ∧ e.time.val ≤ t.val ∧
        AffineBatchDecoder.equation e.sample (enc rate U) ∧
        ∃ re : Record (rate := rate), lookup rate rewards C_star C_h e.time source = some re ∧
          e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries re i ∧
          awaitedUpAt rate re i U) ∧
      (∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ t.val →
        ReferenceSelectedAffinePairLaw.selectedChannel p
          ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v).1 =
            some (1, i) →
        ∃ rv : Record (rate := rate), lookup rate rewards C_star C_h v source = some rv ∧
          awaitedUpAt rate rv i U) ∧
      fixedAwaitedUpFailureAt rate rewards C_star C_h source t := by
  classical
  intro ch Q S tr P W hch hPlength last diagnostic
    hdiagnostic hlast hlastTime hpending hequations hsolvers t
  have hresidual : 0 < Q - ch.pending.length := Nat.sub_pos_of_lt hch
  have hWlength : W.length = Q := by
    change (P.drop (Q - ch.pending.length)).length = Q
    rw [List.length_drop, hPlength]
    exact Nat.add_sub_cancel_left _ _
  have hchronS : S.Pairwise (fun earlier later =>
      earlier.input.time.val < later.input.time.val) := hchron.drop.take
  have hP : P = ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i :=
    ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained S i hchronS
  have horigins : ∀ e ∈ W, ∃ k : Fin B.length,
      max f 1 ≤ k.val ∧ k.val ≤ q.val ∧
        e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries B[k.val] i := by
    intro e he
    have he' : e ∈ (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i).drop
        (Q - ch.pending.length) := by
      change e ∈ P.drop (Q - ch.pending.length) at he
      rw [hP] at he
      exact he
    obtain ⟨k, hklo, hkhi, hmem⟩ :=
      second_batch_origins B i f b (Q - ch.pending.length) hresidual e he'
    exact ⟨k, hklo, Nat.le_of_lt_succ (by simpa only [← hqb] using hkhi), hmem⟩
  have hmaxq : max f 1 ≤ q.val := max_le hfq (Nat.succ_le_of_lt hqpos)
  have hstart : max f 1 < B.length := hmaxq.trans_lt q.isLt
  let startIndex : Fin B.length := ⟨max f 1, hstart⟩
  let a := B[startIndex.val].input.time
  have haTime : a.val = start + max f 1 :=
    (hlookups startIndex).2
  have hqLookup : lookup rate rewards C_star C_h t source = some B[q.val] ∧
      t.val = start + q.val := hlookups q
  have hat : a.val ≤ t.val := by
    rw [haTime, hqLookup.2]
    exact Nat.add_le_add_left hmaxq start
  have hentries : ∀ e ∈ W, a.val ≤ e.time.val ∧ e.time.val ≤ t.val ∧
      AffineBatchDecoder.equation e.sample (enc rate U) ∧
      ∃ re : Record (rate := rate), lookup rate rewards C_star C_h e.time source = some re ∧
        e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries re i ∧
        awaitedUpAt rate re i U := by
    intro e he
    obtain ⟨k, hklo, hkq, hmem⟩ := horigins e he
    have hstamp := ((record_up_positive_origin B[k.val] i).2 e hmem).1
    have hlookup := hlookups k
    have htime : e.time.val = start + k.val :=
      (congrArg Fin.val hstamp).trans hlookup.2
    have hfields := hsourceFields k
    have hchannel := record_up_positive_selected B[k.val] i e hmem
    change ReferenceSelectedAffinePairLaw.selectedChannel p
      ((B[k.val].input.rows B[k.val].input.selected).2 B[k.val].input.time).1 =
        some (1, i) at hchannel
    rw [hfields.1, hfields.2.1] at hchannel
    refine ⟨?_, ?_, hequations e he, B[k.val], ?_, hmem, hawait k hklo (hkq.trans hqn) hchannel⟩
    · rw [haTime, htime]
      exact Nat.add_le_add_left hklo start
    · rw [htime, hqLookup.2]
      exact Nat.add_le_add_left hkq start
    · rw [hstamp]
      exact hlookup.1
  have hcalendar : ∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ t.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v).1 =
          some (1, i) →
      ∃ rv : Record (rate := rate), lookup rate rewards C_star C_h v source = some rv ∧
        awaitedUpAt rate rv i U := by
    intro v hva hvt hchannel
    have hbase : start ≤ v.val := (Nat.le_add_right (start) (max f 1)).trans
      (haTime ▸ hva)
    have hkqNat : v.val - (start) ≤ q.val :=
      Nat.sub_le_iff_le_add'.mpr (hqLookup.2 ▸ hvt)
    have hkIndex : v.val - (start) < B.length := hkqNat.trans_lt q.isLt
    let k : Fin B.length := ⟨v.val - (start), hkIndex⟩
    have hklo : max f 1 ≤ k.val := Nat.le_sub_of_add_le' (haTime ▸ hva)
    have hkq : k.val ≤ q.val := hkqNat
    have hlookup := hlookups k
    have htime : B[k.val].input.time.val = start + (v.val - (start)) := hlookup.2
    have htimeEq : B[k.val].input.time = v :=
      Fin.ext (htime.trans (Nat.add_sub_of_le hbase))
    refine ⟨B[k.val], ?_, hawait k hklo (hkq.trans hqn) ?_⟩
    · simpa only [htimeEq] using hlookup.1
    · rw [htimeEq]
      exact hchannel
  have hlastRecord : last ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries B[q.val] i := by
    obtain ⟨k, hklo, hkq, hmem⟩ := horigins last hlast
    have hstamp := ((record_up_positive_origin B[k.val] i).2 last hmem).1
    have htime := (hlookups k).2
    have htimeEq : B[k.val].input.time = t := hstamp.symm.trans hlastTime.symm
    have hkEq : k = q := Fin.ext (Nat.add_left_cancel
      (htime.symm.trans ((congrArg Fin.val htimeEq).trans hqLookup.2)))
    simpa only [hkEq] using hmem
  obtain ⟨hlastStamp, diagnostic', hd', hselected, heligible, hpositive⟩ :=
    (record_up_positive_origin B[q.val] i).2 last hlastRecord
  have hdiagnosticEq : diagnostic' = diagnostic :=
    Option.some.inj (hd'.symm.trans hdiagnostic)
  rw [hdiagnosticEq] at hselected heligible hpositive
  obtain ⟨L, hsite, hcheckInput, hinput, hafter⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input B[q.val] diagnostic hdiagnostic
  have hcheck : CoordinatorUpReception.receptionInputCheck diagnostic.input = true := by
    rw [hinput]
    exact hcheckInput
  have happended : appendedUp rate diagnostic = W := by
    unfold appendedUp
    rw [hselected, hpositive]
    exact hpending
  have hcompletion : completedUpBatch rate B[q.val] i = some W := by
    apply (completedUpBatch_eq_some_iff rate B[q.val] i W).2
    refine ⟨diagnostic, hdiagnostic, hselected, hcheck, heligible, ?_, happended⟩
    rw [happended, hWlength]
  have hmultiple : ReferenceFirstLiveDownCompletionReadout.multipleSolutions W := by
    obtain ⟨left, right, hne, hleft, hright⟩ := hsolvers
    exact (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff W).2
      ⟨left, right, hleft, hright, hne⟩
  refine ⟨a, haTime, hqLookup.1, hcompletion, hat, hUsigma, hmultiple,
    hentries, hcalendar, ?_⟩
  exact ⟨B[q.val], i, U, W, a, hqLookup.1, hcompletion, hat, hUsigma,
    hmultiple, hentries, hcalendar⟩

section ActualWindow

variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (source : BootstrapPrivateRoundStreams.SourceInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ) (count : ℕ)
variable (hcross : (ReferenceInitializationRun.output
  (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
variable (hspan : ReferenceInitializationRun.elapsed p
  (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)

/-- The same actual second receiver batch supplies the literal awaited UP
failure. The finite dynamic inputs are projections of the actual first
threshold receiver; lookup, completion and both provenance clauses are proved
here rather than assumed. -/
public theorem actual_formed_up_receiver_awaited_failure
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
    let out := d.stream
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let hB : out.ell ≤ B.length := by
      calc
        out.ell ≤ out.window.length := out.withinWindow
        _ = B.length := congrArg List.length out.windowIsActual
    ∀ (n : Fin out.ell) (hn : 0 < n.val) (i : Fin (p.m - 1)),
      i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
    ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (B[n.val]'(n.isLt.trans_le hB)).input.state.followers i = .ordinary state memory →
      state.lastDown = some (out.payload.downRecord i) →
    ∀ U : UP (p := p) (rate := rate),
      U.val = ActiveFollowerQueueOperation.upOfferFields state →
    ∀ j : Fin E.records.length, j.val < w + n.val →
      ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i
        (out.payload.downRecord i) →
    let f := if j.val < w then 0 else j.val - w + 1
    ∀ (b : ℕ) (q : Fin B.length)
      (_hqpos : 0 < q.val) (hfq : f ≤ q.val) (_hqn : q.val ≤ n.val) (hqb : q.val + 1 = b),
    let ch := (B[f]'(hfq.trans_lt q.isLt)).input.state.upDecoderBank i
    let Q := AffineBatchDecoder.quota p
    let S := (B.drop f).take (b - f)
    let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
    let P := AffineBatchDecoder.positives p tr (S.map (fun r => r.input.time))
    let W := P.drop (Q - ch.pending.length)
    ch.pending.length < Q → P.length = Q - ch.pending.length + Q →
    ∀ (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      B[q.val].output.coordinator.up = some diagnostic →
      last ∈ W → B[q.val].input.time = last.time →
      (diagnostic.input.upDecoderBank i).pending ++ [last] = W →
      (∀ e ∈ W, AffineBatchDecoder.equation e.sample (enc rate U)) →
      (∃ left right : AffineChannelLaw.Word (AffineBatchDecoder.width p),
        left ≠ right ∧ AffineBatchDecoder.satisfies (AffineBatchDecoder.samples W) left ∧
          AffineBatchDecoder.satisfies (AffineBatchDecoder.samples W) right) →
    let t := B[q.val].input.time
    ∃ a : Fin p.T,
      a.val = s + w + max f 1 ∧
      lookup rate rewards C_star C_h t source = some B[q.val] ∧
      completedUpBatch rate B[q.val] i = some W ∧ a.val ≤ t.val ∧
      1 ≤ U.val.sigma ∧ ReferenceFirstLiveDownCompletionReadout.multipleSolutions W ∧
      (∀ e ∈ W, a.val ≤ e.time.val ∧ e.time.val ≤ t.val ∧
        AffineBatchDecoder.equation e.sample (enc rate U) ∧
        ∃ re : Record (rate := rate), lookup rate rewards C_star C_h e.time source = some re ∧
          e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries re i ∧
          awaitedUpAt rate re i U) ∧
      (∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ t.val →
        ReferenceSelectedAffinePairLaw.selectedChannel p
          ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v).1 =
            some (1, i) →
        ∃ rv : Record (rate := rate), lookup rate rewards C_star C_h v source = some rv ∧
          awaitedUpAt rate rv i U) ∧
      fixedAwaitedUpFailureAt rate rewards C_star C_h source t := by
  intro out E w s B hB n hn i hi state memory hstate hdown U hU j hj hretained f
    b q hqpos hfq hqn hqb ch Q S tr P W hch hPlength last diagnostic
    hdiagnostic hlast hlastTime hpending hequations hsolvers t
  obtain ⟨hlookups, hsourceFields, hchron, hUsigma, hawait⟩ := actual_formed_up_source_data
    rate source rewards C_star C_h count hcross hspan hshort d
    n hn i hi state memory hstate hdown U hU j hj hretained
  exact second_batch_failure_of_actual_window
    (rate := rate) (source := source) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (B := B) (start := s + w) (i := i) (U := U) (n := n.val) (f := f) (b := b) (q := q)
    hqpos hfq hqn hqb hlookups hsourceFields hchron hUsigma hawait
    hch hPlength last diagnostic hdiagnostic hlast hlastTime hpending hequations hsolvers

end ActualWindow

end Bandits.Support.ReferenceFirstCollectionFormedUpAwaitedFailure
