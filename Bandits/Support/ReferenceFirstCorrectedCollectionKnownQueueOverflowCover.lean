/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCollectionKnownQueueSource
public import Bandits.Support.ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow

import Mathlib.Tactic

/-!
# First corrected collection known-queue overflow sites

This module covers the retained collection coordinator's literal INPUT,
CHOICE, decoded, OUTPUT, and reached stage-(1) candidate queue registers,
together with the first excluded INPUT and CHOICE registers.  The event uses
the actual original source segment and leaves the source record and register
optional when they are absent.  Its probability bound is inherited from the
existing original-source all-arm numerical overflow event.

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:192-233,246-299,391-408,425-426`, and
`04_slow_fast_learner.tex:157-187,256-290`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
  (correctedCell sourceRecords sourceStart birthIndex liveTail prefixInputs prefixReadout)
open ReferenceCollectionSegmentExtraction
open scoped Classical

namespace Bandits.Support.ReferenceFirstCorrectedCollectionKnownQueueOverflowCover

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
local notation "Readout" => ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K

local instance sourceInputMeasurableSpace : MeasurableSpace X := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-! A constructor is a physical site identity.  Each queue is projected from
the ledger at that site; absent registers do not produce an integer. -/

inductive KnownQueueSourceSite (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (a : Fin p.K) (field : ReferenceFirstCorrectedCollectionKnownQueueSource.QueueRegisterField) :
    ℕ → Prop where
  | retainedInput {q : ℕ} (v : ℕ) (hv : v < seg.records.length)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (proposal : Option (Fin p.T × Bool))
      (hinput : (seg.records[v]'hv).input.state.coordinator =
        .collection seg.context.payload ledger proposal)
      (hqueue : ReferenceFirstCorrectedCollectionKnownQueueSource.knownSiteQueue?
        ledger a field = some q) :
      KnownQueueSourceSite seg a field q
  | retainedChoice {q : ℕ} (v : ℕ) (hv : v < seg.records.length)
      (call : ReferenceCollectionSegmentExtraction.Choice rate)
      (hchoice : ReferenceCollectionSegmentExtraction.choice
        (seg.records[v]'hv).input = some call)
      (hpayload : call.payload = seg.context.payload)
      (hqueue : ReferenceFirstCorrectedCollectionKnownQueueSource.knownSiteQueue?
        call.preLedger a field = some q) :
      KnownQueueSourceSite seg a field q
  | retainedDecoded {q : ℕ} (v : ℕ) (hv : v < seg.records.length)
      (done : ReferenceCollectionSegmentExtraction.CompletedRound rate)
      (hdone : ReferenceCollectionSegmentExtraction.extractRound (seg.records[v]'hv) = some done)
      (hchoice : ReferenceCollectionSegmentExtraction.choice (seg.records[v]'hv).input =
        some done.context)
      (hpayload : done.context.payload = seg.context.payload)
      (out : CoordinatorRecordingOperation.Output p)
      (hrecording : (seg.records[v]'hv).output.coordinator.recording = some out)
      (hrun : CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare (seg.records[v]'hv).input)
          done.context.payload done.context.started done.context.weights) = some out)
      (started decoded : ReferenceActivePhysicalStep.Ledger rate)
      (bank : CoordinatorUpReception.UpDecoderBank p)
      (hstart : CoordinatorCollectionLedger.startRound done.context.preLedger
        ((seg.records[v]'hv).input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled done.context.preLedger
          (seg.records[v]'hv).input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) =
          .success started)
      (hreceive : (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare (seg.records[v]'hv).input) started).result =
          (if done.accepted then .success (decoded, bank) else .rejected (decoded, bank)))
      (hfinish : CoordinatorCollectionLedger.finishRound decoded = .success done.final)
      (hqueue : ReferenceFirstCorrectedCollectionKnownQueueSource.knownSiteQueue?
        decoded a field = some q) :
      KnownQueueSourceSite seg a field q
  | retainedOutput {q : ℕ} (v : ℕ) (hv : v < seg.records.length)
      (done : ReferenceCollectionSegmentExtraction.CompletedRound rate)
      (hdone : ReferenceCollectionSegmentExtraction.extractRound (seg.records[v]'hv) = some done)
      (hpayload : done.context.payload = seg.context.payload)
      (proposal : Option (Fin p.T × Bool))
      (houtput : (seg.records[v]'hv).output.next.coordinator =
        .collection seg.context.payload done.final proposal)
      (hqueue : ReferenceFirstCorrectedCollectionKnownQueueSource.knownSiteQueue?
        done.final a field = some q) :
      KnownQueueSourceSite seg a field q
  | reachedStageOneCandidate {q : ℕ} (v : ℕ) (hv : v < seg.records.length)
      (call : ReferenceCollectionSegmentExtraction.Choice rate)
      (hchoice : ReferenceCollectionSegmentExtraction.choice
        (seg.records[v]'hv).input = some call)
      (hpayload : call.payload = seg.context.payload)
      (out : CoordinatorRecordingOperation.Output p)
      (hdiagnostic : (seg.records[v]'hv).coordinatorDiagnostics.recording = some out)
      (hrun : CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare (seg.records[v]'hv).input)
          call.payload call.started call.weights) = some out)
      (candidate : ReferenceActivePhysicalStep.Ledger rate)
      (hcandidate : ReferenceFirstCorrectedCollectionKnownQueueSource.reachedStageOneCandidate?
        call.preLedger (seg.records[v]'hv).input.time
        (ReferenceActivePhysicalStep.collectionEnabled call.preLedger
          (seg.records[v]'hv).input.time) out = some candidate)
      (hqueue : ReferenceFirstCorrectedCollectionKnownQueueSource.knownSiteQueue?
        candidate a field = some q) :
      KnownQueueSourceSite seg a field q
  | firstExcludedInput {q : ℕ} (record : Record)
      (hhead : seg.remaining.head? = some record)
      (proposal : Option (Fin p.T × Bool))
      (hinput : record.input.state.coordinator =
        .collection seg.context.payload seg.final proposal)
      (hqueue : ReferenceFirstCorrectedCollectionKnownQueueSource.knownSiteQueue?
        seg.final a field = some q) :
      KnownQueueSourceSite seg a field q
  | firstExcludedChoice {q : ℕ} (record : Record)
      (hhead : seg.remaining.head? = some record)
      (call : ReferenceCollectionSegmentExtraction.Choice rate)
      (hchoice : ReferenceCollectionSegmentExtraction.choice record.input = some call)
      (hcall : call.payload = seg.context.payload ∧ call.preLedger = seg.final ∧
        call.initializer = none)
      (hqueue : ReferenceFirstCorrectedCollectionKnownQueueSource.knownSiteQueue?
        call.preLedger a field = some q) :
      KnownQueueSourceSite seg a field q

/-- Literal threshold event for an observed integer in an actual first
corrected collection coordinator register site. -/
def firstCollectionKnownQueueOverflowEvent (u t : Fin p.T) : Set X :=
  {z | z ∈ correctedCell rate rewards C_star C_h u t ∧
    ∃ seg : ReferenceCollectionSegmentExtraction.Segment rate,
      ReferenceCollectionSegmentExtraction.segmentAt
        (sourceRecords rate rewards C_star C_h z)
        (birthIndex rate rewards C_star C_h z + 1 +
          (liveTail rate rewards C_star C_h z).length) = some seg ∧
      ∃ (a : Fin p.K) (field : ReferenceFirstCorrectedCollectionKnownQueueSource.QueueRegisterField)
        (q : ℕ),
        KnownQueueSourceSite rate seg a field q ∧
        (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)}

private theorem sourceRecord_actualRecord (_u _t : Fin p.T) (z : X) (date : Fin p.T)
    (e : ℕ) (hdate : sourceStart rate rewards C_star C_h z + e = date.val)
    (entry : Record) (hentry : (sourceRecords rate rewards C_star C_h z)[e]? = some entry) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h date z =
      some entry := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  change (if sourceStart rate rewards C_star C_h z ≤ date.val then
      (sourceRecords rate rewards C_star C_h z)[date.val -
        sourceStart rate rewards C_star C_h z]? else none) = some entry
  have hle : sourceStart rate rewards C_star C_h z ≤ date.val := by omega
  rw [ite_eq_left hle]
  have hindex : date.val - sourceStart rate rewards C_star C_h z = e := by omega
  rw [hindex]
  exact hentry

private theorem horizonCutoff_eq_record (_u _t : Fin p.T) (z : X) (q : Fin p.T)
    (entry : Record)
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h q z = some entry) :
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
      rate rewards C_star C_h q z =
        ReferenceCollectionPhaseHistory.cutoffChosen entry.input := by
  unfold ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?
  simp only [hrecord, Option.map_some, Option.bind_some]
  unfold ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag
    ReferenceCollectionPhaseHistory.cutoffChosen
  have hprepare : (ReferenceActivePhysicalStep.prepare entry.input).coordinator =
      ReferenceActivePhysicalStep.dispatch entry.input := rfl
  rw [hprepare]
  cases ReferenceActivePhysicalStep.dispatch entry.input with
  | live registers owned base outcome => cases outcome <;> rfl
  | first outcome => rfl
  | collection payload ledger clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

private theorem knownSegmentEndpoint (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt
      (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length) = some seg) :
    t.val + 1 ≤ sourceStart rate rewards C_star C_h z +
        (birthIndex rate rewards C_star C_h z + 1 +
          (liveTail rate rewards C_star C_h z).length) ∧
      sourceStart rate rewards C_star C_h z +
          (birthIndex rate rewards C_star C_h z + 1 +
            (liveTail rate rewards C_star C_h z).length) + seg.records.length ≤
        ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint
          rate rewards C_star C_h t z := by
  let R := sourceRecords rate rewards C_star C_h z
  let s := sourceStart rate rewards C_star C_h z
  let e := birthIndex rate rewards C_star C_h z + 1 +
    (liveTail rate rewards C_star C_h z).length
  have hnonempty : 0 < (R.drop e).length := by
    have hbranch := (ReferenceCollectionSegmentExtraction.segmentAt_branch R e seg hseg).1
    cases hdrop : R.drop e with
    | nil => simp [ReferenceCollectionSegmentExtraction.segment, hdrop] at hbranch
    | cons _ _ => simp
  have he : e < R.length := by
    have hlen : (R.drop e).length = R.length - e := List.length_drop
    omega
  obtain ⟨L, B, c, birth, payload, actualSeg, D, _hL, _hprefixBirth,
    _hLb, hdateBirth, _hb, _hborn, _hsigma, _hlater, hactualSeg, hentry,
    _hpay, hcut, _hfirstCut, hAlen, _heR, hprefixA, hDlen, _hDcells,
    _hDwords, _hinputWords, _hspan, _hprefixFull, _hrecords, _hprefixAll⟩ :=
      ReferenceFirstCorrectedCollectionKnownQueuePrefixReplay.firstCell_actual_segment_prefix_words
        rate rewards C_star C_h u t z hz he
  have hsameSeg : actualSeg = seg := Option.some.inj (hactualSeg.symm.trans hseg)
  subst actualSeg
  have hRlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  change R.length = p.T - s at hRlen
  have hde : s + e = t.val + 1 + (liveTail rate rewards C_star C_h z).length := by
    dsimp only [s, e]
    rw [← ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
      rate rewards C_star C_h u t z hz]
    omega
  have hlive := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength_actual
    rate rewards C_star C_h u t z hz
  let d := t.val + 1 +
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
      rate rewards C_star C_h t z
  have hde : s + e = d := by
    dsimp only [s, e, d]
    rw [← hlive]
    rw [← ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
      rate rewards C_star C_h u t z hz]
    omega
  have hse : s + e < p.T := by
    rw [hRlen] at he
    omega
  have hd : d < p.T := by
    rw [← hde]
    exact hse
  let date : Fin p.T := ⟨d, hd⟩
  have hdate : s + e = date.val := by
    dsimp only [date]
    exact hde
  have hsourceEntry : R[e]? = some seg.entry := by
    rw [hentry]
    exact List.getElem?_eq_getElem he
  have hactual := sourceRecord_actualRecord rate rewards C_star C_h u t z date e hdate
    seg.entry hsourceEntry
  have hcutRecord := horizonCutoff_eq_record rate rewards C_star C_h u t z date
    seg.entry hactual
  have hcutFlag : ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
      rate rewards C_star C_h date z = true := hcutRecord.trans hcut
  obtain ⟨entry, actualSeg, _hentry, _hcut, hseg', hendpoint⟩ :=
    ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint_eq_actualSegment_of_cutoff
      rate rewards C_star C_h u t z hz hd hcutFlag
  have hsameActual : actualSeg = seg := Option.some.inj (hseg'.symm.trans hseg)
  rw [hsameActual] at hendpoint
  constructor
  · rw [hde]
    omega
  · rw [hendpoint]
    exact Nat.le_max_right _ _

private theorem prefixCrossing_to_original_event (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (n : ℕ) (P : List (RecordedQueueRun.RoundInput p.K))
    (hinputs : prefixInputs rate rewards C_star C_h n z = some P)
    (hpositive : 0 < P.length)
    (hthreshold : ∃ a : Fin p.K,
      ((UnstoppedRecordedQueueComparison.unstoppedReplay Q P P.length a).2 : ℝ) /
        ((Q).n : ℝ) > 1 / (32 * (Q).eta))
    (hdateLo : t.val + 1 ≤ n)
    (hdateHi : n ≤ ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint
      rate rewards C_star C_h t z) :
    ∃ a : Fin p.K,
      z ∈ ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionOverflowEvent
        rate rewards C_star C_h u t a := by
  obtain ⟨a, hq⟩ := hthreshold
  have hcross : UnstoppedRecordedQueueComparison.replay_crosses_overflow Q P P.length :=
    (UnstoppedRecordedQueueComparison.replay_crosses_overflow_iff_normalized
      Q P P.length).2 ⟨a, hq⟩
  have hcrossExists : ∃ m, 1 ≤ m ∧ m ≤ P.length ∧
      UnstoppedRecordedQueueComparison.replay_crosses_overflow Q P m :=
    ⟨P.length, hpositive, le_rfl, hcross⟩
  have hfirst : UnstoppedRecordedQueueComparison.firstOverflowPrefix Q P ≤ P.length := by
    dsimp [UnstoppedRecordedQueueComparison.firstOverflowPrefix]
    rw [dite_eq_left hcrossExists]
    exact Nat.find_min' hcrossExists ⟨hpositive, le_rfl, hcross⟩
  have hrunOverflow : (RecordedQueueRun.run Q P).overflow = true := by
    have hprefix :=
      UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        Q P P.length (by omega)
    have h := hprefix.mpr hfirst
    simpa only [List.take_length] using h
  obtain ⟨detector, hdetector⟩ :=
    StoppedQueueBound.run_overflow_iff_terminal_threshold Q P |>.mp hrunOverflow
  let out : Readout := ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
    (RecordedQueueRun.run Q P)
  have hout : prefixReadout rate rewards C_star C_h n z = some out := by
    change (prefixInputs rate rewards C_star C_h n z).map
      (fun inputs => ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run Q inputs)) = some out
    rw [hinputs]
    rfl
  have hdetectorThreshold : ((out.1 detector).2 : ℝ) / ((Q).n : ℝ) >
      1 / (32 * rate.eta.val) := by
    simpa only [out, ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
      StoppedQueueBound.normalizedBacklog,
      ReferenceFirstLaunchNumericalCell.queueParameters] using hdetector
  exact ⟨detector, hz, n, hdateLo, hdateHi, out, hout, hdetectorThreshold⟩

private theorem knownCurrentQueue_eq {ledger : ReferenceActivePhysicalStep.Ledger rate}
    (a : Fin p.K) (q value : ℕ)
    (hqueue : ReferenceFirstCorrectedCollectionKnownQueueSource.knownSiteQueue?
      ledger a .current = some q)
    (hregister : ∀ current, ledger.currentRegisters a = some current → current.queue = value) :
    q = value := by
  rw [ReferenceFirstCorrectedCollectionKnownQueueSource.knownSiteQueue?_current] at hqueue
  obtain ⟨current, hreg, hvalue⟩ := Option.map_eq_some_iff.mp hqueue
  exact hvalue.symm.trans (hregister current hreg)

private theorem knownCutoffQueue_eq {ledger : ReferenceActivePhysicalStep.Ledger rate}
    (a : Fin p.K) (q value : ℕ)
    (hqueue : ReferenceFirstCorrectedCollectionKnownQueueSource.knownSiteQueue?
      ledger a .cutoff = some q)
    (hregister : ∀ cutoff, ledger.cutoffRegisters a = some cutoff → cutoff.queue = value) :
    q = value := by
  rw [ReferenceFirstCorrectedCollectionKnownQueueSource.knownSiteQueue?_cutoff] at hqueue
  obtain ⟨cutoff, hreg, hvalue⟩ := Option.map_eq_some_iff.mp hqueue
  exact hvalue.symm.trans (hregister cutoff hreg)

/-- Every witnessed physical register site supplies its own literal original
source prefix, whose stopped run records the first detecting update. -/
private theorem knownSite_has_original_prefix (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt
      (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 +
        (liveTail rate rewards C_star C_h z).length) = some seg)
    (a : Fin p.K) (field : ReferenceFirstCorrectedCollectionKnownQueueSource.QueueRegisterField)
    (q : ℕ) (hsite : KnownQueueSourceSite rate seg a field q)
    (hthreshold : (q : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    ∃ n : ℕ, ∃ P : List (RecordedQueueRun.RoundInput p.K),
      prefixInputs rate rewards C_star C_h n z = some P ∧
      0 < P.length ∧
      ((UnstoppedRecordedQueueComparison.unstoppedReplay Q P P.length a).2 : ℝ) /
        ((Q).n : ℝ) > 1 / (32 * (Q).eta) ∧
      t.val + 1 ≤ n ∧
      n ≤ ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint
        rate rewards C_star C_h t z := by
  let R := sourceRecords rate rewards C_star C_h z
  let s := sourceStart rate rewards C_star C_h z
  let e := birthIndex rate rewards C_star C_h z + 1 +
    (liveTail rate rewards C_star C_h z).length
  obtain ⟨A, D, hAlen, hDlen, hprefixA, hcells, hwords, hvalues,
    hsites, hcallSites, hboundary⟩ :=
    ReferenceFirstCorrectedCollectionKnownQueueSource.firstCell_collection_known_queue_source
      rate rewards C_star C_h u t z hz seg hseg
  have hgeometry := knownSegmentEndpoint rate rewards C_star C_h u t z hz seg hseg
  have hepos : 0 < e := by dsimp only [e]; omega
  have hprefixLength (v : ℕ) (hv : v ≤ D.length) :
      (A ++ D.take v).length = e + v := by
    rw [List.length_append, List.length_take, Nat.min_eq_left hv, hAlen]
  have hthresholdFor (P : List (RecordedQueueRun.RoundInput p.K))
      (hqr : q = (UnstoppedRecordedQueueComparison.unstoppedReplay Q P P.length a).2) :
      ((UnstoppedRecordedQueueComparison.unstoppedReplay Q P P.length a).2 : ℝ) /
          ((Q).n : ℝ) > 1 / (32 * (Q).eta) := by
    rw [hqr] at hthreshold
    simpa only [ReferenceFirstLaunchNumericalCell.queueParameters] using hthreshold
  have hsourceDate (v : ℕ) (hv : v ≤ D.length) :
      prefixInputs rate rewards C_star C_h (s + e + v) z =
        some (A ++ D.take v) := by
    have h := hvalues v hv
    change prefixInputs rate rewards C_star C_h (s + e + v) z =
      some (A ++ D.take v) ∧ _ ∧ _ at h
    exact h.1
  have hsourceBase : prefixInputs rate rewards C_star C_h (s + e) z = some A := by
    simpa only [Nat.add_zero] using hprefixA
  have hsourceFull : prefixInputs rate rewards C_star C_h (s + e + D.length) z =
      some (A ++ D) := by
    simpa only [List.take_length] using hsourceDate D.length le_rfl
  cases hsite with
  | retainedInput v hv ledger proposal hinput hqueue =>
      have hvD : v < D.length := by rw [hDlen]; exact hv
      have hvLe : v ≤ D.length := Nat.le_of_lt hvD
      obtain ⟨done, hdone, hchoice, hbefore, _hafter, hpreCurrent, hpreCutoff,
        hinputLedger, _hfinalCurrent, _hfinalCutoff, _houtput, _hactual⟩ := hsites v hv
      have hledger : ledger = done.context.preLedger :=
        hinputLedger _ _ _ hinput
      subst ledger
      cases field with
      | current =>
          let P := A ++ D.take v
          have hqr := knownCurrentQueue_eq (rate := rate) a q
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q P P.length a).2 hqueue
            (by intro current hreg; dsimp only [P]; exact hpreCurrent a current hreg)
          have hth := hthresholdFor P hqr
          have hpos : 0 < P.length := by
            dsimp only [P]
            rw [hprefixLength v hvLe]
            omega
          have hinputs : prefixInputs rate rewards C_star C_h (s + e + v) z = some P := by
            dsimp only [P]
            exact hsourceDate v hvLe
          refine ⟨s + e + v, P, hinputs, hpos, hth, ?_, ?_⟩
          · exact hgeometry.1.trans (by omega)
          · have hle : v ≤ seg.records.length := by rw [← hDlen]; exact hvLe
            have hbase : (s + e) + seg.records.length ≤
                ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint
                  rate rewards C_star C_h t z := by
              simpa only [s, e] using hgeometry.2
            exact (Nat.add_le_add_left hle (s + e)).trans hbase
      | cutoff =>
          have hqr := knownCutoffQueue_eq (rate := rate) a q
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2 hqueue
            (by intro cutoff hreg; simpa only [hAlen] using hpreCutoff a cutoff hreg)
          have hth := hthresholdFor A hqr
          have hpos : 0 < A.length := by rw [hAlen]; exact hepos
          refine ⟨s + e, A, hsourceBase, hpos, hth, hgeometry.1, ?_⟩
          have hbase : s + e + seg.records.length ≤
              ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint
                rate rewards C_star C_h t z := by
            simpa only [s, e] using hgeometry.2
          calc
            s + e ≤ s + e + seg.records.length := by omega
            _ ≤ _ := hbase
  | retainedChoice v hv call hchoice _hpayload hqueue =>
      have hvD : v < D.length := by rw [hDlen]; exact hv
      have hvLe : v ≤ D.length := Nat.le_of_lt hvD
      obtain ⟨done, _hdone, hsourceChoice, hbefore, _hafter, hpreCurrent,
        hpreCutoff, _hinputLedger, _hfinalCurrent, _hfinalCutoff, _houtput,
        _hactual⟩ := hsites v hv
      have hcall : call = done.context := Option.some.inj (hchoice.symm.trans hsourceChoice)
      subst call
      cases field with
      | current =>
          let P := A ++ D.take v
          have hqr := knownCurrentQueue_eq (rate := rate) a q
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q P P.length a).2 hqueue
            (by intro current hreg; dsimp only [P]; exact hpreCurrent a current hreg)
          have hth := hthresholdFor P hqr
          have hpos : 0 < P.length := by
            dsimp only [P]
            rw [hprefixLength v hvLe]
            omega
          have hinputs : prefixInputs rate rewards C_star C_h (s + e + v) z = some P := by
            dsimp only [P]
            exact hsourceDate v hvLe
          refine ⟨s + e + v, P, hinputs, hpos, hth, ?_, ?_⟩
          · exact hgeometry.1.trans (by omega)
          · have hle : v ≤ seg.records.length := by rw [← hDlen]; exact hvLe
            have hbase : (s + e) + seg.records.length ≤
                ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint
                  rate rewards C_star C_h t z := by
              simpa only [s, e] using hgeometry.2
            exact (Nat.add_le_add_left hle (s + e)).trans hbase
      | cutoff =>
          have hqr := knownCutoffQueue_eq (rate := rate) a q
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2 hqueue
            (by intro cutoff hreg; simpa only [hAlen] using hpreCutoff a cutoff hreg)
          have hth := hthresholdFor A hqr
          have hpos : 0 < A.length := by rw [hAlen]; exact hepos
          refine ⟨s + e, A, hsourceBase, hpos, hth, hgeometry.1, ?_⟩
          have hbase : s + e + seg.records.length ≤
              ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint
                rate rewards C_star C_h t z := by
            simpa only [s, e] using hgeometry.2
          calc
            s + e ≤ s + e + seg.records.length := by omega
            _ ≤ _ := hbase
  | retainedDecoded v hv done hdone _hchoice _hpayload out hrecording _hrun
      started decoded bank hstart hreceive _hfinish hqueue =>
      have hvD : v < D.length := by rw [hDlen]; exact hv
      have hvLe : v ≤ D.length := Nat.le_of_lt hvD
      obtain ⟨done0, hdone0, hsourceChoice, hbefore, _hafter, _hpreCurrent,
        _hpreCutoff, _hinputLedger, hfinalCurrent, hfinalCutoff, _houtput,
        hactual⟩ := hsites v hv
      have hdoneEq : done = done0 := Option.some.inj (hdone.symm.trans hdone0)
      subst done0
      obtain ⟨out0, started0, decoded0, bank0, hrecording0, _hrun0, hstart0,
        hreceive0, _hfinish0, hdecodedCurrent, hdecodedCutoff⟩ := hactual
      have houtEq : out = out0 := Option.some.inj (hrecording.symm.trans hrecording0)
      subst out0
      have hstartedEq : started = started0 :=
        CoordinatorCollectionLedger.Checked.success.inj (hstart.symm.trans hstart0)
      subst started0
      have hresultEq : (if done.accepted then
          CoordinatorCollectionLedger.Checked.success (decoded, bank) else
          CoordinatorCollectionLedger.Checked.rejected (decoded, bank)) =
        (if done.accepted then
          CoordinatorCollectionLedger.Checked.success (decoded0, bank0) else
          CoordinatorCollectionLedger.Checked.rejected (decoded0, bank0)) :=
        hreceive.symm.trans hreceive0
      have hdecodedEq : decoded = decoded0 := by
        cases ha : done.accepted with
        | false =>
            have hpairs : (decoded, bank) = (decoded0, bank0) := by
              have heq : CoordinatorCollectionLedger.Checked.rejected (decoded, bank) =
                  CoordinatorCollectionLedger.Checked.rejected (decoded0, bank0) := by
                simpa [ha] using hresultEq
              exact CoordinatorCollectionLedger.Checked.rejected.inj heq
            exact congrArg Prod.fst hpairs
        | true =>
            have hpairs : (decoded, bank) = (decoded0, bank0) := by
              have heq : CoordinatorCollectionLedger.Checked.success (decoded, bank) =
                  CoordinatorCollectionLedger.Checked.success (decoded0, bank0) := by
                simpa [ha] using hresultEq
              exact CoordinatorCollectionLedger.Checked.success.inj heq
            exact congrArg Prod.fst hpairs
      subst decoded0
      have hvNext : v + 1 ≤ D.length := by omega
      cases field with
      | current =>
          let P := A ++ D.take (v + 1)
          have hqr := knownCurrentQueue_eq (rate := rate) a q
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q P P.length a).2 hqueue
            (by intro current hreg; dsimp only [P]; exact hdecodedCurrent a current hreg)
          have hth := hthresholdFor P hqr
          have hpos : 0 < P.length := by
            dsimp only [P]
            rw [hprefixLength (v + 1) hvNext]
            omega
          have hinputs : prefixInputs rate rewards C_star C_h (s + e + (v + 1)) z =
              some P := by
            dsimp only [P]
            exact hsourceDate (v + 1) hvNext
          refine ⟨s + e + (v + 1), P, hinputs, hpos, hth, ?_, ?_⟩
          · exact hgeometry.1.trans (by omega)
          · have hle : v + 1 ≤ seg.records.length := by rw [← hDlen]; exact hvNext
            have hbase : (s + e) + seg.records.length ≤
                ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint
                  rate rewards C_star C_h t z := by
              simpa only [s, e] using hgeometry.2
            exact (Nat.add_le_add_left hle (s + e)).trans hbase
      | cutoff =>
          have hqr := knownCutoffQueue_eq (rate := rate) a q
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2 hqueue
            (by intro cutoff hreg; simpa only [hAlen] using hdecodedCutoff a cutoff hreg)
          have hth := hthresholdFor A hqr
          have hpos : 0 < A.length := by rw [hAlen]; exact hepos
          refine ⟨s + e, A, hsourceBase, hpos, hth, hgeometry.1, ?_⟩
          have hbase := hgeometry.2
          dsimp only [s, e] at hbase ⊢
          omega
  | retainedOutput v hv done hdone _hpayload _proposal _houtput hqueue =>
      have hvD : v < D.length := by rw [hDlen]; exact hv
      have hvLe : v ≤ D.length := Nat.le_of_lt hvD
      obtain ⟨done0, hdone0, _hchoice, hbefore, _hafter, _hpreCurrent,
        _hpreCutoff, _hinputLedger, hfinalCurrent, hfinalCutoff, _hsourceOutput,
        _hactual⟩ := hsites v hv
      have hdoneEq : done = done0 := Option.some.inj (hdone.symm.trans hdone0)
      subst done0
      cases field with
      | current =>
          let P := A ++ D.take (v + 1)
          have hvNext : v + 1 ≤ D.length := by omega
          have hqr := knownCurrentQueue_eq (rate := rate) a q
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q P P.length a).2 hqueue
            (by intro current hreg; dsimp only [P]; exact hfinalCurrent a current hreg)
          have hth := hthresholdFor P hqr
          have hpos : 0 < P.length := by
            dsimp only [P]
            rw [hprefixLength (v + 1) hvNext]
            omega
          have hinputs : prefixInputs rate rewards C_star C_h (s + e + (v + 1)) z =
              some P := by
            dsimp only [P]
            exact hsourceDate (v + 1) hvNext
          refine ⟨s + e + (v + 1), P, hinputs, hpos, hth, ?_, ?_⟩
          · exact hgeometry.1.trans (by omega)
          · have hle : v + 1 ≤ seg.records.length := by rw [← hDlen]; exact hvNext
            have hbase : (s + e) + seg.records.length ≤
                ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint
                  rate rewards C_star C_h t z := by
              simpa only [s, e] using hgeometry.2
            exact (Nat.add_le_add_left hle (s + e)).trans hbase
      | cutoff =>
          have hqr := knownCutoffQueue_eq (rate := rate) a q
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2 hqueue
            (by intro cutoff hreg; simpa only [hAlen] using hfinalCutoff a cutoff hreg)
          have hth := hthresholdFor A hqr
          have hpos : 0 < A.length := by rw [hAlen]; exact hepos
          refine ⟨s + e, A, hsourceBase, hpos, hth, hgeometry.1, ?_⟩
          have hbase := hgeometry.2
          dsimp only [s, e] at hbase ⊢
          omega
  | reachedStageOneCandidate v hv call hchoice _hpayload out hdiagnostic _hrun
      candidate hcandidate hqueue =>
      have hvD : v < D.length := by rw [hDlen]; exact hv
      have hvLe : v ≤ D.length := Nat.le_of_lt hvD
      have hvNext : v + 1 ≤ D.length := by omega
      obtain ⟨_d, sourceCall, _hreadCell, hsourceChoice, _hpayload, _hpre,
        _hreadS, _hread0, _hcallRead, hcandidateReplay⟩ := hcallSites v hv
      have hcallEq : call = sourceCall := Option.some.inj (hchoice.symm.trans hsourceChoice)
      subst sourceCall
      obtain ⟨hcur, hcut⟩ := hcandidateReplay out candidate hdiagnostic hcandidate
      cases field with
      | current =>
          let P := A ++ D.take (v + 1)
          have hqr := knownCurrentQueue_eq (rate := rate) a q
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q P P.length a).2 hqueue
            (by intro current hreg; dsimp only [P]; exact hcur a current hreg)
          have hth := hthresholdFor P hqr
          have hpos : 0 < P.length := by
            dsimp only [P]
            rw [hprefixLength (v + 1) hvNext]
            omega
          have hinputs : prefixInputs rate rewards C_star C_h (s + e + (v + 1)) z =
              some P := by
            dsimp only [P]
            exact hsourceDate (v + 1) hvNext
          refine ⟨s + e + (v + 1), P, hinputs, hpos, hth, ?_, ?_⟩
          · exact hgeometry.1.trans (by omega)
          · have hle : v + 1 ≤ seg.records.length := by rw [← hDlen]; exact hvNext
            have hbase : (s + e) + seg.records.length ≤
                ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint
                  rate rewards C_star C_h t z := by
              simpa only [s, e] using hgeometry.2
            exact (Nat.add_le_add_left hle (s + e)).trans hbase
      | cutoff =>
          have hqr := knownCutoffQueue_eq (rate := rate) a q
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2 hqueue
            (by intro cutoff hreg; simpa only [hAlen] using hcut a cutoff hreg)
          have hth := hthresholdFor A hqr
          have hpos : 0 < A.length := by rw [hAlen]; exact hepos
          refine ⟨s + e, A, hsourceBase, hpos, hth, hgeometry.1, ?_⟩
          have hbase := hgeometry.2
          dsimp only [s, e] at hbase ⊢
          omega
  | firstExcludedInput record hhead _proposal _hinput hqueue =>
      obtain ⟨_hindex, _saved, _hstate, hcurrent, hcutoff, _hchoices⟩ :=
        hboundary record hhead
      cases field with
      | current =>
          have hqr := knownCurrentQueue_eq (rate := rate) a q
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q (A ++ D)
              (A ++ D).length a).2 hqueue
            (by intro current hreg; simpa only [List.length_append, hAlen, hDlen] using
              hcurrent a current hreg)
          have hth := hthresholdFor (A ++ D) hqr
          have hpos : 0 < (A ++ D).length := by simp only [List.length_append, hAlen, hDlen]; omega
          refine ⟨s + e + D.length, A ++ D, hsourceFull, hpos, hth, ?_, ?_⟩
          · exact hgeometry.1.trans (by omega)
          · have hle : D.length ≤ seg.records.length := by rw [hDlen]
            have hbase : (s + e) + seg.records.length ≤
                ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint
                  rate rewards C_star C_h t z := by
              simpa only [s, e] using hgeometry.2
            exact (Nat.add_le_add_left hle (s + e)).trans hbase
      | cutoff =>
          have hqr := knownCutoffQueue_eq (rate := rate) a q
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2 hqueue
            (by intro cutoff hreg; simpa only [hAlen] using hcutoff a cutoff hreg)
          have hth := hthresholdFor A hqr
          have hpos : 0 < A.length := by rw [hAlen]; exact hepos
          refine ⟨s + e, A, hsourceBase, hpos, hth, hgeometry.1, ?_⟩
          have hbase := hgeometry.2
          dsimp only [s, e] at hbase ⊢
          omega
  | firstExcludedChoice record hhead call _hchoice hcall hqueue =>
      obtain ⟨_hindex, _saved, _hstate, hcurrent, hcutoff, hchoices⟩ :=
        hboundary record hhead
      have hledger : call.preLedger = seg.final := hcall.2.1
      rw [hledger] at hqueue
      cases field with
      | current =>
          have hqr := knownCurrentQueue_eq (rate := rate) a q
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q (A ++ D)
              (A ++ D).length a).2 hqueue
            (by intro current hreg; simpa only [List.length_append, hAlen, hDlen] using
              hcurrent a current hreg)
          have hth := hthresholdFor (A ++ D) hqr
          have hpos : 0 < (A ++ D).length := by simp only [List.length_append, hAlen, hDlen]; omega
          refine ⟨s + e + D.length, A ++ D, hsourceFull, hpos, hth, ?_, ?_⟩
          · exact hgeometry.1.trans (by omega)
          · have hle : D.length ≤ seg.records.length := by rw [hDlen]
            have hbase : (s + e) + seg.records.length ≤
                ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionEndpoint
                  rate rewards C_star C_h t z := by
              simpa only [s, e] using hgeometry.2
            exact (Nat.add_le_add_left hle (s + e)).trans hbase
      | cutoff =>
          have hqr := knownCutoffQueue_eq (rate := rate) a q
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2 hqueue
            (by intro cutoff hreg; simpa only [hAlen] using hcutoff a cutoff hreg)
          have hth := hthresholdFor A hqr
          have hpos : 0 < A.length := by rw [hAlen]; exact hepos
          refine ⟨s + e, A, hsourceBase, hpos, hth, hgeometry.1, ?_⟩
          have hbase := hgeometry.2
          dsimp only [s, e] at hbase ⊢
          omega

/-- Every threshold at a witnessed retained or first-excluded physical
register site is covered by the original all-arm event. -/
theorem firstCollectionKnownQueueOverflowEvent_subset_allArmCollectionOverflowEvent
    (u t : Fin p.T) :
    firstCollectionKnownQueueOverflowEvent rate rewards C_star C_h u t ⊆
      ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent
        rate rewards C_star C_h := by
  intro z hz
  rcases hz with ⟨hz, seg, hseg, a, field, q, hsite, hthreshold⟩
  obtain ⟨n, P, hinputs, hpositive, hcross, hdateLo, hdateHi⟩ :=
    knownSite_has_original_prefix rate rewards C_star C_h u t z hz seg hseg
      a field q hsite hthreshold
  obtain ⟨detector, hmember⟩ := prefixCrossing_to_original_event rate rewards C_star C_h
    u t z hz n P hinputs hpositive ⟨a, hcross⟩ hdateLo hdateHi
  change z ∈ ⋃ a : Fin p.K, ⋃ u : Fin p.T, ⋃ t : Fin p.T,
    ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.collectionOverflowEvent
      rate rewards C_star C_h u t a
  exact Set.mem_iUnion.mpr ⟨detector,
    Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨t, hmember⟩⟩⟩

/-- The union over original cell indices and rounds inherits one common
finite-union all-arm probability bound, without re-summing cell estimates. -/
theorem firstCollectionKnownQueueOverflowEvent_union_measure_le
    (control0 : TimeControl p) :
    (sourceInputLaw p).real
        (⋃ u : Fin p.T, ⋃ t : Fin p.T,
          firstCollectionKnownQueueOverflowEvent rate rewards C_star C_h u t) ≤
      2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-CanonicalRecordingRates.beta p rate.eta.val /
          (32 * rate.eta.val)) := by
  have hsubset :
      (⋃ u : Fin p.T, ⋃ t : Fin p.T,
        firstCollectionKnownQueueOverflowEvent rate rewards C_star C_h u t) ⊆
      ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent
        rate rewards C_star C_h := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨u, t, hzt⟩ := hz
    exact firstCollectionKnownQueueOverflowEvent_subset_allArmCollectionOverflowEvent
      rate rewards C_star C_h u t hzt
  calc
    _ ≤ (sourceInputLaw p).real
        (ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent
          rate rewards C_star C_h) :=
      measureReal_mono (μ := sourceInputLaw p) hsubset (by finiteness)
    _ ≤ 2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-CanonicalRecordingRates.beta p rate.eta.val /
          (32 * rate.eta.val)) :=
      ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow.allArmCollectionOverflowEvent_measure_le
        rate rewards C_star C_h control0

end Bandits.Support.ReferenceFirstCorrectedCollectionKnownQueueOverflowCover

end noncomputable section
