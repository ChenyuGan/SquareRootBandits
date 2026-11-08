/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionStoppedCompositeQuota
public import Bandits.Support.ReferenceFirstCollectionAwaitedWaitingCost

/-!
# Original-source common-stop observations for the first replacement

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-55,180-240`,
`sources/zip4/manuscript/06_interruptions.tex:246-349,425-431,459-487`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

The scan below is strictly before its calendar boundary. Its physical records
are never truncated by the analytical flag, and the detecting update remains
in the inclusive common prefix. All observations retain the original source,
whole rewards and original private row index.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionCommonStopObservation

variable {p : Parameters}

/-- The exact original-source awaited-UP ambiguity at a fixed detecting date. -/
def U (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Prop :=
  ReferenceFirstReplacementCollectionLocalStopSourceTransport.originalUpAwaitedAmbiguityAtDate
    (rate := rate) rewards C_star C_h control0 z i t

/-- The common stop at the actual optional record of this original source. -/
def D (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (s : ℕ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Prop :=
  ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
    ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopAt
      s z rewards C_star C_h control0 i r

/-- An analytical flag, scanning original physical dates strictly before `n`.
The onset `u` is one-based; the scanned record dates are zero-based. -/
def L (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (s u : ℕ) (i : Fin (p.m - 1)) (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Bool :=
  decide (∃ t : Fin p.T, u ≤ t.val + 1 ∧ t.val < n ∧
    D rate rewards C_star C_h control0 s i t z)

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

/-- A detected flag remains set when the calendar scan is extended. -/
theorem L_mono (s u : ℕ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n n' : ℕ) (hn : n ≤ n') :
    L rate rewards C_star C_h control0 s u i n z = true →
      L rate rewards C_star C_h control0 s u i n' z = true := by
  simp only [L, decide_eq_true_eq]
  rintro ⟨t, hu, ht, hd⟩
  exact ⟨t, hu, ht.trans_le hn, hd⟩

/-- No new witnesses appear after the finite horizon; physical play has not
been changed into a stopped execution. -/
theorem L_after_horizon (s u : ℕ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ) (hn : p.T ≤ n) :
    L rate rewards C_star C_h control0 s u i n z =
      L rate rewards C_star C_h control0 s u i p.T z := by
  have hlt : ∀ t : Fin p.T, t.val < n := fun t => t.isLt.trans_le hn
  simp only [L, hlt, Fin.is_lt, true_and]

private theorem originalRun_records
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
      (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
        (rate := rate) rewards C_star C_h q t s hs control0 i z)).records =
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h := by
  have hl := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput_launch
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = s :=
    z.property.2.2
  rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate z.val rewards C_star C_h _ hl]
  simp only [hstart]
  rfl

private theorem input_ext
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (hrows : x.rows = y.rows)
    (hselected : x.selected = y.selected) (htime : x.time = y.time)
    (hrewards : x.rewards = y.rewards) : x = y := by
  cases x
  cases y
  simp_all

private theorem originalCurrent_lookup
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z.val =
      some (ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
        (rate := rate) rewards C_star C_h q t s hs control0 i z) := by
  rcases z with ⟨source, hz⟩
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s :=
    hz.2.2
  subst s
  have hl := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput_launch
    (rate := rate) rewards C_star C_h q t _ hs control0 i ⟨source, hz⟩
  rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h t source _ hl hs]
  apply congrArg (fun input : ReferenceActivePhysicalStep.RoundInput p rate =>
    some (⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ :
      ReferenceCompletePhysicalHistory.RoundRecord p rate))
  apply input_ext
  · rfl
  · rfl
  · rfl
  · apply Fin.ext
    exact Nat.add_sub_of_le hs
  · rfl

private theorem actualRecord_input_fields (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · change ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r at hr
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

private theorem record_time_of_lookup
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    r.input.time = t ∧ r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h := by
  refine ⟨(actualRecord_input_fields rate rewards C_star C_h t z r hr).2.2.1, ?_⟩
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split at hr
  · exact List.mem_of_getElem? hr
  · cases hr

private theorem lookup_at_mem
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h r.input.time z =
      some r := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨hkl, _⟩ := List.getElem?_eq_some_iff.mp hk
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have h := congrArg (fun xs : List ℕ => xs[k]?) htimes
  rw [List.getElem?_map, hk] at h
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hindex : k < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by omega
  simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range', hindex,
    Nat.one_mul, Option.map_some, Option.some.injEq] at h
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
      r.input.time.val := by omega
  have hsub : r.input.time.val - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h = k := by omega
  rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hstart, hsub]
  exact hk

/-- Whole round-end observation codes factor through the original selected prefix.
No equality of raw records carrying different whole row tables is asserted. -/
theorem actualRecordCode_factor
    (n : ℕ)
    (v : Fin p.T) (hvn : v.val < n) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h v z).map
        (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) =
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h v (ReferenceSourcePrefixHistoryFiltration.sourcePrefix
        control0 n z)).map
        (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) := by
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h v z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h v
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
    calc
      _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h v
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 v.val z) :=
            ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h
              control0 v z
      _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h v
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 v.val
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)) := by
              rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
                control0 v.val n (by omega)]
      _ = _ := (ReferenceSourcePrefixHistoryFiltration.incoming_factor
          rate rewards C_star C_h control0 v
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)).symm
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h v z with
  | none =>
      cases hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h v
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) with
      | none => rfl
      | some r' =>
          have : False := by
            simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr, hr'] at hin
          exact this.elim
  | some r =>
      cases hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h v
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) with
      | none =>
          have : False := by
            simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr, hr'] at hin
          exact this.elim
      | some r' =>
          have henc : ReferenceActivePhysicalStepMeasurability.encodeState r.input.state =
              ReferenceActivePhysicalStepMeasurability.encodeState r'.input.state := by
            simpa [ReferenceSourcePrefixHistoryFiltration.incoming, hr, hr'] using hin
          have hstate : r.input.state = r'.input.state := by
            have h := congrArg ReferenceActivePhysicalStepMeasurability.decodeState henc
            simpa only [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState] using h
          obtain ⟨hrows, hselected, htime, hrewards⟩ :=
            actualRecord_input_fields rate rewards C_star C_h v z r hr
          obtain ⟨hrows', hselected', htime', hrewards'⟩ :=
            actualRecord_input_fields rate rewards C_star C_h v
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) r' hr'
          have hselectedEq : r.input.selected = r'.input.selected := by
            rw [hselected, hselected',
              ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected]
          have hcurrent : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time := by
            simp [ReferenceActivePhysicalStep.RoundInput.row, hrows, hrows', hselected,
              hselected', htime, htime', ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
              ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, hvn]
          have hpast : ∀ u : Fin p.T, u.val < r.input.time.val →
              (r.input.row.2 u).1 ContinuousControlSlice.Label.prop =
                (r'.input.row.2 u).1 ContinuousControlSlice.Label.prop := by
            intro u hu
            have hu' : u.val < n := by rw [htime] at hu; omega
            simp [ReferenceActivePhysicalStep.RoundInput.row, hrows, hrows', hselected,
              hselected', ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
              ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, hu']
          have hcode := ReferenceInspectedPastRoundObservations.roundRecordCode_eq_of_temporal_reads
            (rate := rate) r.input r'.input hstate hselectedEq (htime.trans htime'.symm)
            (hrewards.trans hrewards'.symm) hcurrent hpast
          have hrecordCode :
              ReferenceActiveHorizonMeasurability.roundRecordCode r =
                ReferenceActiveHorizonMeasurability.roundRecordCode r' := by
            rcases r with ⟨inputL, outputL, houtL⟩
            rcases r' with ⟨inputR, outputR, houtR⟩
            have houtputL : outputL = ReferenceActivePhysicalStep.step inputL := houtL
            have houtputR : outputR = ReferenceActivePhysicalStep.step inputR := houtR
            subst outputL
            subst outputR
            simpa using hcode
          simp [hrecordCode]

private abbrev UpCode := ReferenceCollectionServiceTailMeasurability.UpDiagnosticCode p rate

private def upHistory (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Fin p.T → Option (UpCode (p := p) (rate := rate)) :=
  fun v => (ReferenceInspectedPastRoundObservations.pastRoundObservations
    rate rewards C_star C_h p.T le_rfl z v).bind
      (ReferenceGeneratedUpBatchPrefixEvent.roundRecordUpDiagnosticCode (p := p) (rate := rate))

private theorem upHistory_reconstructs (z : BootstrapPrivateRoundStreams.SourceInput p)
    (v : Fin p.T) (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h v z = some r) :
    (upHistory rate rewards C_star C_h z v).map
      ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic = r.output.coordinator.up := by
  have hobs := ReferenceInspectedPastRoundObservations.pastRoundObservations_some
    rate rewards C_star C_h p.T le_rfl z v r hr
  simp only [upHistory, hobs, Option.bind_some]
  exact ReferenceGeneratedUpBatchPrefixEvent.roundRecordUpDiagnosticCode_reconstructs r

private theorem record_of_upHistory_some (z : BootstrapPrivateRoundStreams.SourceInput p)
    (v : Fin p.T) (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (upHistory rate rewards C_star C_h z v).map
      ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic = some d) :
    ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h v z = some r ∧
      r.output.coordinator.up = some d := by
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h v z with
  | none =>
    simp [upHistory, ReferenceInspectedPastRoundObservations.pastRoundObservations, hr] at hd
  | some r =>
    exact ⟨r, rfl, (upHistory_reconstructs rate rewards C_star C_h z v r hr).symm.trans hd⟩

private def awaitedDiagnostic (i : Fin (p.m - 1))
    (message : OrdinaryMessageCodec.UpRecord (CoordinatorCollectionLedger.codecParams p rate.eta))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate) : Prop :=
  d.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta message) ∧
    d.input.selectedFollower = i ∧
    (CoordinatorUpReception.roundInput d.input).selected = true ∧
    (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
    CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i message = true

private def awaitedCodeTrace (s beta : ℕ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (message : OrdinaryMessageCodec.UpRecord (CoordinatorCollectionLedger.codecParams p rate.eta))
    (history : Fin p.T → Option (UpCode (p := p) (rate := rate)))
    (channels : Fin p.T → Option (ContinuousLearningRows.Channel p)) : Prop :=
  s ≤ beta ∧ beta ≤ t.val ∧
    ∀ v : Fin p.T, beta ≤ v.val → v.val ≤ t.val → channels v = some (1, i) →
      ∃ d, (history v).map ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic = some d ∧
        awaitedDiagnostic (rate := rate) i message d

private def channels (z : BootstrapPrivateRoundStreams.SourceInput p)
    (v : Fin p.T) : Option (ContinuousLearningRows.Channel p) :=
  ReferenceSelectedAffinePairLaw.selectedChannel p
    ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1

private theorem originalAwaitedTrace_iff_code
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (beta : ℕ)
    (message : OrdinaryMessageCodec.UpRecord (CoordinatorCollectionLedger.codecParams p rate.eta)) :
    ReferenceGeneratedUpAwaitedBatchCoverage.awaited_up_source_trace
      rewards C_star C_h q t s hs control0 i z beta message ↔
      awaitedCodeTrace (rate := rate) s beta i t message
        (upHistory rate rewards C_star C_h z.val) (channels z.val) := by
  have hR := originalRun_records rate rewards C_star C_h control0 q t s hs i z
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = s :=
    z.property.2.2
  constructor
  · rintro ⟨hsbeta, hbetat, htrace⟩
    refine ⟨hsbeta, hbetat, ?_⟩
    intro v hbeta hv hchannel
    have hl := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput_launch
      (rate := rate) rewards C_star C_h q t s hs control0 i z
    obtain ⟨r, hr⟩ : ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h v z.val = some r := by
      exact ⟨_, ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
        rate rewards C_star C_h v z.val _ hl (by rw [hstart]; omega)⟩
    obtain ⟨htime, hmem⟩ := record_time_of_lookup rate rewards C_star C_h v z.val r hr
    obtain ⟨hrows, hselected, _, _⟩ := actualRecord_input_fields rate rewards C_star C_h v z.val r hr
    have hchan : ReferenceSelectedAffinePairLaw.selectedChannel p
        (r.input.row.2 r.input.time).1 = some (1, i) := by
      simpa only [channels, ReferenceActivePhysicalStep.RoundInput.row,
        hrows, hselected, htime] using hchannel
    have hmem' := hmem
    rw [← hR] at hmem'
    obtain ⟨hsent, d, hd, hi, hsel, hen, hacc⟩ := htrace r hmem'
      (by rw [htime]; exact hbeta) (by rw [htime]; exact hv) hchan
    refine ⟨d, (upHistory_reconstructs rate rewards C_star C_h z.val v r hr).trans hd,
      ?_, hi, hsel, hen, hacc⟩
    exact (ReferenceGeneratedUpBatchPrefixEvent.actualRecordUpDiagnostic_expected r d hd).trans hsent
  · rintro ⟨hsbeta, hbetat, htrace⟩
    refine ⟨hsbeta, hbetat, ?_⟩
    intro r hr hbeta hv hchan
    have hmem : r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z.val rewards C_star C_h := by rw [← hR]; exact hr
    have hlookup := lookup_at_mem rate rewards C_star C_h z.val r hmem
    obtain ⟨hrows, hselected, _, _⟩ := actualRecord_input_fields
      rate rewards C_star C_h r.input.time z.val r hlookup
    have hchannel : channels z.val r.input.time = some (1, i) := by
      simpa only [channels, ReferenceActivePhysicalStep.RoundInput.row, hrows, hselected] using hchan
    obtain ⟨d, hd, hsent, hi, hsel, hen, hacc⟩ := htrace r.input.time hbeta hv hchannel
    have hdr : r.output.coordinator.up = some d :=
      (upHistory_reconstructs rate rewards C_star C_h z.val r.input.time r hlookup).symm.trans hd
    refine ⟨?_, d, hdr, hi, hsel, hen, hacc⟩
    exact (ReferenceGeneratedUpBatchPrefixEvent.actualRecordUpDiagnostic_expected r d hdr).symm.trans hsent

private def ambiguityCodeAt (s : ℕ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (history : Fin p.T → Option (UpCode (p := p) (rate := rate)))
    (channel : Fin p.T → Option (ContinuousLearningRows.Channel p)) : Prop :=
  ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
    (history t).map ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic = some d ∧
    d.input.selectedFollower = i ∧
    ReferenceActiveAffinePositiveTest.upDiagnosticPositive (some d) = true ∧
    ((d.input.upDecoderBank i).pending).length + 1 = AffineBatchDecoder.quota p ∧
    (∃ (message : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta)) (beta : ℕ),
      awaitedCodeTrace (rate := rate) s beta i t message history channel ∧
      ∀ entry ∈ (d.input.upDecoderBank i).pending ++
        [AffineBatchDecoder.entry p
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time],
        beta ≤ entry.time.val) ∧
    ∃ v₁ v₂ : AffineChannelLaw.Word (AffineBatchDecoder.width p), v₁ ≠ v₂ ∧
      AffineBatchDecoder.satisfies
        (((d.input.upDecoderBank i).pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]).map
              AffineBatchDecoder.Entry.sample) v₁ ∧
      AffineBatchDecoder.satisfies
        (((d.input.upDecoderBank i).pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]).map
              AffineBatchDecoder.Entry.sample) v₂

private theorem U_iff_code (i : Fin (p.m - 1)) (t : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    U rate rewards C_star C_h control0 i t source ↔
      ∃ (q : Fin (M p)) (s : ℕ), s ≤ t.val ∧
        source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
          (rate := rate) rewards C_star C_h q t (1, i) s ∧
        ambiguityCodeAt (rate := rate) s i t (upHistory rate rewards C_star C_h source)
          (channels source) := by
  constructor
  · rintro ⟨q, s, hs, hz, d, hd, hi, hp, hQ, haw, hamb⟩
    let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i := ⟨source, hz⟩
    let current := ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
      (rate := rate) rewards C_star C_h q t s hs control0 i z
    have hlookup := originalCurrent_lookup rate rewards C_star C_h control0 q t s hs i z
    have hdiag := upHistory_reconstructs rate rewards C_star C_h source t current hlookup
    have hfields := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields current d hd
    obtain ⟨_, _, _, hbank, _⟩ := hfields
    have hp' : ReferenceActiveAffinePositiveTest.upDiagnosticPositive (some d) = true := by
      rw [← hd, ← ReferenceActiveAffinePositiveTest.record_upPositive]
      exact hp
    refine ⟨q, s, hs, hz, d, hdiag.trans hd, hi, hp', ?_, ?_, ?_⟩
    · simpa only [hbank] using hQ
    · obtain ⟨message, beta, htrace, htimes⟩ := haw
      refine ⟨message, beta, (originalAwaitedTrace_iff_code rate rewards C_star C_h control0
        q t s hs i z beta message).mp htrace, ?_⟩
      simpa only [hbank] using htimes
    · simpa only [hbank] using hamb
  · rintro ⟨q, s, hs, hz, d, hd, hi, hp, hQ, haw, hamb⟩
    let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i := ⟨source, hz⟩
    let current := ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
      (rate := rate) rewards C_star C_h q t s hs control0 i z
    have hlookup := originalCurrent_lookup rate rewards C_star C_h control0 q t s hs i z
    have hdiag := upHistory_reconstructs rate rewards C_star C_h source t current hlookup
    have hdr : current.output.coordinator.up = some d := hdiag.symm.trans hd
    have hfields := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields current d hdr
    obtain ⟨_, _, _, hbank, _⟩ := hfields
    refine ⟨q, s, hs, hz, d, hdr, hi, ?_, ?_, ?_, ?_⟩
    · rw [ReferenceActiveAffinePositiveTest.record_upPositive, hdr]
      exact hp
    · simpa only [hbank] using hQ
    · obtain ⟨message, beta, htrace, htimes⟩ := haw
      refine ⟨message, beta, (originalAwaitedTrace_iff_code rate rewards C_star C_h control0
        q t s hs i z beta message).mpr htrace, ?_⟩
      simpa only [hbank] using htimes
    · simpa only [hbank] using hamb

private theorem measurable_optionBind {X Y W : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
    (f : Y → Option W) (hf : Measurable f) (g : X → Option Y) (hg : Measurable g) :
    Measurable (fun x => (g x).bind f) := by
  have hbind : Measurable (fun o : Option Y => o.bind f) := by
    apply measurable_comap_iff.mpr
    have hsum : Measurable (Sum.elim
        (fun y => Equiv.optionEquivSumPUnit W (f y))
        (fun _ : PUnit => Equiv.optionEquivSumPUnit W none)) :=
      (measurable_comap_iff.mp hf).sumElim measurable_const
    convert hsum.comp (comap_measurable (Equiv.optionEquivSumPUnit Y)) using 1
    funext o
    cases o <;> rfl
  exact hbind.comp hg

private theorem laterOptionSpace_eq_top {A : Type*} (mA : MeasurableSpace A)
    (hA : mA = ⊤) :
    @LaterAssignmentStartMeasurability.optionMeasurableSpace A mA = ⊤ := by
  subst mA
  let _ : MeasurableSpace A := ⊤
  let e := Equiv.optionEquivSumPUnit A
  have hsum : (inferInstance : MeasurableSpace (A ⊕ PUnit)) = ⊤ := by
    ext s
    rw [measurableSet_sum_iff]
    simp
  have hcomap : (MeasurableSpace.comap e (⊤ : MeasurableSpace (A ⊕ PUnit))) = ⊤ := by
    apply MeasurableSpace.ext
    intro s
    rw [MeasurableSpace.measurableSet_comap]
    constructor
    · intro _
      trivial
    · intro _
      refine ⟨e '' s, trivial, ?_⟩
      ext x
      simp [e.injective]
  unfold LaterAssignmentStartMeasurability.optionMeasurableSpace
  rw [hsum]
  exact hcomap

private theorem measurable_upHistory :
    Measurable (upHistory rate rewards C_star C_h) := by
  apply measurable_pi_iff.mpr
  intro v
  have hobs := ReferenceInspectedPastRoundObservations.measurable_pastRoundObservations
    rate rewards C_star C_h p.T (Nat.le_refl p.T)
  have hobsV := (measurable_pi_iff.mp hobs) v
  have hi : Fin (p.m - 1) := ⟨0, by have := p.two_le_m; omega⟩
  have hdiagTop : @Measurable
      (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate))
      (Option (UpCode (p := p) (rate := rate)))
      ReferenceActiveHorizonMeasurability.roundRecordCodeMeasurableSpace
      (ReferenceCollectionServiceTailMeasurability.upDiagnosticOptionMeasurableSpace p rate)
      (ReferenceGeneratedUpBatchPrefixEvent.roundRecordUpDiagnosticCode
        (p := p) (rate := rate)) := by
    have hprefix :=
      ReferenceGeneratedUpBatchPrefixEvent.measurable_roundRecordPrefixCode
        (p := p) (rate := rate) hi
    change @Measurable _ _ _ _ (fun code =>
      (ReferenceGeneratedUpBatchPrefixEvent.roundRecordPrefixCode hi code).2)
    exact measurable_snd.comp hprefix
  have hUpSpace : (inferInstance : MeasurableSpace (UpCode (p := p) (rate := rate))) = ⊤ := rfl
  have hOptionSpace := laterOptionSpace_eq_top
    (A := UpCode (p := p) (rate := rate))
    (inferInstance : MeasurableSpace (UpCode (p := p) (rate := rate))) hUpSpace
  have hdiag : @Measurable
      (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate))
      (Option (UpCode (p := p) (rate := rate)))
      ReferenceActiveHorizonMeasurability.roundRecordCodeMeasurableSpace
      (@LaterAssignmentStartMeasurability.optionMeasurableSpace
        (UpCode (p := p) (rate := rate))
        (inferInstance : MeasurableSpace (UpCode (p := p) (rate := rate))))
      (ReferenceGeneratedUpBatchPrefixEvent.roundRecordUpDiagnosticCode
        (p := p) (rate := rate)) := by
    exact hdiagTop.mono le_rfl (by rw [hOptionSpace]; exact le_rfl)
  have hbound := measurable_optionBind
    (ReferenceGeneratedUpBatchPrefixEvent.roundRecordUpDiagnosticCode
      (p := p) (rate := rate)) hdiag
    (fun z => ReferenceInspectedPastRoundObservations.pastRoundObservations
      rate rewards C_star C_h p.T (Nat.le_refl p.T) z v) hobsV
  exact hbound.mono le_rfl (by
    rw [ReferenceCollectionServiceTailMeasurability.upDiagnosticOptionMeasurableSpace,
      hOptionSpace])

private theorem measurable_channels (v : Fin p.T) :
    @Measurable (BootstrapPrivateRoundStreams.SourceInput p) (Option (ContinuousLearningRows.Channel p))
      (inferInstance : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p))
      (ReferenceInitializationMeasurability.optionCountableMeasurableSpace
        (ContinuousLearningRows.Channel p))
      (fun z => channels z v) := by
  let : MeasurableSpace (Option (ContinuousLearningRows.Channel p)) :=
    ReferenceInitializationMeasurability.optionCountableMeasurableSpace (ContinuousLearningRows.Channel p)
  have hindex : Measurable (ActualInitializationPhysicalStep.selectedRowIndex p) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have heval : Measurable
      (fun x : CompletePublicTable.CompleteRows p × Fin (M p) => x.1 x.2) := by
    apply measurable_from_prod_countable_left
    exact fun j => measurable_pi_apply j
  have hrow := heval.comp ((measurable_snd.comp measurable_fst).prodMk hindex)
  exact (ReferenceSelectedAffinePairLaw.measurable_selectedChannel p).comp
    (measurable_fst.comp ((measurable_pi_apply v).comp (measurable_snd.comp hrow)))

private theorem measurable_history_channels :
    Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      (upHistory rate rewards C_star C_h z, channels z)) := by
  exact (measurable_upHistory rate rewards C_star C_h).prodMk
    (measurable_pi_iff.mpr fun v => measurable_channels v)

private instance {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A] :
    MeasurableSingletonClass (Fin p.T → A) := by
  refine ⟨fun x => ?_⟩
  have heq : Set.univ.pi (fun v : Fin p.T => {x v}) = {x} := by
    ext y
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_singleton_iff]
    exact ⟨fun hy => funext (fun v => hy v trivial), fun h v _ => congrFun h v⟩
  rw [← heq]
  exact MeasurableSet.univ_pi (fun v => measurableSet_singleton (x v))

/-- Borelness of the EXACT original-source ambiguity, using countable retained
UP diagnostics and the finite selected-channel history. Continuous source
coordinates retain their existing measurable structures. -/
theorem U_borel (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
      U rate rewards C_star C_h control0 i t z} := by
  let CodeData := (Fin p.T → Option (UpCode (p := p) (rate := rate))) ×
    (Fin p.T → Option (ContinuousLearningRows.Channel p))
  have heq : {z : BootstrapPrivateRoundStreams.SourceInput p |
      U rate rewards C_star C_h control0 i t z} =
      ⋃ q : Fin (M p), ⋃ s : ℕ,
        {z | s ≤ t.val ∧ z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
          (rate := rate) rewards C_star C_h q t (1, i) s ∧
          ambiguityCodeAt (rate := rate) s i t
            (upHistory rate rewards C_star C_h z) (channels z)} := by
    ext z
    simpa only [Set.mem_iUnion, Set.mem_ofPred_eq] using
      U_iff_code rate rewards C_star C_h control0 i t z
  rw [heq]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro s
  by_cases hs : s ≤ t.val
  · have hlaunch := ReferenceGeneratedAffineHashHalf.measurableSet_generatedLaunchBranch
      (rate := rate) rewards C_star C_h q t (1, i) s hs control0
    have hevent : MeasurableSet {x : CodeData |
        ambiguityCodeAt (rate := rate) s i t x.1 x.2} := Set.to_countable _ |>.measurableSet
    have hcode := hevent.preimage (measurable_history_channels rate rewards C_star C_h)
    convert hlaunch.inter hcode using 1
    ext z
    simp only [hs, true_and, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  · simp only [hs, false_and, Set.ofPred_false, MeasurableSet.empty]

private theorem upHistory_factor (n : ℕ) (v : Fin p.T) (hv : v.val < n)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    upHistory rate rewards C_star C_h z v = upHistory rate rewards C_star C_h
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) v := by
  have hround := actualRecordCode_factor rate rewards C_star C_h control0 n v hv z
  simp only [upHistory, ReferenceInspectedPastRoundObservations.pastRoundObservations,
    Fin.castLE_refl] at hround ⊢
  simpa only [Option.bind_map] using congrArg
    (fun o => o.bind (ReferenceGeneratedUpBatchPrefixEvent.roundRecordUpDiagnosticCode
      (p := p) (rate := rate))) hround

private theorem channels_factor (n : ℕ) (v : Fin p.T) (hv : v.val < n)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    channels z v = channels
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) v := by
  simp only [channels, ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, ite_eq_left hv]

private theorem ambiguityCodeAt_congr
    (s : ℕ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (history history' : Fin p.T → Option (UpCode (p := p) (rate := rate)))
    (channel channel' : Fin p.T → Option (ContinuousLearningRows.Channel p))
    (hh : ∀ v : Fin p.T, v.val ≤ t.val → history v = history' v)
    (hc : ∀ v : Fin p.T, v.val ≤ t.val → channel v = channel' v) :
    ambiguityCodeAt (rate := rate) s i t history channel ↔
      ambiguityCodeAt (rate := rate) s i t history' channel' := by
  have htrace : ∀ beta message,
      awaitedCodeTrace (rate := rate) s beta i t message history channel ↔
        awaitedCodeTrace (rate := rate) s beta i t message history' channel' := by
    intro beta message
    constructor
    · rintro ⟨hs, ht, h⟩
      refine ⟨hs, ht, ?_⟩
      intro v hb hv hchannel
      obtain ⟨d, hd, haw⟩ := h v hb hv ((hc v hv).trans hchannel)
      exact ⟨d, by simpa only [hh v hv] using hd, haw⟩
    · rintro ⟨hs, ht, h⟩
      refine ⟨hs, ht, ?_⟩
      intro v hb hv hchannel
      obtain ⟨d, hd, haw⟩ := h v hb hv ((hc v hv).symm.trans hchannel)
      exact ⟨d, by simpa only [hh v hv] using hd, haw⟩
  simp only [ambiguityCodeAt, hh t le_rfl, htrace]

private theorem launchBranch_factor (q : Fin (M p)) (s : ℕ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (hs : s ≤ t.val) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h q t (1, i) s ↔
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z ∈
        ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
          (rate := rate) rewards C_star C_h q t (1, i) s := by
  have hlaunch := ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_factor
    rate rewards C_star C_h control0 (t.val + 1) (by omega) s (by omega) z
  have hselector : ReferenceSelectedAffinePairLaw.selector p t z =
      ReferenceSelectedAffinePairLaw.selector p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) := by
    simp only [ReferenceSelectedAffinePairLaw.selector,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control,
      ite_eq_left (Nat.lt_succ_self t.val)]
  change (_ ∧ z ∈ ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h s) ↔
    (_ ∧ ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z ∈
      ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s)
  rw [hselector, hlaunch]

/-- The literal original UP event uses the current update and no later date. -/
theorem U_factor (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    U rate rewards C_star C_h control0 i t z ↔
      U rate rewards C_star C_h control0 i t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) := by
  rw [U_iff_code, U_iff_code]
  apply exists_congr
  intro q
  apply exists_congr
  intro s
  by_cases hs : s ≤ t.val
  · simp only [hs, true_and]
    have hlaunch := launchBranch_factor rate rewards C_star C_h control0 q s i t hs z
    have hcode := ambiguityCodeAt_congr (rate := rate) s i t
      (upHistory rate rewards C_star C_h z)
      (upHistory rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z))
      (channels z) (channels (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z))
      (fun v hv => upHistory_factor rate rewards C_star C_h control0 _ v (by omega) z)
      (fun v hv => channels_factor control0 _ v (by omega) z)
    exact and_congr hlaunch hcode
  · simp only [hs, false_and]

/-- Round-end Borelness in the existing original-source prefix filtration. -/
theorem U_measurableSet (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 2)]
      {z : BootstrapPrivateRoundStreams.SourceInput p | U rate rewards C_star C_h control0 i t z} := by
  rw [show t.val + 2 = (t.val + 1) + 1 by omega,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  refine ⟨{z | U rate rewards C_star C_h control0 i t z},
    U_borel rate rewards C_star C_h control0 i t, ?_⟩
  ext z
  exact (U_factor rate rewards C_star C_h control0 i t z).symm

private theorem siteLedger_eq_reception (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := x) =
      (ReferenceCollectionPhaseHistory.executedTail x).bind
        (fun tail => tail.reception.map Prod.fst) := by
  have htail : ∀ (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate) started weights,
      ReferenceCoordinatorUpPhysicalCall.tailLedger? (ReferenceActivePhysicalStep.prepare x)
        payload ledger started weights =
        (⟨payload, ledger, started, weights⟩ : ReferenceCollectionPhaseHistory.Tail x).reception.map
          Prod.fst := by
    intro payload ledger started weights
    unfold ReferenceCoordinatorUpPhysicalCall.tailLedger? ReferenceCollectionPhaseHistory.Tail.reception
    dsimp only
    cases hr : CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare x)
          payload started weights) with
    | none => rfl
    | some recording =>
      dsimp only
      cases CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) <;> rfl
  unfold ReferenceCoordinatorUpPhysicalCall.siteLedger? ReferenceCollectionPhaseHistory.executedTail
  dsimp only
  split
  · rfl
  · cases h : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | first outcome => cases outcome <;> rfl
    | live registers owned base outcome =>
      cases outcome <;> dsimp only <;> first | rfl | exact htail _ _ _ _
    | collection payload ledger clock cutoff outcome =>
      cases outcome <;> dsimp only <;> first | rfl | exact htail _ _ _ _
    | dagger => rfl
    | invalidCollectionCutoff => rfl

private theorem acceptedLabel_eq_site (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ReferenceCollectionPhaseHistory.acceptedLabel x =
      (ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := x)).bind
        (fun ledger => match (ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare x) ledger).result with
          | .success _ => some (ReferenceActivePhysicalStep.upSenderIndex x)
          | _ => none) := by
  rw [siteLedger_eq_reception]
  unfold ReferenceCollectionPhaseHistory.acceptedLabel
  cases ht : ReferenceCollectionPhaseHistory.executedTail x with
  | none => rfl
  | some tail =>
    simp only [Option.bind_some]
    unfold ReferenceCollectionPhaseHistory.Tail.reception
    cases hr : CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare x)
          tail.payload tail.started tail.weights) with
    | none => rfl
    | some recording =>
      dsimp only
      cases CoordinatorCollectionLedger.startRound tail.ledger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled tail.ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) <;> rfl

private def diagnosticDecode (d : ReferenceActivePhysicalStep.UpDiagnostic p rate) :=
  CoordinatorCollectionLedger.decodeUp d.input.ledger d.input.selectedFollower
    (CoordinatorUpReception.parseDecoderOutput
      (ReferenceUpReception.filterRawByExpected d.raw d.expected))

private theorem receive_result_formula (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) :
    (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare x) ledger).result =
      if CoordinatorUpReception.receptionInputCheck
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledger) = true then
        CoordinatorUpReception.packDecodeResult
          (CoordinatorCollectionLedger.decodeUp ledger (ReferenceActivePhysicalStep.upSenderIndex x)
            (CoordinatorUpReception.parseDecoderOutput (ReferenceUpReception.filterRawByExpected
              (CoordinatorUpReception.decoderTransition
                (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledger)).2
              (ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x)))))
          (CoordinatorUpReception.decoderBankAfter
            (ReferenceCoordinatorUpPhysicalCall.actualUpInput x ledger))
      else .invalid := by
  rfl

private theorem acceptedLabel_at_diagnostic
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d) :
    ReferenceCollectionPhaseHistory.acceptedLabel r.input =
      match diagnosticDecode (rate := rate) d with
      | .success _ => some d.input.selectedFollower
      | _ => none := by
  obtain ⟨ledger, hsite, hcheck, hinput, _hafter, hraw, _hparsed, _hlocal, _hmatch,
      hexpected, _⟩ := ReferenceGeneratedUpBatchCalendar.record_up_executed_fields r d hd
  have hsender : d.input.selectedFollower = ReferenceActivePhysicalStep.upSenderIndex r.input := by
    rw [hinput]
    rfl
  have hledger : d.input.ledger = ledger := by rw [hinput]; rfl
  have hexpected' : d.expected = ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare r.input) := hexpected
  rw [acceptedLabel_eq_site, hsite, Option.bind_some, receive_result_formula,
    ite_eq_left hcheck]
  unfold diagnosticDecode
  rw [hledger, hsender, hraw, hexpected', hinput]
  cases CoordinatorCollectionLedger.decodeUp ledger (ReferenceActivePhysicalStep.upSenderIndex r.input)
    (CoordinatorUpReception.parseDecoderOutput (ReferenceUpReception.filterRawByExpected
      (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger)).2
      (ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input)))) <;> rfl

private theorem no_diagnostic_no_acceptance
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hn : r.output.coordinator.up = none) :
    ReferenceCollectionPhaseHistory.acceptedLabel r.input = none := by
  rw [acceptedLabel_eq_site]
  cases hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) with
  | none => rfl
  | some ledger =>
    have hcheck : CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input ledger) ≠ true := by
      intro hc
      obtain ⟨d, hd⟩ := (ReferenceCoordinatorUpPhysicalCall.record_up_retention_iff r).mpr
        ⟨ledger, hsite, hc⟩
      rw [hn] at hd
      cases hd
    simp only [Option.bind_some, receive_result_formula, ite_eq_right hcheck]

private theorem acceptanceAt_iff_diagnostic
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) (i : Fin (p.m - 1)) :
    ReferenceFirstReplacementCollectionStoppedPureUpQuota.acceptanceAt r i ↔
      ∃ d, r.output.coordinator.up = some d ∧
        (match diagnosticDecode (rate := rate) d with
        | .success _ => some d.input.selectedFollower
        | _ => none) = some i := by
  rw [ReferenceFirstReplacementCollectionStoppedPureUpQuota.acceptanceAt_iff]
  cases hd : r.output.coordinator.up with
  | none =>
    simp only [no_diagnostic_no_acceptance rate r hd, reduceCtorEq, false_and, exists_false]
  | some d =>
    rw [acceptedLabel_at_diagnostic rate r d hd]
    simp only [Option.some.injEq]
    exact ⟨fun h => ⟨d, rfl, h⟩, fun ⟨_, h, ha⟩ => h ▸ ha⟩

/-- Fixed-date DOWN ambiguity on the actual source calendar is Borel, with
all incoming pending entries and the current detecting equation retained. -/
theorem actualDownAmbiguity_borel (s : ℕ) (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
      ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r i} := by
  let event := fun b : Fin (p.T + 1) => {z : BootstrapPrivateRoundStreams.SourceInput p |
    ∃ hz : z ∈ ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h b,
      ∃ data, (ReferenceFirstLiveDownCompletionReadout.sourceDownReadouts
        rate rewards C_star C_h b (p.T - b) (by omega) i ⟨z, hz⟩)[t.val - b]? = some data ∧
        ∃ B, data.1 = some B ∧ (∀ e ∈ B, s ≤ e.time.val) ∧
          ReferenceFirstLiveDownCompletionReadout.multipleSolutions B}
  have hmeas : ∀ b, MeasurableSet (event b) := by
    intro b
    have hm := ReferenceFirstLiveDownCompletionReadout.measurableSet_sourceDownReadouts_test
      rate rewards C_star C_h b (p.T - b) (by omega) i
      (fun xs => ∃ data, xs[t.val - b]? = some data ∧
        ∃ B, data.1 = some B ∧ (∀ e ∈ B, s ≤ e.time.val) ∧
          ReferenceFirstLiveDownCompletionReadout.multipleSolutions B)
    have himage := MeasurableSet.subtype_image
      (ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h b) hm
    convert himage using 1
    ext z
    simp only [event, Set.mem_ofPred_eq, Set.mem_image, Subtype.exists, exists_and_right,
      exists_eq_right]
  have hread : ∀ (b : Fin (p.T + 1))
      (z : ReferenceGeneratedDownAmbiguityMeasurability.GeneratedLaunchFiber
        (rate := rate) rewards C_star C_h b),
      ReferenceFirstLiveDownCompletionReadout.sourceDownReadouts
        rate rewards C_star C_h b (p.T - b) (by omega) i z =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h).map
        (fun r => ReferenceFirstLiveDownCompletionReadout.downReadout r i) := by
    intro b z
    unfold ReferenceFirstLiveDownCompletionReadout.sourceDownReadouts
    rw [ReferenceGeneratedDownAmbiguityMeasurability.generatedRun_records_eq_completeSuffixRecords_take]
    have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z.val rewards C_star C_h
    have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = b :=
      z.property.2
    rw [hstart] at hlen
    rw [List.take_of_length_le (by omega)]
  have heq : {z : BootstrapPrivateRoundStreams.SourceInput p |
      ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r i} =
      ⋃ b : Fin (p.T + 1), {z | b ≤ t.val} ∩ event b := by
    ext z
    constructor
    · rintro ⟨r, hr, B, hB, htimes, hmulti⟩
      have hby : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
          rate rewards C_star C_h t.val z := by
        by_contra hn
        rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
          rate rewards C_star C_h t z hn] at hr
        cases hr
      let b : Fin (p.T + 1) :=
        ⟨ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h, by
          have := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
          omega⟩
      have hz : z ∈ ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h b := ⟨hby.1, rfl⟩
      refine Set.mem_iUnion.mpr ⟨b, hby.2, hz, ReferenceFirstLiveDownCompletionReadout.downReadout r i,
        ?_, B, hB, htimes, hmulti⟩
      rw [hread b ⟨z, hz⟩, List.getElem?_map]
      have hlookup : (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[t.val - b]? = some r := by
        simpa only [ReferenceSourcePrefixHistoryFiltration.actualRecord,
          ite_eq_left hby.2] using hr
      rw [hlookup]
      rfl
    · intro hz
      obtain ⟨b, hb, hlaunch, data, hdata, B, hB, htimes, hmulti⟩ := Set.mem_iUnion.mp hz
      change b.val ≤ t.val at hb
      rw [hread b ⟨z, hlaunch⟩, List.getElem?_map] at hdata
      obtain ⟨r, hr, hrd⟩ := Option.map_eq_some_iff.mp hdata
      have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = b :=
        hlaunch.2
      refine ⟨r, ?_, B, ?_, htimes, hmulti⟩
      · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, hstart, ite_eq_left hb]
        exact hr
      · change (ReferenceFirstLiveDownCompletionReadout.downReadout r i).1 = some B
        rw [hrd]
        exact hB
  rw [heq]
  apply MeasurableSet.iUnion
  intro b
  by_cases hb : b ≤ t.val
  · simpa only [hb, Set.ofPred_true, Set.univ_inter] using hmeas b
  · simp only [hb, Set.ofPred_false, Set.empty_inter, MeasurableSet.empty]

private theorem measurable_some_image {A : Type*} [MeasurableSpace A]
    (S : Set A) (hS : MeasurableSet S) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace] (some '' S) := by
  refine ⟨Sum.inl '' S, measurableSet_inl_image.mpr hS, ?_⟩
  ext o
  cases o <;> simp

@[fun_prop] private theorem measurable_isSome {A : Type*} [MeasurableSpace A] :
    @Measurable (Option A) Bool LaterAssignmentStartMeasurability.optionMeasurableSpace
      inferInstance Option.isSome := by
  convert (measurable_const.sumElim measurable_const).comp
    (comap_measurable (Equiv.optionEquivSumPUnit A)) using 1
  funext o
  cases o <;> rfl

private theorem actualCode_test_borel
    (P : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) → Prop)
    (hP : MeasurableSet {code | P code}) (t : Fin p.T) :
    MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
      ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        P (ReferenceActiveHorizonMeasurability.roundRecordCode r)} := by
  let E := some '' {code | P code}
  have hE : MeasurableSet E := measurable_some_image _ hP
  have hm := hE.preimage ((measurable_pi_iff.mp
    (ReferenceInspectedPastRoundObservations.measurable_pastRoundObservations
      rate rewards C_star C_h p.T le_rfl)) t)
  convert hm using 1
  ext z
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none => simp only [E, ReferenceInspectedPastRoundObservations.pastRoundObservations,
      Fin.castLE_refl, hr, Option.map_none, Set.mem_preimage, Set.mem_image,
      Set.mem_ofPred_eq, reduceCtorEq, and_false, exists_false, false_and]
  | some r =>
    simp only [E, ReferenceInspectedPastRoundObservations.pastRoundObservations,
      Fin.castLE_refl, hr, Option.map_some, Set.mem_preimage, Set.mem_image,
      Set.mem_ofPred_eq, Option.some.injEq, exists_eq_right]
    exact ⟨fun ⟨_, heq, hp⟩ => heq ▸ hp, fun hp => ⟨r, rfl, hp⟩⟩

/-- Actual checked acceptance at a fixed source date is a Borel diagnostic test. -/
theorem actualAcceptance_borel (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
      ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        ReferenceFirstReplacementCollectionStoppedPureUpQuota.acceptanceAt r i} := by
  let P := fun h : Option (UpCode (p := p) (rate := rate)) =>
    ∃ d, h.map ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic = some d ∧
      (match diagnosticDecode (rate := rate) d with
      | .success _ => some d.input.selectedFollower
      | _ => none) = some i
  have hP : MeasurableSet {h | P h} := Set.to_countable _ |>.measurableSet
  have hm := hP.preimage ((measurable_pi_iff.mp
    (measurable_upHistory rate rewards C_star C_h)) t)
  convert hm using 1
  ext z
  change (∃ r, _ = some r ∧ _) ↔ P (upHistory rate rewards C_star C_h z t)
  constructor
  · rintro ⟨r, hr, ha⟩
    obtain ⟨d, hd, hacc⟩ := (acceptanceAt_iff_diagnostic rate r i).mp ha
    exact ⟨d, (upHistory_reconstructs rate rewards C_star C_h z t r hr).trans hd, hacc⟩
  · rintro ⟨d, hd, hacc⟩
    obtain ⟨r, hr, hdr⟩ := record_of_upHistory_some rate rewards C_star C_h z t d hd
    exact ⟨r, hr, (acceptanceAt_iff_diagnostic rate r i).mpr ⟨d, hdr, hacc⟩⟩

private def failureData
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :=
  ((ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
      code.2.2.1.2.2.2.2).failure.isSome,
    fun i : Fin (p.m - 1) =>
      (ReferenceFollowerTailComposition.reconstructFollowerObservable (code.2.2.2.1 i)).failure.isSome)

private theorem failureData_actual
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) :
    failureData (rate := rate) (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
      (r.output.coordinator.failure.isSome, fun i => (r.output.followers i).failure.isSome) := by
  have h := ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r
  apply Prod.ext
  · exact congrArg (fun o => o.failure.isSome) h.2.1
  · funext i
    exact congrArg (fun o => o.failure.isSome) (h.2.2.1 i)

/-- Every retained physical failure, including failures after decoder work,
is Borel on the unchanged original source. -/
theorem actualPhysicalFailure_borel (t : Fin p.T) :
    MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
      ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r} := by
  have hd : Measurable (failureData (p := p) (rate := rate)) := by
    let : MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
    let : MeasurableSpace (Option ReferenceActivePhysicalStep.CoordinatorFailure) :=
      LaterAssignmentStartMeasurability.optionMeasurableSpace
    let : MeasurableSpace (Option DeclaredFollowerLocalRound.RoundFailure) :=
      LaterAssignmentStartMeasurability.optionMeasurableSpace
    let : MeasurableSpace (Option (ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate)) :=
      LaterAssignmentStartMeasurability.optionMeasurableSpace
    change Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) =>
      (code.2.2.1.2.2.2.2.2.2.1.isSome, fun i : Fin (p.m - 1) => (code.2.2.2.1 i).2.1.isSome))
    apply Measurable.prodMk
    · exact measurable_isSome.comp measurable_snd.snd.fst.snd.snd.snd.snd.snd.snd.fst
    · apply measurable_pi_iff.mpr
      intro i
      exact measurable_isSome.comp
        (((measurable_pi_apply i).comp measurable_snd.snd.snd.fst).snd.fst)
  have hP : MeasurableSet {code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) | (failureData (rate := rate) code).1 = true ∨
        ∃ i, (failureData (rate := rate) code).2 i = true} :=
    (Set.to_countable {data : Bool × (Fin (p.m - 1) → Bool) |
      data.1 = true ∨ ∃ i, data.2 i = true}).measurableSet.preimage hd
  have hm := actualCode_test_borel rate rewards C_star C_h _ hP t
  convert hm using 1
  ext z
  apply exists_congr
  intro r
  rw [failureData_actual, ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt_iff]

private theorem actualSavedWrong_borel (t : Fin p.T) :
    MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
      ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r = true} := by
  have hP := (measurableSet_singleton true).preimage
    (ReferenceSavedWrongUniqueMeasurability.measurable_savedWrongCode (p := p) (rate := rate))
  have hm := actualCode_test_borel rate rewards C_star C_h _ hP t
  convert hm using 1
  ext z
  apply exists_congr
  intro r
  exact and_congr_right fun _ =>
    (by simpa only [ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag,
      decide_eq_true_eq, Set.mem_singleton_iff] using
      (ReferenceSavedWrongUniqueMeasurability.savedWrongCode_roundRecord_iff r).symm)

/-- Ambient Borelness of the exact common-stop event. Temporal adaptation
requires the separate pointwise round-end factor of the retained local tests. -/
theorem D_borel (s : ℕ) (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
      D rate rewards C_star C_h control0 s i t z} := by
  have huPresent : ∀ z, U rate rewards C_star C_h control0 i t z →
      ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r := by
    intro z hu
    obtain ⟨q, b, hb, hz, _⟩ := hu
    exact ⟨_, originalCurrent_lookup rate rewards C_star C_h control0 q t b hb i ⟨z, hz⟩⟩
  have heq : {z : BootstrapPrivateRoundStreams.SourceInput p |
      D rate rewards C_star C_h control0 s i t z} =
      {z | ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        ReferenceFirstReplacementCollectionStoppedPureUpQuota.acceptanceAt r i} ∪
      ({z | ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r} ∪
      ({z | ∃ r, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r = true} ∪
      ((⋃ k : Fin (p.m - 1), {z | ∃ r,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
          ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart s r k}) ∪
      {z | U rate rewards C_star C_h control0 i t z}))) := by
    ext z
    simp only [D, ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopAt,
      ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag_eq_true_iff,
      Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨r, hr, ha | hf | (hw | hamb) | hu⟩
      · exact Or.inl ⟨r, hr, ha⟩
      · exact Or.inr (Or.inl ⟨r, hr, hf⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨r, hr, hw⟩))
      · obtain ⟨k, hk⟩ := hamb
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, r, hr, hk⟩)))
      · have ht := (actualRecord_input_fields rate rewards C_star C_h t z r hr).2.2.1
        exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [U, ht] using hu))))
    · rintro (⟨r, hr, ha⟩ | ⟨r, hr, hf⟩ | ⟨r, hr, hw⟩ | ⟨k, r, hr, hk⟩ | hu)
      · exact ⟨r, hr, Or.inl ha⟩
      · exact ⟨r, hr, Or.inr (Or.inl hf)⟩
      · exact ⟨r, hr, Or.inr (Or.inr (Or.inl (Or.inl hw)))⟩
      · exact ⟨r, hr, Or.inr (Or.inr (Or.inl (Or.inr ⟨k, hk⟩)))⟩
      · obtain ⟨r, hr⟩ := huPresent z hu
        have ht := (actualRecord_input_fields rate rewards C_star C_h t z r hr).2.2.1
        exact ⟨r, hr, Or.inr (Or.inr (Or.inr (by simpa only [U, ht] using hu)))⟩
  rw [heq]
  exact (actualAcceptance_borel rate rewards C_star C_h i t).union
    ((actualPhysicalFailure_borel rate rewards C_star C_h t).union
      ((actualSavedWrong_borel rate rewards C_star C_h t).union
        ((MeasurableSet.iUnion fun k => actualDownAmbiguity_borel rate rewards C_star C_h s k t).union
          (U_borel rate rewards C_star C_h control0 i t))))

private theorem retainedFlag_congr (s : ℕ)
    (r r' : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hc : r.output.coordinator = r'.output.coordinator)
    (hf : r.output.followers = r'.output.followers)
    (hg : r.gridFeedback = r'.gridFeedback) (ht : r.input.time = r'.input.time)
    (hcurrent : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time) :
    ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag s r =
      ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag s r' := by
  have hw : ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r =
      ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r' := by
    unfold ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag
      ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted
    rw [hc, hf]
  have hB : ∀ i logged, ReferenceFirstLiveDownCompletionReadout.appendedDownBatch r i logged =
      ReferenceFirstLiveDownCompletionReadout.appendedDownBatch r' i logged := by
    intro i logged
    have ho : ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i =
        ReferenceFollowerDownDecoderReplay.preparedOwnObservation r' i := by
      unfold ReferenceFollowerDownDecoderReplay.preparedOwnObservation
      rw [r.output.preparation.feedback.observations_eq, r'.output.preparation.feedback.observations_eq]
      exact congrArg (ActualInitializationPhysicalStep.observationOfGrid p)
        (congrFun hg (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    have hin : ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate logged =
        ActiveFollowerDownAcceptance.currentRoundInput p i r'.input.row r'.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r' i) rate logged := by
      simp only [ActiveFollowerDownAcceptance.currentRoundInput, hcurrent, ho]
    unfold ReferenceFirstLiveDownCompletionReadout.appendedDownBatch
    rw [hin, ht]
  have hbatch : ∀ i, ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i =
      ReferenceFirstLiveDownCompletionReadout.completedDownBatch r' i := by
    intro i
    simp only [ReferenceFirstLiveDownCompletionReadout.completedDownBatch, hf, hB]
  simp only [ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag, hw,
    ReferenceFirstLiveDownCompletionReadout.completedAmbiguousAfterStart, hbatch]
  apply congrArg (fun b : Bool => ReferenceGeneratedSavedWrongEvent.savedWrongRecordFlag r' || b)
  exact decide_eq_decide.mpr Iff.rfl

/-- The exact common-stop event factors at round end, including retained
DOWN completion and every post-decoder failure path. -/
theorem D_factor (s : ℕ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    D rate rewards C_star C_h control0 s i t z ↔
      D rate rewards C_star C_h control0 s i t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) := by
  let z' := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z
  have hcode := actualRecordCode_factor rate rewards C_star C_h control0 (t.val + 1) t (by omega) z
  change (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
    ReferenceActiveHorizonMeasurability.roundRecordCode =
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z').map
      ReferenceActiveHorizonMeasurability.roundRecordCode at hcode
  change D rate rewards C_star C_h control0 s i t z ↔ D rate rewards C_star C_h control0 s i t z'
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none =>
    cases hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z' with
    | none => simp only [D, hr, hr', reduceCtorEq, false_and, exists_false]
    | some r' => simp only [hr, hr', Option.map_none, Option.map_some, reduceCtorEq] at hcode
  | some r =>
    cases hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z' with
    | none => simp only [hr, hr', Option.map_none, Option.map_some, reduceCtorEq] at hcode
    | some r' =>
      have he : ReferenceActiveHorizonMeasurability.roundRecordCode r =
          ReferenceActiveHorizonMeasurability.roundRecordCode r' := by
        simpa only [hr, hr', Option.map_some, Option.some.injEq] using hcode
      have hrec := ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r
      have hrec' := ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r'
      have hc : r.output.coordinator = r'.output.coordinator :=
        hrec.2.1.symm.trans (he ▸ hrec'.2.1)
      have hf : r.output.followers = r'.output.followers := by
        funext k
        exact (hrec.2.2.1 k).symm.trans (he ▸ hrec'.2.2.1 k)
      have hg : r.gridFeedback = r'.gridFeedback := by
        rw [← (ReferenceActiveHorizonMeasurability.roundRecordCode_front r).2.2.2,
          ← (ReferenceActiveHorizonMeasurability.roundRecordCode_front r').2.2.2, he]
      obtain ⟨hrows, hJ, ht, _⟩ := actualRecord_input_fields rate rewards C_star C_h t z r hr
      obtain ⟨hrows', hJ', ht', _⟩ := actualRecord_input_fields rate rewards C_star C_h t z' r' hr'
      have hcurrent : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time := by
        simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hrows', hJ, hJ', ht, ht', z',
          ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
          ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, ite_eq_left (Nat.lt_succ_self t.val)]
      have hflag := retainedFlag_congr rate s r r' hc hf hg (ht.trans ht'.symm) hcurrent
      have ha : ReferenceFirstReplacementCollectionStoppedPureUpQuota.acceptanceAt r i ↔
          ReferenceFirstReplacementCollectionStoppedPureUpQuota.acceptanceAt r' i := by
        rw [acceptanceAt_iff_diagnostic, acceptanceAt_iff_diagnostic, hc]
      have hphys : ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r ↔
          ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r' := by
        simp only [ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt, hc, hf]
      have hu := U_factor rate rewards C_star C_h control0 i t z
      simp only [U] at hu
      simp only [D, hr, hr', Option.some.injEq, exists_eq_left']
      simp only [ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopAt,
        ha, hphys, hflag, ht, ht', hu]
      rfl

/-- Round-end adaptation of the exact common-stop event. -/
theorem D_measurableSet (s : ℕ) (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 2)]
      {z : BootstrapPrivateRoundStreams.SourceInput p | D rate rewards C_star C_h control0 s i t z} := by
  rw [show t.val + 2 = (t.val + 1) + 1 by omega,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  refine ⟨{z | D rate rewards C_star C_h control0 s i t z},
    D_borel rate rewards C_star C_h control0 s i t, ?_⟩
  ext z
  exact (D_factor rate rewards C_star C_h control0 s i t z).symm

/-- The strict-past scan uses only the original prefix, for every natural
boundary, including boundaries after the horizon. -/
theorem L_factor (s u n : ℕ) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    L rate rewards C_star C_h control0 s u i n z = L rate rewards C_star C_h control0 s u i n
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  have hd : ∀ t : Fin p.T, t.val < n →
      (D rate rewards C_star C_h control0 s i t z ↔ D rate rewards C_star C_h control0 s i t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)) := by
    intro t ht
    have h := D_factor rate rewards C_star C_h control0 s i t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0
      (t.val + 1) n (by omega)] at h
    exact (D_factor rate rewards C_star C_h control0 s i t z).trans h.symm
  unfold L
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨t, hu, ht, h⟩
    exact ⟨t, hu, ht, (hd t ht).mp h⟩
  · rintro ⟨t, hu, ht, h⟩
    exact ⟨t, hu, ht, (hd t ht).mpr h⟩

/-- The finite strict-past flag is measurable before the next source round. -/
theorem L_measurable (s u n : ℕ) (i : Fin (p.m - 1)) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      (L rate rewards C_star C_h control0 s u i n) := by
  apply measurable_to_bool (f := L rate rewards C_star C_h control0 s u i n)
  change MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
    {z : BootstrapPrivateRoundStreams.SourceInput p | decide (∃ t : Fin p.T,
      u ≤ t.val + 1 ∧ t.val < n ∧ D rate rewards C_star C_h control0 s i t z) = true}
  simp only [decide_eq_true_eq, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro t
  by_cases hu : u ≤ t.val + 1
  · by_cases ht : t.val < n
    · simpa only [hu, ht, true_and] using ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).mono
        (show t.val + 2 ≤ n + 1 by omega)) _
          (D_measurableSet rate rewards C_star C_h control0 s i t)
    · simp only [ht, false_and, and_false, Set.ofPred_false, MeasurableSet.empty]
  · simp only [hu, false_and, Set.ofPred_false, MeasurableSet.empty]

private theorem lookup_of_prefix
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate)) (c : ℕ)
    (hprefix : K <+: (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).drop c)
    (a : Fin K.length)
    (htime : (K.get a).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + c + a.val) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (K.get a).input.time z = some (K.get a) := by
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hs : s ≤ (K.get a).input.time.val := by
    rw [htime]
    dsimp [s]
    omega
  have hsub : (K.get a).input.time.val - s = c + a.val := by
    rw [htime]
    dsimp [s]
    omega
  rcases hprefix with ⟨suffix, hsuffix⟩
  rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hs, hsub,
    ← List.getElem?_drop, ← hsuffix, List.getElem?_append_left a.isLt]
  exact List.getElem?_eq_getElem a.isLt

/-- Calendar alignment of the literal scan with an inclusive first-stop index.
The hypotheses here are local list facts; the actual branch constructor below
supplies all of them from the original physical suffix. -/
private theorem mask_of_actual_prefix
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (s c u : ℕ)
    (hs : s = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (hu : u = s + c + 1)
    (hprefix : K <+: (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).drop c)
    (hcalendar : ∀ a : Fin K.length, (K.get a).input.time.val + 1 = u + a.val)
    (i : Fin (p.m - 1)) (a : Fin K.length) :
    L rate rewards C_star C_h control0 s u i (u - 1 + a.val) z = false ↔
      a.val ≤ ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopIndex
        s K z rewards C_star C_h control0 i := by
  let stop : ReferenceCompletePhysicalHistory.RoundRecord p rate → Prop :=
    ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopAt
    s z rewards C_star C_h control0 i
  have hlookup : ∀ b : Fin K.length,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        (K.get b).input.time z = some (K.get b) := by
    intro b
    apply lookup_of_prefix rate rewards C_star C_h z K c hprefix b
    have hb := hcalendar b
    omega
  have hscan : (∃ t : Fin p.T, u ≤ t.val + 1 ∧ t.val < u - 1 + a.val ∧
      D rate rewards C_star C_h control0 s i t z) ↔
      ∃ b : Fin K.length, b.val < a.val ∧ stop (K.get b) := by
    constructor
    · rintro ⟨t, hut, hta, r, hr, hstop⟩
      have hba : t.val - (u - 1) < a.val := by omega
      let b : Fin K.length := ⟨t.val - (u - 1), hba.trans a.isLt⟩
      have hbtime : (K.get b).input.time = t := by
        apply Fin.ext
        have hb := hcalendar b
        have hbval : b.val = t.val - (u - 1) := rfl
        omega
      have heq : r = K.get b := by
        have hb := hlookup b
        rw [hbtime] at hb
        exact Option.some.inj (hr.symm.trans hb)
      exact ⟨b, hba, heq ▸ hstop⟩
    · rintro ⟨b, hba, hstop⟩
      refine ⟨(K.get b).input.time, ?_, ?_, K.get b, hlookup b, hstop⟩
      · have hb := hcalendar b
        omega
      · have hb := hcalendar b
        omega
  simp only [L, decide_eq_false_iff_not, hscan]
  constructor
  · intro hnone
    by_contra hnot
    have hf : ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopIndex
        s K z rewards C_star C_h control0 i < a.val := by omega
    let f := ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopIndex
      s K z rewards C_star C_h control0 i
    have hflen : f < K.length := hf.trans a.isLt
    have hstop : stop (K.get ⟨f, hflen⟩) :=
      of_decide_eq_true (List.findIdx_getElem (w := hflen))
    exact hnone ⟨⟨f, hflen⟩, hf, hstop⟩
  · intro ha hsome
    obtain ⟨b, hba, hstop⟩ := hsome
    have hbf : b.val < ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopIndex
        s K z rewards C_star C_h control0 i := hba.trans_le ha
    have hno := List.not_of_lt_findIdx (xs := K) (p := fun r => decide (stop r)) hbf
    exact (of_decide_eq_false hno) hstop

/-- Joint original-source round-end observations, strict-past adaptation, and
the SAME actual first-replacement inclusive mask. Only the original root data
are inputs; nonmatching physical branches retain their literal absence. -/
theorem complete_first_replacement_common_stop_observation :
    let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
    let pref := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0
    (∀ (i : Fin (p.m - 1)) (t : Fin p.T),
      MeasurableSet[F (t.val + 2)] {z | U rate rewards C_star C_h control0 i t z} ∧
      ∀ z, U rate rewards C_star C_h control0 i t z ↔
        U rate rewards C_star C_h control0 i t (pref (t.val + 1) z)) ∧
    (∀ (s : ℕ) (i : Fin (p.m - 1)) (t : Fin p.T),
      MeasurableSet[F (t.val + 2)] {z | D rate rewards C_star C_h control0 s i t z} ∧
      ∀ z, D rate rewards C_star C_h control0 s i t z ↔
        D rate rewards C_star C_h control0 s i t (pref (t.val + 1) z)) ∧
    (∀ (s u n : ℕ) (i : Fin (p.m - 1)),
      Measurable[F (n + 1)] (L rate rewards C_star C_h control0 s u i n) ∧
      ∀ z, L rate rewards C_star C_h control0 s u i n z =
        L rate rewards C_star C_h control0 s u i n (pref n z)) ∧
    (∀ (s u : ℕ) (i : Fin (p.m - 1)) z,
      L rate rewards C_star C_h control0 s u i 0 z = false ∧
      ∀ n n' : ℕ, n ≤ n' → L rate rewards C_star C_h control0 s u i n z = true →
        L rate rewards C_star C_h control0 s u i n' z = true) ∧
    ∀ z : BootstrapPrivateRoundStreams.SourceInput p,
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ _installed _) =>
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let Wtail := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: Wtail
            (∀ i : Fin (p.m - 1), ∀ a : Fin K.length,
              L rate rewards C_star C_h control0 s u i (u - 1 + a.val) z = false ↔
                a.val ≤ ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopIndex
                  s K z rewards C_star C_h control0 i) ∧
            (∀ i : Fin (p.m - 1), ∀ j : ℕ, ∀ a : Fin K.length,
              a.val < ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonPrefixLength
                s K z rewards C_star C_h control0 i j ↔
              a.val < j ∧ L rate rewards C_star C_h control0 s u i
                (u - 1 + a.val) z = false)
          | _ => True
      | _ => True := by
  refine ⟨(fun i t => ⟨U_measurableSet rate rewards C_star C_h control0 i t,
    U_factor rate rewards C_star C_h control0 i t⟩),
    (fun s i t => ⟨D_measurableSet rate rewards C_star C_h control0 s i t,
      D_factor rate rewards C_star C_h control0 s i t⟩),
    (fun s u n i => ⟨L_measurable rate rewards C_star C_h control0 s u n i,
      L_factor rate rewards C_star C_h control0 s u n i⟩),
    (fun s u i z => ⟨by simp [L],
      fun n n' hn => L_mono rate rewards C_star C_h control0 s u i z n n' hn⟩), ?_⟩
  intro z
  have hQ :=
    ReferenceFirstReplacementCollectionStoppedCompositeQuota.complete_first_replacement_collection_stopped_composite_quota
      rate z rewards C_star C_h control0
  dsimp only at hQ ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    rw [hb] at hQ
    dsimp only at hQ ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      rw [hbirth] at hQ
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hQ ⊢
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        rw [hc] at hQ
        dsimp only at hQ ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          rw [hcut] at hQ
          cases outcome <;> try trivial
          dsimp only at hQ ⊢
          let u := cut.input.time.val + 1
          let Wtail := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: Wtail
          obtain ⟨hcuttime, hcalendar, _hinjective, _hquota⟩ := hQ
          have hprefix : K <+: R.drop c := by
            have hdrop : R.drop c = cut :: R.drop (c + 1) :=
              by
                have hget := List.getElem?_eq_some_iff.mp hc
                simpa only [hget.2] using List.drop_eq_getElem_cons hget.1
            rw [hdrop]
            exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
          have hmask := mask_of_actual_prefix rate rewards C_star C_h control0 z K s c u
            rfl (by dsimp [u]; omega) hprefix hcalendar
          refine ⟨hmask, ?_⟩
          intro i j a
          rw [ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonPrefixLength_coordinate_iff,
            ← hmask i a]

end Bandits.Support.ReferenceFirstReplacementCollectionCommonStopObservation

end
