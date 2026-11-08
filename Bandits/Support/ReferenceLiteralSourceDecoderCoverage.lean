/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceSourceRawDecoderDecision

/-!
# Physical fixed-awaited calls and forward source decoder safety

Sources: pinned ZIP4 `05_binary_transport.tex:23-55`,
`06_interruptions.tex:140-177,425-487`,
`appendix_a_local_protocol.tex:87-157`, and
`appendix_b_communication.tex:94-99,725-751`.

The local predicates below use the actual sender and the ordinary parser and
acceptance test. They do not use saved comparison or expected-word fields.
The source ambiguity events keep every original positive entry and every
selected date in the witnessed interval, including zero observations.

Only the forward source implication is established. In particular, the local
dictionaries do not establish arbitrary-source reverse ambiguity coverage.
Physical execution continues through the whole horizon. These are internal
results for `ReferenceFirstCollectionLiteralStoppedCharge`, not a probability
bound or a manuscript closure claim.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceLiteralSourceDecoderCoverage

open ConstructorDimensions AffineBatchDecoder
open ReferenceFollowerDownDecoderReplay
open scoped Classical


variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Word := AffineChannelLaw.Word (width p)
abbrev Batch := List (AffineBatchDecoder.Entry p.T (width p))
abbrev Down := OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)
abbrev Up := OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

/-- A selected DOWN call to an unoccupied receiver, on the passed physical
domains, whose actual sender offers `w` and whose ordinary parse is acceptable.
There is deliberately no positivity condition on the receiver observation. -/
def physicalAwaitedDownAt (r : Record (rate := rate)) (i : Fin (p.m - 1))
    (w : Word (p := p)) : Prop :=
  ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (M : Down (rate := rate)),
    (r.output.followers i).downInput = some logged ∧
    (r.output.followers i).down = some cut ∧
    ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
    logged.status = .unoccupied ∧
    ActiveFollowerDownAcceptance.registerInputDomain p rate logged ∧
    ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch ∧
    ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer ∧
    ReferenceActiveAffinePositiveTest.downSent r.input = some w ∧
    ReferenceDownReception.ordinaryParse p rate (some w) = some M ∧
    ReferencePrelaunchFollower.acceptedStart logged < M.val.sigma ∧
    M.val.sigma ≤ r.input.time.val + 1

/-- A reached UP call with passed physical input domains, cutoff, slot, and
pending receiver, offering the actual encoded positive-start ordinary record.
The ordinary acceptance test is evaluated at the physical calendar date. -/
def physicalAwaitedUpAt (r : Record (rate := rate)) (i : Fin (p.m - 1))
    (M : Up (rate := rate)) : Prop :=
  ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
    r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
    CoordinatorUpReception.receptionInputDomain d.input ∧
    d.input.ledger.cutoff ≤ d.input.time.val + 1 ∧
    d.input.slot = PublicDiscreteDraws.upSlot ∧
    i ∈ d.input.ledger.pending ∧
    ReferenceActiveAffinePositiveTest.upSent r.input = some (ReferenceCollectionUpFailureReadoutV2.enc rate M) ∧
    CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
      (some (ReferenceCollectionUpFailureReadoutV2.enc rate M)) = some M ∧
    1 ≤ M.val.sigma ∧
    OrdinaryMessageCodec.acceptUp (ReferencePrelaunchFollower.codecParams p rate.eta)
      d.input.ledger.cutoff (d.input.time.val + 1) i.val
      (CoordinatorCollectionLedger.pendingNaturalLabels d.input.ledger)
      d.input.ledger.sigma M

/-- The saved awaited DOWN readout gives the physical call without requiring
a successful recovery or a successful successor configuration. -/
theorem physicalAwaitedDownAt_of_awaitedDownAt
    (r : Record (rate := rate)) (i : Fin (p.m - 1)) (w : Word (p := p))
    (h : ReferenceFirstCollectionAwaitedDownFailureReadout.awaitedDownAt rate r i w) : physicalAwaitedDownAt r i w := by
  obtain ⟨logged, cut, hi, hd, hsel, hstatus, hreg, hbank, hbuffer, _⟩ :=
    ReferenceFirstCollectionAwaitedDownFailureReadout.awaitedDownAt_retained_call_fields rate r i w h
  obtain ⟨logged', M, hi', hp, hs, ht⟩ :=
    ReferenceFirstCollectionAwaitedDownFailureReadout.awaitedDownAt_strict_accepted_start rate r i w h
  cases hi.symm.trans hi'
  obtain ⟨l, c, hl, hc, hcompare, hexpected, _⟩ := h
  cases hi.symm.trans hl
  cases hd.symm.trans hc
  have hsender := ReferenceFirstCollectionAwaitedDownFailureReadout.awaitedDownAt_expected_sender_word rate r i w
    ⟨logged, cut, hi, hd, hcompare, hexpected, by
      rw [hp]
      exact ⟨hs, ht⟩⟩
  have hfields := ReferenceFirstLiveDownCompletionReadout.retained_call_fields
    r i logged cut hi hd hcompare
  have hsent : ReferenceActiveAffinePositiveTest.downSent r.input = some w := by
    rw [← ReferenceSourceRawDecoderDecision.retained_down_sent r i logged cut hi hd hcompare,
      hfields.2.2.2.2.2.2.1]
    exact hsender
  exact ⟨logged, cut, M, hi, hd, hsel, hstatus, hreg, hbank, hbuffer, hsent, hp, hs, ht⟩

/-- The five actual DOWN guards reconstruct comparison presence. The word
comparison itself need not succeed and the later recovery need not finish. -/
theorem awaitedDownAt_of_physicalAwaitedDownAt
    (r : Record (rate := rate)) (i : Fin (p.m - 1)) (w : Word (p := p))
    (h : physicalAwaitedDownAt r i w) : ReferenceFirstCollectionAwaitedDownFailureReadout.awaitedDownAt rate r i w := by
  obtain ⟨logged, cut, M, hi, hd, hsel, hstatus, hreg, hbank, hbuffer, hsent, hp, hs, ht⟩ := h
  have hactual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    r i logged cut hi hd
  have hcompare : cut.rawComparison.isSome = true := by
    rw [hactual]
    unfold ReferenceDownReception.referenceDownCut
    simp only [dite_eq_left hsel, dite_eq_left hstatus, dite_eq_left hreg, dite_eq_left hbank, dite_eq_left hbuffer]
    split <;> rfl
  refine ⟨logged, cut, hi, hd, hcompare, ?_, ?_⟩
  · rw [ReferenceSourceRawDecoderDecision.retained_down_sent r i logged cut hi hd hcompare]
    exact hsent
  · rw [hp]
    exact ⟨hs, ht⟩

/-- The local dictionary is on the same physical record, follower, and word.
It imposes no positive-feedback or completed-bank requirement. -/
theorem physicalAwaitedDownAt_iff
    (r : Record (rate := rate)) (i : Fin (p.m - 1)) (w : Word (p := p)) :
    physicalAwaitedDownAt r i w ↔ ReferenceFirstCollectionAwaitedDownFailureReadout.awaitedDownAt rate r i w :=
  ⟨awaitedDownAt_of_physicalAwaitedDownAt r i w,
    physicalAwaitedDownAt_of_awaitedDownAt r i w⟩

/-- The ordinary parser inverts the actual flat encoding. -/
theorem parseUp_encoded (M : Up (rate := rate)) :
    CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
      (some (ReferenceCollectionUpFailureReadoutV2.enc rate M)) = some M := by
  change OrdinaryMessageCodec.parseUp (ReferencePrelaunchFollower.codecParams p rate.eta)
    (some ((OrdinaryMessageCodec.wordEquivFlat _).symm
      ((OrdinaryMessageCodec.wordEquivFlat _) (OrdinaryMessageCodec.encodeUp _ M)))) = some M
  rw [Equiv.symm_apply_apply]
  exact OrdinaryMessageCodec.parseUp_encode _ M

/-- Passed domains identify the actual input cursor with its physical date;
positive sigma follows from ordinary acceptance and the passed ledger. -/
theorem physicalAwaitedUpAt_of_awaitedUpAt
    (r : Record (rate := rate)) (i : Fin (p.m - 1)) (M : Up (rate := rate))
    (h : ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate r i M) : physicalAwaitedUpAt r i M := by
  obtain ⟨d, hd, hi, hc, hg, he, ha⟩ := h
  have hdom := (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mp hc
  obtain ⟨_, hsigma, _, _, _, _, htime, _⟩ :=
    CoordinatorUpReception.receptionInputDomain_parts d.input hdom
  have hacc := (CoordinatorCollectionLedger.acceptUpCheck_iff _ _ _).mp ha
  have hlabel : M.val.sigma = d.input.ledger.sigma := hacc.2.2
  obtain ⟨hcut, hslot, hpending⟩ := hg
  refine ⟨d, hd, hi, hdom, hcut, hslot, hi ▸ hpending, ?_,
    parseUp_encoded M, ?_, ?_⟩
  · rw [← ReferenceSourceRawDecoderDecision.retained_up_sent r d hd]
    exact he
  · omega
  · simpa only [OrdinaryMessageCodec.acceptUp, htime, CoordinatorCollectionLedger.sourceRound] using hacc

/-- Reconstruct the saved UP awaited diagnostic from actual sender and
ordinary acceptance. No ledger reconstruction or finish success is assumed. -/
theorem awaitedUpAt_of_physicalAwaitedUpAt
    (r : Record (rate := rate)) (i : Fin (p.m - 1)) (M : Up (rate := rate))
    (h : physicalAwaitedUpAt r i M) : ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate r i M := by
  obtain ⟨d, hd, hi, hdom, hcut, hslot, hpending, he, _, _, ha⟩ := h
  obtain ⟨_, _, _, _, _, _, htime, _⟩ :=
    CoordinatorUpReception.receptionInputDomain_parts d.input hdom
  have hc := (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mpr hdom
  refine ⟨d, hd, hi, hc, ⟨hcut, hslot, hi.symm ▸ hpending⟩, ?_, ?_⟩
  · rw [ReferenceSourceRawDecoderDecision.retained_up_sent r d hd]
    exact he
  · apply (CoordinatorCollectionLedger.acceptUpCheck_iff _ _ _).mpr
    simpa only [OrdinaryMessageCodec.acceptUp, htime, CoordinatorCollectionLedger.sourceRound] using ha

/-- The UP dictionary also covers zero receiver observations. The initial
placeholder is excluded by ordinary acceptance on the positive-start ledger. -/
theorem physicalAwaitedUpAt_iff
    (r : Record (rate := rate)) (i : Fin (p.m - 1)) (M : Up (rate := rate)) :
    physicalAwaitedUpAt r i M ↔ ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate r i M :=
  ⟨awaitedUpAt_of_physicalAwaitedUpAt r i M,
    physicalAwaitedUpAt_of_awaitedUpAt r i M⟩

/-- The literal completed DOWN bank: original pending entries, current
positive append, quota, and clearing update, before subsequent recovery. -/
def physicalDownCompletedAt (r : Record (rate := rate)) (i : Fin (p.m - 1))
    (W : Batch (p := p)) : Prop :=
  ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
    (r.output.followers i).downInput = some logged ∧
    (r.output.followers i).down = some cut ∧
    ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
    logged.status = .unoccupied ∧
    ActiveFollowerDownAcceptance.registerInputDomain p rate logged ∧
    ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch ∧
    ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer ∧
    W = logged.downBatch.pending ++ positiveAt p
      (ActiveFollowerDownAcceptance.currentInputExtension p
        (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
          (preparedOwnObservation r i) rate logged)) r.input.time ∧
    W.length = quota p ∧
    (ActiveFollowerDownAcceptance.currentDecodeStep p i r.input.row r.input.time
      (preparedOwnObservation r i) rate logged).1 =
        ⟨[], logged.downBatch.completed ++ [W]⟩ ∧
    cut.raw = batchOutput W

/-- A literal completed UP bank on the actually selected receiver, preserving
the carried partial batch even when it predates formation of the current UP. -/
def physicalUpCompletedAt (r : Record (rate := rate)) (i : Fin (p.m - 1))
    (W : Batch (p := p)) : Prop :=
  ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
    r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
    CoordinatorUpReception.receptionInputDomain d.input ∧
    eligible (CoordinatorUpReception.roundInput d.input) ∧
    W = (d.input.upDecoderBank i).pending ++
      positiveAt p (CoordinatorUpReception.traceAt d.input) d.input.time ∧
    W.length = quota p ∧
    d.decoderAfter = ⟨[], (d.input.upDecoderBank i).completed ++ [W]⟩ ∧
    d.raw = batchOutput W

/-- The completed readout produces all physical append/quota/clear fields. -/
theorem physicalDownCompletedAt_of_completedDownBatch
    (r : Record (rate := rate)) (i : Fin (p.m - 1)) (W : Batch (p := p))
    (h : ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i = some W) :
    physicalDownCompletedAt r i W := by
  obtain ⟨hlen, logged, cut, hi, hd, hc, hbank, hclear, hraw⟩ :=
    ReferenceFirstLiveDownCompletionReadout.completedDownBatch_spec r i W h
  obtain ⟨hsel, hstatus, hreg, hdecoder, hbuffer, _⟩ :=
    ReferenceFirstLiveDownCompletionReadout.retained_call_fields r i logged cut hi hd hc
  exact ⟨logged, cut, hi, hd, hsel, hstatus, hreg, hdecoder, hbuffer,
    hbank, hlen, hclear, hraw⟩

/-- The UP readout likewise produces the original bank and exact clearing
update; this uses the reached call even if its later finish fails. -/
theorem physicalUpCompletedAt_of_completedUpBatch
    (r : Record (rate := rate)) (i : Fin (p.m - 1)) (W : Batch (p := p))
    (h : ReferenceCollectionUpFailureReadoutV2.completedUpBatch rate r i = some W) :
    physicalUpCompletedAt r i W := by
  obtain ⟨d, hd, hi, hc, hel, _, hbank⟩ :=
    (ReferenceCollectionUpFailureReadoutV2.completedUpBatch_eq_some_iff rate r i W).mp h
  obtain ⟨hlen, d', hd', hi', hclear, hraw⟩ :=
    ReferenceCollectionUpFailureReadoutV2.completedUpBatch_spec rate r i W h
  cases hd.symm.trans hd'
  refine ⟨d, hd, hi,
    (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mp hc,
    hel, ?_, hlen, hclear, hraw⟩
  simpa only [ReferenceCollectionUpFailureReadoutV2.appendedUp, hi] using hbank.symm

/-- A retained DOWN positive entry carries the actual call time and the
actual focal affine sample, rather than a reconstructed satisfying equation. -/
theorem downPositiveEntry_original_coordinates
    (r : Record (rate := rate)) (i : Fin (p.m - 1))
    (e : AffineBatchDecoder.Entry p.T (width p))
    (he : e ∈ actualDownPositives i [r]) :
    e.time = r.input.time ∧ e.sample = (r.input.row.2 r.input.time).2 (0, i) := by
  obtain ⟨call, hcall, hentry⟩ := List.mem_flatMap.mp he
  obtain ⟨record, hrecord, hcall⟩ := List.mem_filterMap.mp hcall
  have hrecord' : record = r := List.mem_singleton.mp hrecord
  subst record
  have hel : eligible call.2 := by
    by_contra hn
    simp only [positiveAt, ActiveFollowerDownAcceptance.currentInputExtension,
      hn, ite_false, List.not_mem_nil] at hentry
  have heq : e = ⟨call.1, call.2.sample⟩ := by
    simpa only [positiveAt, ActiveFollowerDownAcceptance.currentInputExtension,
      hel, ite_true, List.mem_singleton, AffineBatchDecoder.entry] using hentry
  have hfields := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
    r i call hcall
  exact ⟨congrArg AffineBatchDecoder.Entry.time heq |>.trans hfields.1,
    congrArg AffineBatchDecoder.Entry.sample heq |>.trans hfields.2.1⟩

/-- The UP positive origin similarly keeps the actual receiver time and
the selected channel's original affine sample, even if later finish fails. -/
theorem upPositiveEntry_original_coordinates
    (r : Record (rate := rate)) (i : Fin (p.m - 1))
    (e : AffineBatchDecoder.Entry p.T (width p))
    (he : e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i) :
    e.time = r.input.time ∧ e.sample = (r.input.row.2 r.input.time).2 (1, i) := by
  cases hd : r.output.coordinator.up with
  | none =>
      simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
        hd, List.not_mem_nil] at he
  | some d =>
      have hi : d.input.selectedFollower = i := by
        by_contra hn
        simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
          hd, ReferenceCoordinatorUpDecoderReplay.retainedUpFollower,
          hn, ite_false, List.not_mem_nil] at he
      have hel : eligible (CoordinatorUpReception.roundInput d.input) := by
        by_contra hn
        simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
          hd, ReferenceCoordinatorUpDecoderReplay.retainedUpFollower, hi, ite_true,
          ReferenceCoordinatorUpDecoderReplay.retainedUpTime, positiveAt,
          ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
          hn, ite_false, List.not_mem_nil] at he
      have heq0 : e = ⟨d.input.time, (CoordinatorUpReception.roundInput d.input).sample⟩ := by
        simpa only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
          hd, ReferenceCoordinatorUpDecoderReplay.retainedUpFollower, hi, ite_true,
          ReferenceCoordinatorUpDecoderReplay.retainedUpTime, positiveAt,
          ReferenceCoordinatorUpDecoderReplay.constantInputTrace, hel, ite_true,
          List.mem_singleton, AffineBatchDecoder.entry] using he
      have heq : e = ⟨d.input.time, d.input.affineSample⟩ := by
        simpa only [CoordinatorUpReception.roundInput] using heq0
      obtain ⟨ledger, _, _, _, htime, _, hselected, hsample, _⟩ :=
        ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd
      have hchannel : CoordinatorUpMeasurability.selectedChannelFollower
          ((r.input.rows r.input.selected).2 r.input.time) = i :=
        hselected.symm.trans hi
      refine ⟨congrArg AffineBatchDecoder.Entry.time heq |>.trans htime, ?_⟩
      rw [heq]
      exact hsample.trans (congrArg
        (fun j => ((r.input.rows r.input.selected).2 r.input.time).2 (1, j)) hchannel)

section WholeSource

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

/-- Public launch/absence facts identify the original whole rows, private
selected index, reward table, and physical date of every actual source record. -/
theorem actualRecord_original_fields
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (r : Record (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
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
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

/-- Literal wrong acceptance on the original source. The three bodies are
already physical ordinary decisions: a completed unique bank, comparison to
the actual option-valued sender, and ordinary direction Parse/Acc. Prelaunch
uses the inherited prefix bank and absent sender, with no fabricated record. -/
def S_false (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) : Prop :=
  (∃ i, ReferenceSourceRawDecoderDecision.prelaunch_down_wrong
    rate rewards C_star C_h z t i) ∨
  (∃ i, ReferenceSourceRawDecoderDecision.source_down_wrong
    rate rewards C_star C_h z t i) ∨
  (∃ i, ReferenceSourceRawDecoderDecision.source_up_wrong
    rate rewards C_star C_h z t i)

/-- A completed DOWN Q-bank with two distinct solvers and one common actual
sent word throughout an awaited interval. Original entries, source dates,
whole rows, and receiver-positive provenance are retained, and ordinary
Parse/Acc is required at every selected date, including zero observations. -/
def literalDownAmbiguityAt (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) : Prop :=
  ∃ (r : Record (rate := rate)) (i : Fin (p.m - 1)) (w : Word (p := p))
      (W : Batch (p := p)) (a : Fin p.T),
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
    physicalDownCompletedAt r i W ∧ a.val ≤ t.val ∧
    (∃ u v, satisfies (samples W) u ∧ satisfies (samples W) v ∧ u ≠ v) ∧
    (∀ e ∈ W, a.val ≤ e.time.val ∧ e.time.val ≤ t.val ∧ equation e.sample w ∧
      ∃ re : Record (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h e.time z = some re ∧
        re.input.rows = z.1.2 ∧
        re.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        re.input.time = e.time ∧ re.input.rewards = rewards ∧
        e.sample = ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2
          e.time).2 (0, i) ∧
        e ∈ actualDownPositives i [re] ∧ physicalAwaitedDownAt re i w) ∧
    (∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ t.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 =
          some (0, i) →
      ∃ rv : Record (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h v z = some rv ∧
        rv.input.rows = z.1.2 ∧
        rv.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        rv.input.time = v ∧ rv.input.rewards = rewards ∧ physicalAwaitedDownAt rv i w)

/-- The UP version retains the same original completed bank and positive
origins; the fixed word is an actual encoding of an ordinary accepted record
with positive start, so the initial placeholder cannot witness this event. -/
def literalUpAmbiguityAt (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) : Prop :=
  ∃ (r : Record (rate := rate)) (i : Fin (p.m - 1)) (M : Up (rate := rate))
      (W : Batch (p := p)) (a : Fin p.T),
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
    physicalUpCompletedAt r i W ∧ a.val ≤ t.val ∧ 1 ≤ M.val.sigma ∧
    (∃ u v, satisfies (samples W) u ∧ satisfies (samples W) v ∧ u ≠ v) ∧
    (∀ e ∈ W, a.val ≤ e.time.val ∧ e.time.val ≤ t.val ∧
      equation e.sample (ReferenceCollectionUpFailureReadoutV2.enc rate M) ∧
      ∃ re : Record (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h e.time z = some re ∧
        re.input.rows = z.1.2 ∧
        re.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        re.input.time = e.time ∧ re.input.rewards = rewards ∧
        e.sample = ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2
          e.time).2 (1, i) ∧
        e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries re i ∧
        physicalAwaitedUpAt re i M) ∧
    (∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ t.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 =
          some (1, i) →
      ∃ rv : Record (rate := rate),
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h v z = some rv ∧
        rv.input.rows = z.1.2 ∧
        rv.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
        rv.input.time = v ∧ rv.input.rewards = rewards ∧ physicalAwaitedUpAt rv i M)

/-- The source's fixed-awaited ambiguity event, separately from wrong unique
acceptance. Mixed and inconsistent banks do not suffice for this predicate. -/
def S_amb (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) : Prop :=
  literalDownAmbiguityAt rate rewards C_star C_h z t ∨
    literalUpAmbiguityAt rate rewards C_star C_h z t

/-- Translate the saved DOWN detector using its full positive history and
calendar witnesses, and consume the physical local dictionary at each date. -/
theorem literalDownAmbiguityAt_of_fixedAwaitedDownFailureAt
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (h : ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
      rate rewards C_star C_h z t) :
    literalDownAmbiguityAt rate rewards C_star C_h z t := by
  obtain ⟨r, i, w, W, a, hr, hW, hat, hmulti, hentries, hcalendar⟩ := h
  refine ⟨r, i, w, W, a, hr, physicalDownCompletedAt_of_completedDownBatch r i W hW,
    hat, (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff W).mp hmulti, ?_, ?_⟩
  · intro e he
    obtain ⟨ha, ht, heq, re, hre, hpositive, haw⟩ := hentries e he
    obtain ⟨hrows, hselected, htime, hrewards⟩ :=
      actualRecord_original_fields rate rewards C_star C_h z e.time re hre
    have hsample := (downPositiveEntry_original_coordinates re i e hpositive).2
    change e.sample = ((re.input.rows re.input.selected).2 re.input.time).2 (0, i) at hsample
    rw [hrows, hselected, htime] at hsample
    exact ⟨ha, ht, heq, re, hre, hrows, hselected, htime, hrewards, hsample, hpositive,
      physicalAwaitedDownAt_of_awaitedDownAt re i w haw⟩
  · intro v ha ht hchannel
    obtain ⟨rv, hrv, haw⟩ := hcalendar v ha ht hchannel
    obtain ⟨hrows, hselected, htime, hrewards⟩ :=
      actualRecord_original_fields rate rewards C_star C_h z v rv hrv
    exact ⟨rv, hrv, hrows, hselected, htime, hrewards,
      physicalAwaitedDownAt_of_awaitedDownAt rv i w haw⟩

/-- Translate UP ambiguity on the same whole source, date, follower, record,
encoded word, completed bank, interval, and every original positive origin. -/
theorem literalUpAmbiguityAt_of_fixedAwaitedUpFailureAt
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (h : ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
      rate rewards C_star C_h z t) :
    literalUpAmbiguityAt rate rewards C_star C_h z t := by
  obtain ⟨r, i, M, W, a, hr, hW, hat, hsigma, hmulti, hentries, hcalendar⟩ := h
  refine ⟨r, i, M, W, a, hr, physicalUpCompletedAt_of_completedUpBatch r i W hW,
    hat, hsigma, (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff W).mp hmulti,
    ?_, ?_⟩
  · intro e he
    obtain ⟨ha, ht, heq, re, hre, hpositive, haw⟩ := hentries e he
    obtain ⟨hrows, hselected, htime, hrewards⟩ :=
      actualRecord_original_fields rate rewards C_star C_h z e.time re hre
    have hsample := (upPositiveEntry_original_coordinates re i e hpositive).2
    change e.sample = ((re.input.rows re.input.selected).2 re.input.time).2 (1, i) at hsample
    rw [hrows, hselected, htime] at hsample
    exact ⟨ha, ht, heq, re, hre, hrows, hselected, htime, hrewards, hsample, hpositive,
      physicalAwaitedUpAt_of_awaitedUpAt re i M haw⟩
  · intro v ha ht hchannel
    obtain ⟨rv, hrv, haw⟩ := hcalendar v ha ht hchannel
    obtain ⟨hrows, hselected, htime, hrewards⟩ :=
      actualRecord_original_fields rate rewards C_star C_h z v rv hrv
    exact ⟨rv, hrv, hrows, hselected, htime, hrewards,
      physicalAwaitedUpAt_of_awaitedUpAt rv i M haw⟩

/-- Forward source safety: each saved detector failure is an actual ordinary
wrong acceptance or a physical fixed-awaited ambiguous Q-bank. The saved
union alone is insufficient; both raw and awaited dictionaries are consumed. -/
theorem decoderFailureAt_implies_literal_source_failure
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (h : ReferenceFirstCollectionInclusiveDecoderStop.decoderFailureAt
      rate rewards C_star C_h z t) :
    S_false rate rewards C_star C_h z t ∨ S_amb rate rewards C_star C_h z t := by
  rcases (ReferenceFirstCollectionInclusiveDecoderStop.decoderFailureAt_sourceWitnesses
    rate rewards C_star C_h z t).mp h with hpre | hwrong | hdown | hup
  · obtain ⟨i, hi⟩ := hpre
    exact Or.inl (Or.inl ⟨i,
      (ReferenceSourceRawDecoderDecision.prelaunch_down_wrong_iff
        rate rewards C_star C_h z t i).mpr hi⟩)
  · have hraw := (ReferenceSourceRawDecoderDecision.actual_raw_wrong_decision_iff_saved_diagnostic
      rate rewards C_star C_h z t).mpr hwrong
    exact Or.inl (Or.inr hraw)
  · exact Or.inr (Or.inl
      (literalDownAmbiguityAt_of_fixedAwaitedDownFailureAt rate rewards C_star C_h z t hdown))
  · exact Or.inr (Or.inr
      (literalUpAmbiguityAt_of_fixedAwaitedUpFailureAt rate rewards C_star C_h z t hup))

/-- Absence of literal source failures strictly before `n` clears the existing
postlaunch past flag. The detecting date itself is not removed by this rule. -/
theorem pastFailureFlag_false_of_no_earlier_literal_failure
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ)
    (h : ∀ t : Fin p.T, t.val < n →
      ¬ (S_false rate rewards C_star C_h z t ∨ S_amb rate rewards C_star C_h z t)) :
    ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag
      rate rewards C_star C_h n z = false := by
  apply (ReferenceFirstCollectionAwaitedDownFailureReadout.pastFailureFlag_false_iff_no_earlier_failure
    rate rewards C_star C_h z n).mpr
  intro t ht hfailure
  exact h t ht (decoderFailureAt_implies_literal_source_failure
    rate rewards C_star C_h z t (Or.inr hfailure))

/-- The same strict-past conclusion for the union with the prelaunch scan. -/
theorem decoderPastFlag_false_of_no_earlier_literal_failure
    (z : BootstrapPrivateRoundStreams.SourceInput p) (n : ℕ) (hn : n ≤ p.T)
    (h : ∀ t : Fin p.T, t.val < n →
      ¬ (S_false rate rewards C_star C_h z t ∨ S_amb rate rewards C_star C_h z t)) :
    ReferenceFirstCollectionInclusiveDecoderStop.decoderPastFlag
      rate rewards C_star C_h n hn z = false := by
  apply (ReferenceFirstCollectionInclusiveDecoderStop.decoderPastFlag_false_iff_no_earlier_failure
    rate rewards C_star C_h n hn z).mpr
  intro t ht hfailure
  exact h t ht (decoderFailureAt_implies_literal_source_failure
    rate rewards C_star C_h z t hfailure)

end WholeSource

end Bandits.Support.ReferenceLiteralSourceDecoderCoverage

end
