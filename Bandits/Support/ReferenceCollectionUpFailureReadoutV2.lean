/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFormedUpSourceDetectingCut
public import Bandits.Support.ReferenceFirstCollectionStoppedOldDownQuota

/-!
# Strict-past actual completed UP failure readout

This module reads completed fixed-awaited-word ambiguity from the existing
physical round records and original source. It does not add a run, mask,
quota, or source-wide event equality.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:27-55`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`, and
`sources/zip4/manuscript/06_interruptions.tex:431-487`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceCollectionUpFailureReadoutV2

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

abbrev Z := BootstrapPrivateRoundStreams.SourceInput p
abbrev I := Fin (p.m - 1)
abbrev Q := AffineBatchDecoder.quota p
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Batch := List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
abbrev UP := OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

abbrev enc (U : UP (p := p) (rate := rate)) :=
  ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord (p := p) (rate := rate) U

abbrev lookup (t : Fin p.T) (z : Z (p := p)) :=
  ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z

abbrev F (c : ContinuousLearningRows.TimeControl p) :=
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration c

abbrev Init (z : Z (p := p)) :=
  ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate

abbrev s (z : Z (p := p)) :=
  ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output (Init rate rewards C_star C_h z)).completed

/-- The existing carried UP pending bank with the actual current positive
receiver entry, retaining the full incoming decoder bank at the call. -/
def appendedUp (d : ReferenceActivePhysicalStep.UpDiagnostic p rate) : Batch (p := p) :=
  (d.input.upDecoderBank d.input.selectedFollower).pending ++
    AffineBatchDecoder.positiveAt p (CoordinatorUpReception.traceAt d.input) d.input.time

/-- An actual retained checked eligible UP receiver call whose appended
physical batch reaches the decoder quota. Later ledger or clock completion is
not required. -/
def completedUpBatch (r : Record (rate := rate)) (i : I (p := p)) : Option (Batch (p := p)) :=
  match r.output.coordinator.up with
  | none => none
  | some d =>
      if d.input.selectedFollower = i ∧
          CoordinatorUpReception.receptionInputCheck d.input = true ∧
          AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
          Q (p := p) ≤ (appendedUp rate d).length then
        some (appendedUp rate d)
      else none

/-- The diagnostic at a record says that the fixed UP word was the saved
expected word and passed the ordinary ledger acceptance check. -/
def awaitedUpAt (r : Record (rate := rate)) (i : I (p := p)) (U : UP (p := p) (rate := rate)) : Prop :=
  ∃ d, r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
    CoordinatorUpReception.receptionInputCheck d.input = true ∧
    CoordinatorUpReception.receptionGate d.input ∧ d.expected = some (enc rate U) ∧
    CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i U = true

/-- One completed UP batch made entirely of actual positive entries from one
fixed awaited word, with every selected-channel round in its stamped interval
retained as a witness, including zero observations. -/
def fixedAwaitedUpFailureAt (z : Z (p := p)) (t : Fin p.T) : Prop :=
  ∃ (r : Record (rate := rate)) (i : I (p := p)) (U : UP (p := p) (rate := rate))
      (W : Batch (p := p)) (a : Fin p.T),
    lookup rate rewards C_star C_h t z = some r ∧
    completedUpBatch rate r i = some W ∧ a.val ≤ t.val ∧
    1 ≤ U.val.sigma ∧
    ReferenceFirstLiveDownCompletionReadout.multipleSolutions W ∧
    (∀ e ∈ W, a.val ≤ e.time.val ∧ e.time.val ≤ t.val ∧
      AffineBatchDecoder.equation e.sample (enc rate U) ∧
      ∃ re : Record (rate := rate), lookup rate rewards C_star C_h e.time z = some re ∧
        e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries re i ∧
        awaitedUpAt rate re i U) ∧
    (∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ t.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 = some (1, i) →
      ∃ rv : Record (rate := rate), lookup rate rewards C_star C_h v z = some rv ∧
        awaitedUpAt rate rv i U)

/-- The strict-past flag scans precisely physical times smaller than `n`. -/
def pastUpFailureFlag (n : ℕ) (z : Z (p := p)) : Bool :=
  decide (∃ t : Fin p.T, t.val < n ∧ fixedAwaitedUpFailureAt rate rewards C_star C_h z t)

private abbrev UpCode :=
  ReferenceCollectionServiceTailMeasurability.UpDiagnosticCode p rate
private abbrev RoundCode :=
  ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)
private abbrev Channel := ContinuousLearningRows.Channel p

/-- The retained countable UP-diagnostic projection of each actual physical
record. The full source rows and state are not replaced by this code. -/
private def upDiagnosticCodeHistory (z : Z (p := p)) : Fin p.T → Option (UpCode (p := p) (rate := rate)) :=
  fun v => (ReferenceInspectedPastRoundObservations.pastRoundObservations
    rate rewards C_star C_h p.T (Nat.le_refl p.T) z v).bind
      (ReferenceGeneratedUpBatchPrefixEvent.roundRecordUpDiagnosticCode
        (p := p) (rate := rate))

/-- The original selector at every calendar time, retaining all zero reads. -/
private def selectedChannelHistory (z : Z (p := p)) : Fin p.T → Option (Channel (p := p)) :=
  fun v => (ReferenceSelectedAffinePairLaw.selector p v z).2

private def decodeUpDiagnosticOption (code : Option (UpCode (p := p) (rate := rate))) :
    Option (ReferenceActivePhysicalStep.UpDiagnostic p rate) :=
  code.map ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic

private def completedUpBatchFromDiagnostic
    (diagnostic : Option (ReferenceActivePhysicalStep.UpDiagnostic p rate))
    (i : I (p := p)) : Option (Batch (p := p)) :=
  match diagnostic with
  | none => none
  | some d =>
      if d.input.selectedFollower = i ∧
          CoordinatorUpReception.receptionInputCheck d.input = true ∧
          AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
          Q (p := p) ≤ (appendedUp rate d).length then
        some (appendedUp rate d)
      else none

private def completedUpBatchFromCode (code : Option (UpCode (p := p) (rate := rate)))
    (i : I (p := p)) : Option (Batch (p := p)) :=
  completedUpBatchFromDiagnostic rate (decodeUpDiagnosticOption rate code) i

private def recordUpPositiveEntriesFromDiagnostic
    (diagnostic : Option (ReferenceActivePhysicalStep.UpDiagnostic p rate))
    (i : I (p := p)) : Batch (p := p) :=
  match diagnostic with
  | none => []
  | some d =>
      if d.input.selectedFollower = i then
        AffineBatchDecoder.positiveAt p
          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time
      else []

private def recordUpPositiveEntriesFromCode
    (code : Option (UpCode (p := p) (rate := rate))) (i : I (p := p)) : Batch (p := p) :=
  recordUpPositiveEntriesFromDiagnostic rate (decodeUpDiagnosticOption rate code) i

private def awaitedUpAtDiagnostic
    (diagnostic : Option (ReferenceActivePhysicalStep.UpDiagnostic p rate))
    (i : I (p := p)) (U : UP (p := p) (rate := rate)) : Prop :=
  ∃ d, diagnostic = some d ∧ d.input.selectedFollower = i ∧
    CoordinatorUpReception.receptionInputCheck d.input = true ∧
    CoordinatorUpReception.receptionGate d.input ∧ d.expected = some (enc rate U) ∧
    CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i U = true

private def awaitedUpAtCode (code : Option (UpCode (p := p) (rate := rate)))
    (i : I (p := p)) (U : UP (p := p) (rate := rate)) : Prop :=
  awaitedUpAtDiagnostic rate (decodeUpDiagnosticOption rate code) i U

private def fixedAwaitedUpFailureCodeAt
    (history : Fin p.T → Option (UpCode (p := p) (rate := rate)))
    (channels : Fin p.T → Option (Channel (p := p))) (t : Fin p.T) : Prop :=
  ∃ (i : I (p := p)) (U : UP (p := p) (rate := rate))
      (W : Batch (p := p)) (a : Fin p.T),
    completedUpBatchFromCode rate (history t) i = some W ∧ a.val ≤ t.val ∧
    1 ≤ U.val.sigma ∧ ReferenceFirstLiveDownCompletionReadout.multipleSolutions W ∧
    (∀ e ∈ W, a.val ≤ e.time.val ∧ e.time.val ≤ t.val ∧
      AffineBatchDecoder.equation e.sample (enc rate U) ∧
      e ∈ recordUpPositiveEntriesFromCode rate (history e.time) i ∧
      awaitedUpAtCode rate (history e.time) i U) ∧
    (∀ v : Fin p.T, a.val ≤ v.val → v.val ≤ t.val →
      channels v = some (1, i) → awaitedUpAtCode rate (history v) i U)

private abbrev ReadoutCodeData :=
  (Fin p.T → Option (UpCode (p := p) (rate := rate))) ×
    (Fin p.T → Option (Channel (p := p)))

private theorem measurable_optionBind {X Y W : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
    (f : Y → Option W) (hf : Measurable f) (g : X → Option Y) (hg : Measurable g) :
    Measurable (fun x => (g x).bind f) := by
  classical
  intro s hs
  let someImage : Set (Option Y) := some '' (f ⁻¹' s)
  have hsome : MeasurableSet someImage := by
    change MeasurableSet[
      (inferInstance : MeasurableSpace (Y ⊕ PUnit)).comap
        (Equiv.optionEquivSumPUnit Y)] someImage
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨Sum.inl '' (f ⁻¹' s), measurableSet_inl_image.mpr (hf hs), ?_⟩
    ext value
    cases value <;> simp [someImage]
  have hnone : MeasurableSet ({none} : Set (Option Y)) := by
    change MeasurableSet[
      (inferInstance : MeasurableSpace (Y ⊕ PUnit)).comap
        (Equiv.optionEquivSumPUnit Y)] {none}
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨{Sum.inr PUnit.unit}, ?_, ?_⟩
    · convert measurableSet_inr_image.mpr (measurableSet_singleton PUnit.unit) using 1
      ext value
      simp
    ext value
    cases value <;> simp
  have hpre :
      (fun x => (g x).bind f) ⁻¹' s = g ⁻¹'
        (someImage ∪ if (none : Option W) ∈ s then
          ({(none : Option Y)} : Set (Option Y)) else ∅) := by
    ext x
    cases h : g x <;> simp [h, someImage]
  have hrest : MeasurableSet (if (none : Option W) ∈ s then
      ({(none : Option Y)} : Set (Option Y)) else ∅) := by
    by_cases h : (none : Option W) ∈ s
    · simpa [h] using hnone
    · simp [h]
  have hmeas := hg (hsome.union hrest)
  rw [← hpre] at hmeas
  exact hmeas

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

private theorem upDiagnosticCodeHistory_eq_of_actualRecord
    (z : Z (p := p)) (v : Fin p.T) (r : Record (rate := rate))
    (hr : lookup rate rewards C_star C_h v z = some r) :
    decodeUpDiagnosticOption rate (upDiagnosticCodeHistory rate rewards C_star C_h z v) =
      r.output.coordinator.up := by
  have hobs := ReferenceInspectedPastRoundObservations.pastRoundObservations_some
    rate rewards C_star C_h p.T (Nat.le_refl p.T) z v r hr
  simp only [upDiagnosticCodeHistory, hobs, Option.bind_some]
  exact ReferenceGeneratedUpBatchPrefixEvent.roundRecordUpDiagnosticCode_reconstructs r

private theorem actualRecord_of_upDiagnosticCodeHistory_some
    (z : Z (p := p)) (v : Fin p.T) (code : UpCode (p := p) (rate := rate))
    (hcode : upDiagnosticCodeHistory rate rewards C_star C_h z v = some code) :
    ∃ r, lookup rate rewards C_star C_h v z = some r ∧
      decodeUpDiagnosticOption rate (some code) = r.output.coordinator.up := by
  cases hr : lookup rate rewards C_star C_h v z with
  | none =>
      simp [upDiagnosticCodeHistory, ReferenceInspectedPastRoundObservations.pastRoundObservations,
        hr] at hcode
  | some r =>
      have hobs := ReferenceInspectedPastRoundObservations.pastRoundObservations_some
        rate rewards C_star C_h p.T (Nat.le_refl p.T) z v r hr
      unfold upDiagnosticCodeHistory at hcode
      rw [hobs] at hcode
      simp only [Option.bind_some] at hcode
      refine ⟨r, rfl, ?_⟩
      have hdiag := ReferenceGeneratedUpBatchPrefixEvent.roundRecordUpDiagnosticCode_reconstructs r
      rw [hcode] at hdiag
      exact hdiag

private theorem completedUpBatch_from_diagnostic (r : Record (rate := rate))
    (i : I (p := p)) :
    completedUpBatch rate r i =
      completedUpBatchFromDiagnostic rate r.output.coordinator.up i := rfl

private theorem recordUpPositiveEntries_from_diagnostic (r : Record (rate := rate))
    (i : I (p := p)) :
    ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i =
      recordUpPositiveEntriesFromDiagnostic rate r.output.coordinator.up i := by
  cases h : r.output.coordinator.up with
  | none => simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
      recordUpPositiveEntriesFromDiagnostic, h]
  | some d =>
      by_cases hi : d.input.selectedFollower = i
      · simp [recordUpPositiveEntriesFromDiagnostic, h,
          ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
          ReferenceCoordinatorUpDecoderReplay.retainedUpFollower, hi,
          ReferenceCoordinatorUpDecoderReplay.retainedUpTime]
      · simp [recordUpPositiveEntriesFromDiagnostic, h,
          ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries,
          ReferenceCoordinatorUpDecoderReplay.retainedUpFollower, hi]

private theorem awaitedUpAt_from_diagnostic (r : Record (rate := rate))
    (i : I (p := p)) (U : UP (p := p) (rate := rate)) :
    awaitedUpAt rate r i U =
      awaitedUpAtDiagnostic rate r.output.coordinator.up i U := rfl

private theorem fixedAwaitedUpFailureAt_iff_code
    (z : Z (p := p)) (t : Fin p.T) :
    fixedAwaitedUpFailureAt rate rewards C_star C_h z t ↔
      fixedAwaitedUpFailureCodeAt rate
        (upDiagnosticCodeHistory rate rewards C_star C_h z)
        (selectedChannelHistory z) t := by
  constructor
  · rintro ⟨r, i, U, W, a, hrt, hbatch, hat, hsigma, hmulti, hentries, hchannels⟩
    have hdiagT := upDiagnosticCodeHistory_eq_of_actualRecord
      rate rewards C_star C_h z t r hrt
    refine ⟨i, U, W, a, ?_, hat, hsigma, hmulti, ?_, ?_⟩
    · change completedUpBatchFromDiagnostic rate
        (decodeUpDiagnosticOption rate
          (upDiagnosticCodeHistory rate rewards C_star C_h z t)) i = some W
      rw [hdiagT]
      change completedUpBatch rate r i = some W
      exact hbatch
    · intro e he
      rcases hentries e he with ⟨hbirth, htime, heq, re, hre, hpos, haw⟩
      have hdiagE := upDiagnosticCodeHistory_eq_of_actualRecord
        rate rewards C_star C_h z e.time re hre
      refine ⟨hbirth, htime, heq, ?_, ?_⟩
      · change e ∈ recordUpPositiveEntriesFromDiagnostic rate
          (decodeUpDiagnosticOption rate
            (upDiagnosticCodeHistory rate rewards C_star C_h z e.time)) i
        rw [hdiagE]
        change e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries re i
        exact hpos
      · change awaitedUpAtDiagnostic rate
          (decodeUpDiagnosticOption rate
            (upDiagnosticCodeHistory rate rewards C_star C_h z e.time)) i U
        rw [hdiagE]
        change awaitedUpAt rate re i U
        exact haw
    · intro v ha hv hchannel
      have hchannelActual :
          ReferenceSelectedAffinePairLaw.selectedChannel p
            ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v).1 =
              some (1, i) := by
        simpa [selectedChannelHistory, ReferenceSelectedAffinePairLaw.selector,
          ActualInitializationPhysicalStep.selectedRowIndex] using hchannel
      rcases hchannels v ha hv hchannelActual with ⟨rv, hrv, haw⟩
      have hdiagV := upDiagnosticCodeHistory_eq_of_actualRecord
        rate rewards C_star C_h z v rv hrv
      change awaitedUpAtDiagnostic rate
        (decodeUpDiagnosticOption rate
          (upDiagnosticCodeHistory rate rewards C_star C_h z v)) i U
      rw [hdiagV]
      change awaitedUpAt rate rv i U
      exact haw
  · rintro ⟨i, U, W, a, hbatch, hat, hsigma, hmulti, hentries, hchannels⟩
    have hdiagTsome : ∃ code, upDiagnosticCodeHistory rate rewards C_star C_h z t = some code := by
      cases hcode : upDiagnosticCodeHistory rate rewards C_star C_h z t with
      | none =>
          have : completedUpBatchFromCode rate none i = none := by
            simp [completedUpBatchFromCode, decodeUpDiagnosticOption,
              completedUpBatchFromDiagnostic]
          rw [hcode] at hbatch
          rw [this] at hbatch
          cases hbatch
      | some code => exact ⟨code, rfl⟩
    obtain ⟨ct, hct⟩ := hdiagTsome
    obtain ⟨r, hrt, hdiagT⟩ := actualRecord_of_upDiagnosticCodeHistory_some
      rate rewards C_star C_h z t ct hct
    have hbatch' : completedUpBatch rate r i = some W := by
      rw [hct] at hbatch
      change completedUpBatchFromDiagnostic rate
        (decodeUpDiagnosticOption rate (some ct)) i = some W at hbatch
      rw [hdiagT] at hbatch
      change completedUpBatch rate r i = some W at hbatch
      exact hbatch
    refine ⟨r, i, U, W, a, hrt, hbatch', hat, hsigma, hmulti, ?_, ?_⟩
    · intro e he
      rcases hentries e he with ⟨hbirth, htime, heq, hpos, haw⟩
      have hceSome : ∃ ce, upDiagnosticCodeHistory rate rewards C_star C_h z e.time = some ce := by
        cases hc : upDiagnosticCodeHistory rate rewards C_star C_h z e.time with
        | none =>
            have : False := by
              simp [awaitedUpAtCode, awaitedUpAtDiagnostic,
                decodeUpDiagnosticOption, hc] at haw
            exact this.elim
        | some code => exact ⟨code, rfl⟩
      obtain ⟨ce, hce⟩ := hceSome
      obtain ⟨re, hre, hdiagE⟩ := actualRecord_of_upDiagnosticCodeHistory_some
        rate rewards C_star C_h z e.time ce hce
      have hpos' : recordUpPositiveEntriesFromCode rate
            (upDiagnosticCodeHistory rate rewards C_star C_h z e.time) i =
          ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries re i := by
        change recordUpPositiveEntriesFromDiagnostic rate
          (decodeUpDiagnosticOption rate
            (upDiagnosticCodeHistory rate rewards C_star C_h z e.time)) i = _
        rw [hce]
        rw [hdiagE]
        exact (recordUpPositiveEntries_from_diagnostic rate re i).symm
      have haw' : awaitedUpAt rate re i U := by
        change awaitedUpAtDiagnostic rate
          (decodeUpDiagnosticOption rate
            (upDiagnosticCodeHistory rate rewards C_star C_h z e.time)) i U at haw
        rw [hce, hdiagE] at haw
        change awaitedUpAt rate re i U at haw
        exact haw
      exact ⟨hbirth, htime, heq, re, hre, hpos' ▸ hpos, haw'⟩
    · intro v ha hv hchannel
      have hchannel' : selectedChannelHistory z v = some (1, i) := by
        simpa [selectedChannelHistory, ReferenceSelectedAffinePairLaw.selector,
          ActualInitializationPhysicalStep.selectedRowIndex] using hchannel
      have haw := hchannels v ha hv hchannel'
      have hcvSome : ∃ cv, upDiagnosticCodeHistory rate rewards C_star C_h z v = some cv := by
        cases hc : upDiagnosticCodeHistory rate rewards C_star C_h z v with
        | none =>
            have : False := by
              simp [awaitedUpAtCode, awaitedUpAtDiagnostic,
                decodeUpDiagnosticOption, hc] at haw
            exact this.elim
        | some code => exact ⟨code, rfl⟩
      obtain ⟨cv, hcv⟩ := hcvSome
      obtain ⟨rv, hrv, hdiagV⟩ := actualRecord_of_upDiagnosticCodeHistory_some
        rate rewards C_star C_h z v cv hcv
      have haw' : awaitedUpAt rate rv i U := by
        change awaitedUpAtDiagnostic rate
          (decodeUpDiagnosticOption rate
            (upDiagnosticCodeHistory rate rewards C_star C_h z v)) i U at haw
        rw [hcv, hdiagV] at haw
        exact haw
      exact ⟨rv, hrv, haw'⟩

private theorem measurable_upDiagnosticCodeHistory :
    Measurable (upDiagnosticCodeHistory rate rewards C_star C_h) := by
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

private theorem measurable_selectedChannelHistory (v : Fin p.T) :
    @Measurable (Z (p := p)) (Option (Channel (p := p)))
      (inferInstance : MeasurableSpace (Z (p := p)))
      (ReferenceInitializationMeasurability.optionCountableMeasurableSpace
        (Channel (p := p)))
      (fun z => selectedChannelHistory z v) := by
  let : MeasurableSpace (Option (Channel (p := p))) :=
    ReferenceInitializationMeasurability.optionCountableMeasurableSpace (Channel (p := p))
  let index : Z (p := p) → Fin (ConstructorDimensions.M p) :=
    fun z => ActualInitializationPhysicalStep.selectedRowIndex p z
  have hindex : Measurable index := by
    exact (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  let rows : Z (p := p) → CompletePublicTable.CompleteRows p := fun z => z.1.2
  have hrows : Measurable rows := measurable_snd.comp measurable_fst
  have hrowEval : Measurable (fun z : Z (p := p) => rows z (index z)) := by
    have heval : Measurable
        (fun x : CompletePublicTable.CompleteRows p × Fin (ConstructorDimensions.M p) => x.1 x.2) := by
      apply measurable_from_prod_countable_left
      intro j
      exact measurable_pi_apply j
    exact heval.comp (hrows.prodMk hindex)
  let learningRow : Z (p := p) → ContinuousLearningRows.LearningRow p :=
    fun z => (rows z (index z)).2
  have hlearning : Measurable learningRow :=
    measurable_snd.comp hrowEval
  have htimeEval : Measurable (fun z : Z (p := p) => learningRow z v) := by
    have heval : Measurable
        (fun x : ContinuousLearningRows.LearningRow p × Fin p.T => x.1 x.2) := by
      apply measurable_from_prod_countable_left
      intro t
      exact measurable_pi_apply t
    exact heval.comp (hlearning.prodMk measurable_const)
  have hslice : Measurable (fun z : Z (p := p) => (learningRow z v).1) :=
    measurable_fst.comp htimeEval
  have hselected := (ReferenceSelectedAffinePairLaw.measurable_selectedChannel p).comp hslice
  change @Measurable (Z (p := p)) (Option (Channel (p := p)))
    (inferInstance : MeasurableSpace (Z (p := p)))
    (ReferenceInitializationMeasurability.optionCountableMeasurableSpace
      (Channel (p := p)))
    (fun z : Z (p := p) =>
      ReferenceSelectedAffinePairLaw.selectedChannel p (learningRow z v).1)
  exact hselected

/-- The fixed-time readout is Borel in the original source space. Its code
characterization uses only the canonical diagnostic history, the finite
selected-channel calendar, and countable words and stamped-entry lists. -/
theorem fixedAwaitedUpFailureAt_borel (t : Fin p.T) :
    MeasurableSet {z : Z (p := p) |
      fixedAwaitedUpFailureAt rate rewards C_star C_h z t} := by
  let : MeasurableSpace (Option (UpCode (p := p) (rate := rate))) :=
    ReferenceCollectionServiceTailMeasurability.upDiagnosticOptionMeasurableSpace p rate
  let : MeasurableSpace (Option (Channel (p := p))) :=
    ReferenceInitializationMeasurability.optionCountableMeasurableSpace (Channel (p := p))
  let codeMap : Z (p := p) → ReadoutCodeData (p := p) (rate := rate) := fun z =>
    (upDiagnosticCodeHistory rate rewards C_star C_h z, selectedChannelHistory z)
  have hcodeHistory := measurable_upDiagnosticCodeHistory rate rewards C_star C_h
  have hchannelHistory : Measurable (selectedChannelHistory (p := p)) := by
    apply measurable_pi_iff.mpr
    intro v
    exact measurable_selectedChannelHistory (p := p) v
  have hcodeMap : Measurable codeMap := hcodeHistory.prodMk hchannelHistory
  let : Countable (Fin p.T → Option (UpCode (p := p) (rate := rate))) := inferInstance
  let : Countable (Fin p.T → Option (Channel (p := p))) := inferInstance
  let : MeasurableSingletonClass (Fin p.T → Option (UpCode (p := p) (rate := rate))) :=
    ⟨fun x => by
      have heq : Set.univ.pi (fun v => {x v}) = {x} := by
        ext y
        simp only [Set.mem_pi, Set.mem_univ, Set.mem_singleton_iff]
        constructor
        · intro hy
          funext v
          exact hy v trivial
        · intro h v _
          exact congrFun h v
      rw [← heq]
      exact MeasurableSet.univ_pi (fun v => measurableSet_singleton (x v))⟩
  let : MeasurableSingletonClass (Fin p.T → Option (Channel (p := p))) :=
    ⟨fun x => by
      have heq : Set.univ.pi (fun v => {x v}) = {x} := by
        ext y
        simp only [Set.mem_pi, Set.mem_univ, Set.mem_singleton_iff]
        constructor
        · intro hy
          funext v
          exact hy v trivial
        · intro h v _
          exact congrFun h v
      rw [← heq]
      exact MeasurableSet.univ_pi (fun v => measurableSet_singleton (x v))⟩
  let event : Set (ReadoutCodeData (p := p) (rate := rate)) :=
    {x | fixedAwaitedUpFailureCodeAt rate x.1 x.2 t}
  have hevent : MeasurableSet event := event.to_countable.measurableSet
  have heq : {z : Z (p := p) |
      fixedAwaitedUpFailureAt rate rewards C_star C_h z t} = codeMap ⁻¹' event := by
    ext z
    exact (fixedAwaitedUpFailureAt_iff_code rate rewards C_star C_h z t)
  rw [heq]
  exact hevent.preimage hcodeMap

private theorem actualRecord_input_fields (t : Fin p.T) (z : Z (p := p))
    (r : Record (rate := rate))
    (hr : lookup rate rewards C_star C_h t z = some r) :
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

private theorem actualRecord_roundRecordCode_map_eq_of_prefix
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (v : Fin p.T) (hvn : v.val < n) (z : Z (p := p)) :
    (lookup rate rewards C_star C_h v z).map
        (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) =
      (lookup rate rewards C_star C_h v (ReferenceSourcePrefixHistoryFiltration.sourcePrefix
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
  cases hr : lookup rate rewards C_star C_h v z with
  | none =>
      cases hr' : lookup rate rewards C_star C_h v
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) with
      | none => rfl
      | some r' =>
          have : False := by
            simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr, hr'] at hin
          exact this.elim
  | some r =>
      cases hr' : lookup rate rewards C_star C_h v
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

private theorem upDiagnosticCodeHistory_eq_of_prefix
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (v : Fin p.T) (hvn : v.val < n) (z : Z (p := p)) :
    upDiagnosticCodeHistory rate rewards C_star C_h z v =
      upDiagnosticCodeHistory rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) v := by
  have hround := actualRecord_roundRecordCode_map_eq_of_prefix rate rewards C_star C_h
    control0 n v hvn z
  simp only [upDiagnosticCodeHistory,
    ReferenceInspectedPastRoundObservations.pastRoundObservations,
    Fin.castLE_refl] at hround ⊢
  simpa only [Option.bind_map] using congrArg
    (fun o => o.bind (ReferenceGeneratedUpBatchPrefixEvent.roundRecordUpDiagnosticCode
      (p := p))) hround

private theorem selectedChannelHistory_eq_of_prefix
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (v : Fin p.T) (hvn : v.val < n) (z : Z (p := p)) :
    selectedChannelHistory (p := p) z v = selectedChannelHistory (p := p)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) v := by
  simp [selectedChannelHistory, ReferenceSelectedAffinePairLaw.selector,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, hvn]

private theorem fixedAwaitedUpFailureCodeAt_congr_on_past
    (history history' : Fin p.T → Option (UpCode (p := p) (rate := rate)))
    (channels channels' : Fin p.T → Option (Channel (p := p))) (t : Fin p.T)
    (hcode : ∀ v : Fin p.T, v.val ≤ t.val → history v = history' v)
    (hchannel : ∀ v : Fin p.T, v.val ≤ t.val → channels v = channels' v)
    : fixedAwaitedUpFailureCodeAt rate history channels t ↔
        fixedAwaitedUpFailureCodeAt rate history' channels' t := by
  constructor
  · rintro ⟨i, U, W, a, hbatch, ha, hsigma, hmulti, hentries, hinterval⟩
    refine ⟨i, U, W, a, ?_, ha, hsigma, hmulti, ?_, ?_⟩
    · rw [hcode t (by omega)] at hbatch
      exact hbatch
    · intro e he
      rcases hentries e he with ⟨hbirth, htime, heq, hpos, haw⟩
      have hecode := hcode e.time (by omega)
      exact ⟨hbirth, htime, heq, by simpa only [hecode] using hpos,
        by simpa only [hecode] using haw⟩
    · intro v hb ht hc
      have hc' := hchannel v (by omega)
      have haw := hinterval v hb ht (hc'.trans hc)
      simpa only [hcode v (by omega)] using haw
  · rintro ⟨i, U, W, a, hbatch, ha, hsigma, hmulti, hentries, hinterval⟩
    refine ⟨i, U, W, a, ?_, ha, hsigma, hmulti, ?_, ?_⟩
    · rw [← hcode t (by omega)] at hbatch
      exact hbatch
    · intro e he
      rcases hentries e he with ⟨hbirth, htime, heq, hpos, haw⟩
      have hecode := hcode e.time (by omega)
      exact ⟨hbirth, htime, heq, by simpa only [hecode] using hpos,
        by simpa only [hecode] using haw⟩
    · intro v hb ht hc
      have hc' := hchannel v (by omega)
      have haw := hinterval v hb ht (hc'.symm.trans hc)
      simpa only [hcode v (by omega)] using haw

/-- The strict-past failure event is unchanged by replacing the source suffix
after `n`; the physical lookup and its temporal diagnostic code are retained. -/
private theorem pastUpFailureFlag_factor_lt (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (_hn : n < p.T) (z : Z (p := p)) :
    pastUpFailureFlag rate rewards C_star C_h n z =
      pastUpFailureFlag rate rewards C_star C_h n
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  unfold pastUpFailureFlag
  congr 1
  apply propext
  constructor
  · rintro ⟨t, htn, hfail⟩
    refine ⟨t, htn, ?_⟩
    rw [fixedAwaitedUpFailureAt_iff_code rate rewards C_star C_h]
    rw [fixedAwaitedUpFailureAt_iff_code rate rewards C_star C_h] at hfail
    have hhistory : ∀ v : Fin p.T, v.val ≤ t.val →
        upDiagnosticCodeHistory rate rewards C_star C_h z v =
          upDiagnosticCodeHistory rate rewards C_star C_h
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) v := by
      intro v hv
      exact upDiagnosticCodeHistory_eq_of_prefix rate rewards C_star C_h control0 n v
        (by omega) z
    have hchannels : ∀ v : Fin p.T, v.val ≤ t.val →
        selectedChannelHistory z v = selectedChannelHistory
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) v := by
      intro v hv
      exact selectedChannelHistory_eq_of_prefix control0 n v (by omega) z
    exact (fixedAwaitedUpFailureCodeAt_congr_on_past rate
      (upDiagnosticCodeHistory rate rewards C_star C_h z)
      (upDiagnosticCodeHistory rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z))
      (selectedChannelHistory z)
      (selectedChannelHistory (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z))
      t hhistory hchannels).mp hfail
  · rintro ⟨t, htn, hfail⟩
    refine ⟨t, htn, ?_⟩
    rw [fixedAwaitedUpFailureAt_iff_code rate rewards C_star C_h]
    rw [fixedAwaitedUpFailureAt_iff_code rate rewards C_star C_h] at hfail
    have hhistory : ∀ v : Fin p.T, v.val ≤ t.val →
        upDiagnosticCodeHistory rate rewards C_star C_h z v =
          upDiagnosticCodeHistory rate rewards C_star C_h
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) v := by
      intro v hv
      exact upDiagnosticCodeHistory_eq_of_prefix rate rewards C_star C_h control0 n v
        (by omega) z
    have hchannels : ∀ v : Fin p.T, v.val ≤ t.val →
        selectedChannelHistory z v = selectedChannelHistory
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) v := by
      intro v hv
      exact selectedChannelHistory_eq_of_prefix control0 n v (by omega) z
    exact (fixedAwaitedUpFailureCodeAt_congr_on_past rate
      (upDiagnosticCodeHistory rate rewards C_star C_h z)
      (upDiagnosticCodeHistory rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z))
      (selectedChannelHistory z)
      (selectedChannelHistory (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z))
      t hhistory hchannels).mpr hfail

/-- The strict-past flag factors through the original source prefix. -/
theorem pastUpFailureFlag_factor (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (z : Z (p := p)) :
    pastUpFailureFlag rate rewards C_star C_h n z =
      pastUpFailureFlag rate rewards C_star C_h n
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  by_cases hn : p.T ≤ n
  · rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_eq_self control0 n hn]
  · exact pastUpFailureFlag_factor_lt rate rewards C_star C_h control0 n (by omega) z

theorem pastUpFailureFlag_zero (z : Z (p := p)) :
    pastUpFailureFlag rate rewards C_star C_h 0 z = false := by
  simp [pastUpFailureFlag]

private theorem measurable_pastUpFailureFlag (n : ℕ) :
    Measurable (pastUpFailureFlag rate rewards C_star C_h n) := by
  have htrue : MeasurableSet {z : Z (p := p) |
      pastUpFailureFlag rate rewards C_star C_h n z = true} := by
    change MeasurableSet {z | decide (∃ t : Fin p.T, t.val < n ∧
      fixedAwaitedUpFailureAt rate rewards C_star C_h z t) = true}
    simp only [decide_eq_true_eq]
    have hevent : {z : Z (p := p) | ∃ t : Fin p.T, t.val < n ∧
        fixedAwaitedUpFailureAt rate rewards C_star C_h z t} =
        ⋃ t : Fin p.T, {z : Z (p := p) | t.val < n ∧
          fixedAwaitedUpFailureAt rate rewards C_star C_h z t} := by
      ext z
      simp
    rw [hevent]
    exact MeasurableSet.iUnion fun t => by
      by_cases ht : t.val < n
      · simpa [ht] using fixedAwaitedUpFailureAt_borel rate rewards C_star C_h t
      · simp [ht]
  have hfalse : MeasurableSet {z : Z (p := p) |
      pastUpFailureFlag rate rewards C_star C_h n z = false} := by
    have heq : {z : Z (p := p) |
        pastUpFailureFlag rate rewards C_star C_h n z = false} =
          {z | pastUpFailureFlag rate rewards C_star C_h n z = true}ᶜ := by
      ext z
      cases h : pastUpFailureFlag rate rewards C_star C_h n z <;> simp [h]
    rw [heq]
    exact htrue.compl
  rw [measurable_iff_comap_le]
  intro s hs
  obtain ⟨u, hu, hsu⟩ := MeasurableSpace.measurableSet_comap.mp hs
  rw [← hsu]
  have hpre : (pastUpFailureFlag rate rewards C_star C_h n) ⁻¹' u =
      (if true ∈ u then
        {z : Z (p := p) | pastUpFailureFlag rate rewards C_star C_h n z = true}
        else ∅) ∪
      (if false ∈ u then
        {z : Z (p := p) | pastUpFailureFlag rate rewards C_star C_h n z = false}
        else ∅) := by
    ext z
    cases h : pastUpFailureFlag rate rewards C_star C_h n z <;> simp [h]
  rw [hpre]
  by_cases ht : true ∈ u <;> by_cases hf : false ∈ u
  · simpa [ht, hf] using htrue.union hfalse
  · simpa [ht, hf] using htrue
  · simpa [ht, hf] using hfalse
  · simp [ht, hf]

/-- The readout uses only strict-past physical times and is measurable before
the next source round in the existing prefix filtration. -/
theorem pastUpFailureFlag_adapted (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) :
    Measurable[F control0 (n + 1)] (pastUpFailureFlag rate rewards C_star C_h n) := by
  change Measurable[F control0 (n + 1)]
    (fun z : Z (p := p) => pastUpFailureFlag rate rewards C_star C_h n z)
  have hambient := measurable_pastUpFailureFlag rate rewards C_star C_h n
  have hfactor : (fun z : Z (p := p) => pastUpFailureFlag rate rewards C_star C_h n z) =
      (fun z => pastUpFailureFlag rate rewards C_star C_h n
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)) := by
    funext z
    exact pastUpFailureFlag_factor rate rewards C_star C_h control0 n z
  rw [hfactor]
  unfold F
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  rw [measurable_iff_comap_le]
  have hcomp : (fun z : Z (p := p) => pastUpFailureFlag rate rewards C_star C_h n
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)) =
      pastUpFailureFlag rate rewards C_star C_h n ∘
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n := rfl
  rw [hcomp]
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hambient.comap_le

/-- A detected strict-past failure stays set as the scan is extended. -/
theorem pastUpFailureFlag_mono (z : Z (p := p)) (a b : ℕ) (hab : a ≤ b) :
    pastUpFailureFlag rate rewards C_star C_h a z = true →
      pastUpFailureFlag rate rewards C_star C_h b z = true := by
  simp only [pastUpFailureFlag, decide_eq_true_eq]
  rintro ⟨t, hta, hfailure⟩
  exact ⟨t, lt_of_lt_of_le hta hab, hfailure⟩

/-- Exact diagnostic form of actual completed UP readout. -/
theorem completedUpBatch_eq_some_iff (r : Record (rate := rate)) (i : I (p := p))
    (W : Batch (p := p)) :
    completedUpBatch rate r i = some W ↔
      ∃ d, r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
        CoordinatorUpReception.receptionInputCheck d.input = true ∧
        AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
        Q (p := p) ≤ (appendedUp rate d).length ∧ appendedUp rate d = W := by
  cases h : r.output.coordinator.up with
  | none => simp [completedUpBatch, h]
  | some d =>
      by_cases hc : d.input.selectedFollower = i ∧
          CoordinatorUpReception.receptionInputCheck d.input = true ∧
          AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
          Q (p := p) ≤ (appendedUp rate d).length
      · simp [completedUpBatch, h, hc]
      · constructor
        · simp [completedUpBatch, h, hc]
        · rintro ⟨d', hd', hselected, hcheck, heligible, hthreshold, happended⟩
          have hdd : d = d' := Option.some.inj hd'
          subst d'
          exact (hc ⟨hselected, hcheck, heligible, hthreshold⟩).elim

/-- No retained receiver diagnostic means no completed physical UP batch. -/
theorem completedUpBatch_eq_none_of_no_up (r : Record (rate := rate)) (i : I (p := p))
    (h : r.output.coordinator.up = none) : completedUpBatch rate r i = none := by
  simp [completedUpBatch, h]

/-- A retained diagnostic whose reception input failed is not a completion. -/
theorem completedUpBatch_eq_none_of_input_check_false
    (r : Record (rate := rate)) (i : I (p := p))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d)
    (hcheck : CoordinatorUpReception.receptionInputCheck d.input = false) :
    completedUpBatch rate r i = none := by
  simp [completedUpBatch, hd, hcheck]

/-- An ineligible retained call contributes no completed readout. -/
theorem completedUpBatch_eq_none_of_ineligible
    (r : Record (rate := rate)) (i : I (p := p))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d)
    (hineligible : ¬ AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input)) :
    completedUpBatch rate r i = none := by
  simp [completedUpBatch, hd, hineligible]

/-- A passed retained call below quota remains incomplete. -/
theorem completedUpBatch_eq_none_of_incomplete
    (r : Record (rate := rate)) (i : I (p := p))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d)
    (hcheck : CoordinatorUpReception.receptionInputCheck d.input = true)
    (heligible : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input))
    (hsmall : (appendedUp rate d).length < Q (p := p)) :
    completedUpBatch rate r i = none := by
  by_cases hi : d.input.selectedFollower = i
  · simp [completedUpBatch, hd, hcheck, heligible, hsmall, hi]
  · simp [completedUpBatch, hd, hcheck, heligible, hi]

/-- A completed readout is exactly quota-sized and records the decoder's
actual cleared state and its actual raw output, including raw absence. -/
theorem completedUpBatch_spec (r : Record (rate := rate)) (i : I (p := p))
    (W : Batch (p := p)) (hW : completedUpBatch rate r i = some W) :
    W.length = Q (p := p) ∧ ∃ d, r.output.coordinator.up = some d ∧
      d.input.selectedFollower = i ∧
      d.decoderAfter = ⟨[], (d.input.upDecoderBank i).completed ++ [W]⟩ ∧
      d.raw = AffineBatchDecoder.batchOutput W := by
  rcases (completedUpBatch_eq_some_iff rate r i W).mp hW with
    ⟨d, hd, hselected, hcheck, heligible, hthreshold, happended⟩
  have hfields := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
    r d hd
  obtain ⟨ledger, hsite, hledger, hbank, htime, hobs, hsender, hsample, hslot,
    henabled, hselectedFlag, hroundSample, hroundReward, hfeedback⟩ := hfields
  have hdomain := (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mp hcheck
  obtain ⟨_, _, _, _, _, _, _, hbankWellFormed⟩ :=
    CoordinatorUpReception.receptionInputDomain_parts d.input hdomain
  have hpending := (hbankWellFormed i).1
  have happendedLength : (appendedUp rate d).length =
      (d.input.upDecoderBank i).pending.length + 1 := by
    simp [appendedUp, hselected, CoordinatorUpReception.traceAt,
      AffineBatchDecoder.positiveAt, heligible]
  have hquota : (r.input.state.upDecoderBank i).pending.length + 1 =
      AffineBatchDecoder.quota p := by
    have hupper : (r.input.state.upDecoderBank i).pending.length + 1 ≤
        AffineBatchDecoder.quota p := by
      rw [← hbank]
      exact Nat.succ_le_of_lt hpending
    have hlower : AffineBatchDecoder.quota p ≤
        (r.input.state.upDecoderBank i).pending.length + 1 := by
      simpa only [happendedLength, hbank] using hthreshold
    omega
  have hpositiveEntries :
      ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i ≠ [] := by
    simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd,
      ReferenceCoordinatorUpDecoderReplay.retainedUpFollower, hselected,
      ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
      AffineBatchDecoder.positiveAt, heligible]
  have hpositive :=
    (ReferenceGeneratedUpBatchCalendar.record_up_positive_entries_ne_nil_iff
      r d hd i).mp hpositiveEntries |>.2
  have hcomplete := ReferenceGeneratedUpBatchCalendar.record_up_quota_completion
    r d hd i hselected hpositive hquota
  have hbatch :
      (r.input.state.upDecoderBank i).pending ++
          [AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time] = W := by
    calc
      _ = appendedUp rate d := by
        simp [appendedUp, hbank, hselected, CoordinatorUpReception.traceAt,
          AffineBatchDecoder.positiveAt, heligible]
        rfl
      _ = W := happended
  refine ⟨?_, d, hd, hselected, ?_, ?_⟩
  · rw [← hbatch]
    simp [hquota]
  · simpa [hbank, hbatch] using hcomplete.2.2.1
  · simpa [hbatch] using hcomplete.2.2.2

end Bandits.Support.ReferenceCollectionUpFailureReadoutV2

end
