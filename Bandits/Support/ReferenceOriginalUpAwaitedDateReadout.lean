/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCompositeQuota
public import Bandits.Support.ReferenceLiteralSourceDecoderCoverage

/-!
# Same-date readout of original-source awaited UP ambiguity

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-55,180-240`,
`sources/zip4/manuscript/06_interruptions.tex:110-177,246-296,425-437,459-487`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-108,141-157`.

The source premise retains the entire incoming bank and its detecting entry.
The readout uses the same message and interval, including selected zero reads.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceGeneratedUpBatchPrefixEvent
open Bandits.Support.ReferenceGeneratedUpPrefixPositiveHalf
open Bandits.Support.ReferenceGeneratedUpAwaitedBatchCoverage

namespace Bandits.Support.ReferenceOriginalUpAwaitedDateReadout

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

section SourceCalendar

variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
  (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)
  (i : Fin (p.m - 1))
  (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
    (rate := rate) rewards C_star C_h q t s i)

private theorem source_start :
    ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = s := by
  exact z.property.2.2

/-- Lookup in the actual physical history agrees with the original source run
at every calendar coordinate from launch through the horizon. -/
private theorem source_lookup (v : Fin p.T) (hv : s ≤ v.val) :
    let input := originalSourceRunInput (rate := rate)
      rewards C_star C_h q t s hs control0 i z
    ReferenceCollectionUpFailureReadoutV2.lookup rate rewards C_star C_h v z.val =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt
        input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2
        s (v.val - s) (by omega) input.property) := by
  let input := originalSourceRunInput (rate := rate)
    rewards C_star C_h q t s hs control0 i z
  have hstart := source_start rewards C_star C_h q t s i z
  have hlaunch := originalSourceRunInput_launch (rate := rate)
    rewards C_star C_h q t s hs control0 i z
  have h := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h v z.val input.val.1 hlaunch (by omega)
  simpa only [hstart, input, originalSourceRunInput] using h

/-- Every record in the whole original run is the actual record at its own
physical date. This statement does not truncate at a decoder failure. -/
private theorem source_member_lookup
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : r ∈ (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s)
      (by omega) (originalSourceRunInput (rate := rate)
        rewards C_star C_h q t s hs control0 i z)).records) :
    ReferenceCollectionUpFailureReadoutV2.lookup rate rewards C_star C_h
      r.input.time z.val = some r ∧ s ≤ r.input.time.val := by
  let input := originalSourceRunInput (rate := rate)
    rewards C_star C_h q t s hs control0 i z
  change r ∈ (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 s (p.T - s) (by omega) input.property).records at hr
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hr
  have hj' : j < p.T - s := by
    simpa only [ReferenceActivePhysicalHorizon.run_record_count] using hj
  rw [ReferenceLocalReleaseGateChronology.run_record_at _ _ _ _ _ _ _ _ ⟨j, hj'⟩] at heq
  subst r
  have htime : (ReferenceAssignmentPayloadChronology.actualRunRecordAt
      input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s j
      (by omega) input.property).input.time.val = s + j := rfl
  refine ⟨?_, ?_⟩
  · have hlookup := source_lookup rewards C_star C_h q t s hs control0 i z
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt
        input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s j
        (by omega) input.property).input.time (by change s ≤ s + j; omega)
    simpa only [htime, Nat.add_sub_cancel_left] using hlookup
  · change s ≤ s + j
    omega

/-- Conversely every in-range date has a record in the original whole run. -/
private theorem source_date_member (v : Fin p.T) (hv : s ≤ v.val) :
    ∃ r ∈ (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s)
      (by omega) (originalSourceRunInput (rate := rate)
        rewards C_star C_h q t s hs control0 i z)).records,
      r.input.time = v ∧
      ReferenceCollectionUpFailureReadoutV2.lookup rate rewards C_star C_h v z.val = some r := by
  let input := originalSourceRunInput (rate := rate)
    rewards C_star C_h q t s hs control0 i z
  let full := ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input
  have hj : v.val - s < p.T - s := by have ht := v.isLt; omega
  have hlength : full.records.length = p.T - s :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  let r := full.records[v.val - s]'(by omega)
  have hr : r ∈ full.records := List.getElem_mem (by omega)
  have hrecord : r = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2
      s (v.val - s) (by omega) input.property :=
    ReferenceLocalReleaseGateChronology.run_record_at _ _ _ _ _ _ _ _ ⟨_, hj⟩
  have htime : r.input.time = v := by
    rw [hrecord]
    apply Fin.ext
    change s + (v.val - s) = v.val
    omega
  refine ⟨r, hr, htime, ?_⟩
  rw [← htime]
  exact (source_member_lookup rewards C_star C_h q t s hs control0 i z r hr).1

/-- The event's current record is exactly the original whole-run record at t. -/
private theorem source_current_lookup :
    ReferenceCollectionUpFailureReadoutV2.lookup rate rewards C_star C_h t z.val =
      some (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q t s hs control0 i z) := by
  rw [source_lookup rewards C_star C_h q t s hs control0 i z t hs]
  let mkRecord (x : ReferenceActivePhysicalStep.RoundInput p rate) :
      ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
    ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩
  congr 1
  change mkRecord _ = mkRecord _
  apply congrArg mkRecord
  dsimp only [originalSourceCurrentInput, ReferenceActiveHorizonMeasurability.runOfInput,
    ReferenceActivePhysicalHorizon.roundInputAt]
  congr 1
  apply Fin.ext
  change s + (t.val - s) = t.val
  omega

private theorem source_current_member :
    originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z ∈
      (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
        (originalSourceRunInput (rate := rate)
          rewards C_star C_h q t s hs control0 i z)).records := by
  obtain ⟨r, hr, _, hlookup⟩ := source_date_member
    rewards C_star C_h q t s hs control0 i z t hs
  have hcurrent := source_current_lookup rewards C_star C_h q t s hs control0 i z
  have heq := Option.some.inj (hlookup.symm.trans hcurrent)
  exact heq ▸ hr

end SourceCalendar

/-- Both APIs encode the same four-field UP record with the same codec. -/
private theorem enc_eq_offered
    (M : OrdinaryMessageCodec.UpRecord (CoordinatorCollectionLedger.codecParams p rate.eta)) :
    ReferenceCollectionUpFailureReadoutV2.enc rate M =
      ActiveFollowerArmChoice.offeredUpWord rate.eta M := by
  rfl

private theorem retained_check
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d) :
    CoordinatorUpReception.receptionInputCheck d.input = true := by
  obtain ⟨ledger, _, hcheck, hinput, _⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input r d hd
  rw [hinput]
  exact hcheck

private theorem retained_eligible
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d)
    (hp : ReferenceActiveAffinePositiveTest.upPositive r.input = true) :
    AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) := by
  classical
  rw [ReferenceActiveAffinePositiveTest.record_upPositive r, hd] at hp
  exact of_decide_eq_true hp

/-- The actual retained call supplies the input check, including on zero reads.
The remaining fields are precisely those supplied by the original trace. -/
private theorem awaited_of_trace
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.UpRecord (CoordinatorCollectionLedger.codecParams p rate.eta))
    (hsent : ReferenceActiveAffinePositiveTest.upSent r.input =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta M))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d) (hi : d.input.selectedFollower = i)
    (hselected : (CoordinatorUpReception.roundInput d.input).selected = true)
    (haccept : CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i M = true) :
    ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate r i M := by
  refine ⟨d, hd, hi, retained_check r d hd,
    (CoordinatorUpReception.roundInput_selected_iff_gate d.input).mp hselected, ?_, haccept⟩
  rw [ReferenceSourceRawDecoderDecision.retained_up_sent r d hd, hsent, enc_eq_offered]
  rfl

/-- Ordinary acceptance at an actually reached receiver excludes the placeholder;
no endpoint truth or successful successor is needed. -/
private theorem awaited_sigma_pos
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.UpRecord (CoordinatorCollectionLedger.codecParams p rate.eta))
    (h : ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate r i M) :
    1 ≤ M.val.sigma := by
  obtain ⟨d, _, _, hcheck, _, _, haccept⟩ := h
  have hdomain := (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mp hcheck
  have hpositive := (CoordinatorUpReception.receptionInputDomain_parts d.input hdomain).2.1
  simp only [CoordinatorCollectionLedger.acceptUpCheck, Bool.and_eq_true,
    decide_eq_true_eq] at haccept
  rw [haccept.2.2]
  exact hpositive

/-- Time and sample equality transfer an individual test to its original
positive entry. Length equality by itself would be insufficient. -/
private theorem entry_mem_of_test
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (test : AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p))
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (htest : upTestOfDiagnostic i r.output.coordinator.up = some test)
    (htime : test.time = e.time.val) (hsample : test.sample = e.sample) :
    e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i := by
  classical
  cases hd : r.output.coordinator.up with
  | none => simp only [upTestOfDiagnostic, hd, reduceCtorEq] at htest
  | some d =>
      by_cases hel : d.input.selectedFollower = i ∧
          AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input)
      · have heq : (⟨d.input.time.val, d.input.affineSample, d.expected⟩ :
            AdaptiveAffineBatchTail.Test (AffineBatchDecoder.width p)) = test := by
          simpa only [upTestOfDiagnostic, hd, hel.1, hel.2, and_self, ite_true, Option.some.injEq] using htest
        have het : e.time = d.input.time := by
          apply Fin.ext
          exact (htime.symm.trans (congrArg AdaptiveAffineBatchTail.Test.time heq).symm)
        have hes : e.sample = d.input.affineSample :=
          hsample.symm.trans (congrArg AdaptiveAffineBatchTail.Test.sample heq).symm
        have he : e = AffineBatchDecoder.entry p
            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time := by
          cases e
          simp only [AffineBatchDecoder.entry,
            ReferenceCoordinatorUpDecoderReplay.constantInputTrace, CoordinatorUpReception.roundInput]
          exact congrArg₂ AffineBatchDecoder.Entry.mk het hes
        simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd,
          ReferenceCoordinatorUpDecoderReplay.retainedUpFollower, hel.1, ite_true,
          ReferenceCoordinatorUpDecoderReplay.retainedUpTime, AffineBatchDecoder.positiveAt,
          ReferenceCoordinatorUpDecoderReplay.constantInputTrace, hel.2, List.mem_singleton]
        exact he
      · simp only [upTestOfDiagnostic, hd, hel, ite_false, reduceCtorEq] at htest

/-- Positive physical feedback and the same actual offered word certify the
retained equation, with the original sample and focal follower unchanged. -/
private theorem equation_of_positive_origin
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.UpRecord (CoordinatorCollectionLedger.codecParams p rate.eta))
    (e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (he : e ∈ ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i)
    (hp : ReferenceActiveAffinePositiveTest.upPositive r.input = true)
    (hsent : ReferenceActiveAffinePositiveTest.upSent r.input =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta M))
    (haw : ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate r i M) :
    AffineBatchDecoder.equation e.sample (ReferenceCollectionUpFailureReadoutV2.enc rate M) := by
  obtain ⟨d, hd, hi, _⟩ := haw
  obtain ⟨ledger, _, _, _, _, _, hsender, _⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd
  have hindex : ReferenceActivePhysicalStep.upSenderIndex r.input = i :=
    hsender.symm.trans hi
  have hhash := ReferenceUpPhysicalHashRule.upPositive_hash_one r.input
    (ReferenceCollectionUpFailureReadoutV2.enc rate M) (by rw [enc_eq_offered]; exact hsent) hp
  rw [hindex] at hhash
  apply (AffineBatchDecoder.equation_iff_affineHash _ _).mpr
  rw [(ReferenceLiteralSourceDecoderCoverage.upPositiveEntry_original_coordinates r i e he).2]
  exact hhash

/-- Read original-source awaited ambiguity at its detecting date. The follower,
current record, message, whole bank, and interval are those of the premise.
This is an internal implication, with no additional source-validity premise. -/
theorem fixedAwaitedUpFailureAt_of_originalUpAwaitedAmbiguityAtDate
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (h : ReferenceFirstReplacementCollectionLocalStopSourceTransport.originalUpAwaitedAmbiguityAtDate
        (rate := rate) rewards C_star C_h control0 z i t) :
    ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt
      rate rewards C_star C_h z t := by
  classical
  obtain ⟨q, s, hs, hz, d, hbody⟩ := h
  let zL : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i := ⟨z, hz⟩
  let input := originalSourceRunInput (rate := rate)
    rewards C_star C_h q t s hs control0 i zL
  let full := ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input
  let r := originalSourceCurrentRecord (rate := rate)
    rewards C_star C_h q t s hs control0 i zL
  let W := (r.input.state.upDecoderBank i).pending ++
    [AffineBatchDecoder.entry p
      (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]
  change r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
    ReferenceActiveAffinePositiveTest.upPositive r.input = true ∧
    (r.input.state.upDecoderBank i).pending.length + 1 = AffineBatchDecoder.quota p ∧
    (∃ M beta, awaited_up_source_trace rewards C_star C_h q t s hs control0 i zL beta M ∧
      ∀ e ∈ W, beta ≤ e.time.val) ∧
    ∃ v₁ v₂, v₁ ≠ v₂ ∧
      AffineBatchDecoder.satisfies (W.map AffineBatchDecoder.Entry.sample) v₁ ∧
      AffineBatchDecoder.satisfies (W.map AffineBatchDecoder.Entry.sample) v₂ at hbody
  obtain ⟨hd, hi, hp, hQ, ⟨M, beta, htrace, hbeta⟩, v₁, v₂, hne, hv₁, hv₂⟩ := hbody
  obtain ⟨hsbeta, hbetat, htrace⟩ := htrace
  let a : Fin p.T := ⟨beta, lt_of_le_of_lt hbetat t.isLt⟩
  have hrlookup := source_current_lookup rewards C_star C_h q t s hs control0 i zL
  have hrmem : r ∈ full.records :=
    source_current_member rewards C_star C_h q t s hs control0 i zL
  have hfields := ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
    rate rewards C_star C_h z t r hrlookup
  obtain ⟨hrows, hselected, htime, _⟩ := hfields
  have hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p
      (r.input.row.2 r.input.time).1 = some (1, i) := by
    change ReferenceSelectedAffinePairLaw.selectedChannel p
      ((r.input.rows r.input.selected).2 r.input.time).1 = some (1, i)
    rw [hrows, hselected, htime]
    exact congrArg Prod.snd hz.1
  -- This dictionary retains EVERY selected date, without a positivity condition.
  have hawaited : ∀ rv ∈ full.records,
      beta ≤ rv.input.time.val → rv.input.time.val ≤ t.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p (rv.input.row.2 rv.input.time).1 =
        some (1, i) →
      ReferenceActiveAffinePositiveTest.upSent rv.input =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) ∧
      ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate rv i M := by
    intro rv hrv hb ht hc
    obtain ⟨hsent, diagnostic, hdiagnostic, hsender, hsel, _, haccept⟩ :=
      htrace rv hrv hb ht hc
    exact ⟨hsent, awaited_of_trace rv i M hsent diagnostic hdiagnostic hsender hsel haccept⟩
  have hcurrentAwaited := (hawaited r hrmem (by rw [htime]; exact hbetat)
    (by rw [htime]) hchannel).2
  have hsigma := awaited_sigma_pos r i M hcurrentAwaited
  have hcheck := retained_check r d hd
  have hel := retained_eligible r d hd hp
  obtain ⟨ledger, _, _, hbank, _⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd
  have happended : ReferenceCollectionUpFailureReadoutV2.appendedUp rate d = W := by
    simp only [ReferenceCollectionUpFailureReadoutV2.appendedUp, hi, hbank,
      AffineBatchDecoder.positiveAt, CoordinatorUpReception.traceAt, hel, ite_true]
    rfl
  have hlength : W.length = AffineBatchDecoder.quota p := by
    change ((r.input.state.upDecoderBank i).pending ++ [_]).length = _
    simpa only [List.length_append, List.length_singleton] using hQ
  have hcompleted : ReferenceCollectionUpFailureReadoutV2.completedUpBatch rate r i = some W :=
    (ReferenceCollectionUpFailureReadoutV2.completedUpBatch_eq_some_iff rate r i W).mpr
      ⟨d, hd, hi, hcheck, hel, by rw [happended, hlength], happended⟩
  have hmultiple : ReferenceFirstLiveDownCompletionReadout.multipleSolutions W :=
    (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff W).mpr
      ⟨v₁, v₂, hv₁, hv₂, hne⟩
  -- The candidate producer reconstructs ALL incoming entries, including inherited
  -- entries. We use its time/sample equality separately for each original e.
  obtain ⟨alpha, _, _, _, _, _, hcoordinates, horigins, _⟩ :=
    actual_completed_up_candidates rewards C_star C_h q t s hs control0 i zL d hd hi hp hQ
  refine ⟨r, i, M, W, a, hrlookup, hcompleted, hbetat, hsigma, hmultiple, ?_, ?_⟩
  · intro e he
    have hcoordmem : (e.time.val, e.sample) ∈
        (ReferenceGeneratedUpSourceCalendar.originalSourceTests (rate := rate) rewards C_star C_h q t s hs control0 alpha i zL
          |>.take (AffineBatchDecoder.quota p)).map (fun test => (test.time, test.sample)) := by
      rw [hcoordinates]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    obtain ⟨test, htest, hcoord⟩ := List.mem_map.mp hcoordmem
    have htesttime : test.time = e.time.val := congrArg Prod.fst hcoord
    have htestsample : test.sample = e.sample := congrArg Prod.snd hcoord
    obtain ⟨re, hremem, htestorigin, htestdate, _, _, hpositive, hselectedOrigin, hupper⟩ :=
      horigins test htest
    have hepositive := entry_mem_of_test re i test e htestorigin htesttime htestsample
    have hedate : e.time = re.input.time := by
      apply Fin.ext
      exact htesttime.symm.trans htestdate
    have hbl : beta ≤ re.input.time.val := by rw [← hedate]; exact hbeta e he
    obtain ⟨hsent, haw⟩ := hawaited re hremem hbl hupper hselectedOrigin
    have hlookup := (source_member_lookup
      rewards C_star C_h q t s hs control0 i zL re hremem).1
    refine ⟨hbeta e he, ?_, equation_of_positive_origin re i M e hepositive hpositive hsent haw,
      re, ?_, hepositive, haw⟩
    · rw [hedate]
      exact hupper
    · rw [hedate]
      exact hlookup
  · intro v hb ht hc
    have hsv : s ≤ v.val := le_trans hsbeta hb
    obtain ⟨rv, hrv, hvdate, hvlookup⟩ :=
      source_date_member rewards C_star C_h q t s hs control0 i zL v hsv
    have hrvfields := ReferenceLiteralSourceDecoderCoverage.actualRecord_original_fields
      rate rewards C_star C_h z v rv hvlookup
    have hrvchannel : ReferenceSelectedAffinePairLaw.selectedChannel p
        (rv.input.row.2 rv.input.time).1 = some (1, i) := by
      change ReferenceSelectedAffinePairLaw.selectedChannel p
        ((rv.input.rows rv.input.selected).2 rv.input.time).1 = some (1, i)
      rw [hrvfields.1, hrvfields.2.1, hvdate]
      exact hc
    exact ⟨rv, hvlookup, (hawaited rv hrv (by rw [hvdate]; exact hb)
      (by rw [hvdate]; exact ht) hrvchannel).2⟩

/-- The same original event also gives the accepted literal physical readout
at the very same date, with its original witness coordinates preserved. -/
theorem literalUpAmbiguityAt_of_originalUpAwaitedAmbiguityAtDate
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (h : ReferenceFirstReplacementCollectionLocalStopSourceTransport.originalUpAwaitedAmbiguityAtDate
        (rate := rate) rewards C_star C_h control0 z i t) :
    ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt rate rewards C_star C_h z t := by
  exact ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt_of_fixedAwaitedUpFailureAt
    rate rewards C_star C_h z t
    (fixedAwaitedUpFailureAt_of_originalUpAwaitedAmbiguityAtDate
      rate rewards C_star C_h control0 z i t h)

end Bandits.Support.ReferenceOriginalUpAwaitedDateReadout
