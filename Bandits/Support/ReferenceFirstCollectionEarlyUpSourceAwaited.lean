/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionEarlyUpWindowAcceptance
public import Bandits.Support.ReferenceGeneratedUpAwaitedAmbiguityTail

/-!
# Early second UP windows on the original source

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-53`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,246-295,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`.

The fixed early reply is chosen before the prefix and disintegration queries.
The saved second window retains the actual incoming bank and completed history.
Original-source restoration uses the entire original table and private index.
Awaitedness includes every selected calendar round, including zero observations.
All count, ordinary-endpoint and ambiguity conditions remain explicit. No
service attainment, probability bound, numerical authenticity or manuscript
closure is asserted here.
-/

@[expose] public section

noncomputable section
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionEarlyUpSourceAwaited

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem prefix_records
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s total : ℕ) (hspan : s + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (n : ℕ) (hn : n ≤ total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards s total hspan active).records.take n =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards s n (by omega) active).records := by
  obtain ⟨suffix, heq⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards s n (total - n) (by omega) active
  have hcount : n + (total - n) = total := Nat.add_sub_of_le hn
  simp only [hcount] at heq
  rw [heq, List.take_append_of_le_length (by
    rw [ReferenceActivePhysicalHorizon.run_record_count])]
  apply List.take_of_length_le
  rw [ReferenceActivePhysicalHorizon.run_record_count]

private theorem record_time_index
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s total : ℕ) (hspan : s + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (k : ℕ) (hk : k < (ReferenceActivePhysicalHorizon.run
      initial rows selected rewards s total hspan active).records.length) :
    ((ReferenceActivePhysicalHorizon.run initial rows selected rewards s total hspan active).records[k]).input.time.val =
      s + k := by
  have ht := ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards s total hspan active
  have hget := congrArg (fun xs : List ℕ => xs[k]?) ht
  have hkt : k < total := by
    rw [ReferenceActivePhysicalHorizon.run_record_count] at hk
    exact hk
  simpa only [List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some,
    ReferenceActivePhysicalHorizon.calendar, List.getElem?_range', hkt,
    decide_true, ite_true, Nat.one_mul, Option.some.injEq] using hget

private theorem selected_up_fields
    (slice : ContinuousLearningRows.Slice p)
    (i : Fin (p.m - 1))
    (h : ReferenceSelectedAffinePairLaw.selectedChannel p slice = some (1, i)) :
    PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.upSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K slice = i := by
  classical
  unfold ReferenceSelectedAffinePairLaw.selectedChannel
    ReferenceSelectedAffinePairLaw.channelFromDraws at h
  split_ifs at h with hd hu
  · have hdirection := congrArg Prod.fst (Option.some.inj h)
    exact (zero_ne_one hdirection).elim
  · exact ⟨hu, (Prod.mk.inj (Option.some.inj h)).2⟩

private theorem source_run_input_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch (rate := rate)
      rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source) t (1, i) s)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross) s) :
    ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput (rate := rate)
      rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source)
        t s hs control0 i ⟨source, hz⟩ =
      ⟨(ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross,
        source.1.2, ActualInitializationPhysicalStep.selectedRowIndex p source, rewards), active⟩ := by
  have hlaunch := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput_launch (rate := rate)
    rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source)
      t s hs control0 i ⟨source, hz⟩
  have hseed : (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput (rate := rate)
      rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source)
        t s hs control0 i ⟨source, hz⟩).val.1 =
      ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross := by
    unfold ReferenceFirstCollectionEpochAlignment.actualLaunchState
    exact (Option.get_of_eq_some
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).2 hcross) hlaunch).symm
  apply Subtype.ext
  exact Prod.ext hseed rfl

private theorem original_current_mem
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource (rate := rate)
      rewards C_star C_h q t s i) :
    ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z ∈
      (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput (rate := rate)
          rewards C_star C_h q t s hs control0 i z)).records := by
  let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput (rate := rate)
    rewards C_star C_h q t s hs control0 i z
  have ht := prefix_records input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2
    s (p.T - s) (by omega) input.property (t.val - s + 1) (by omega)
  have hsplit : (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s + 1)
      (by omega) input).records =
      (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input).records ++
        [ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord (rate := rate)
          rewards C_star C_h q t s hs control0 i z] := by
    dsimp only [ReferenceActiveHorizonMeasurability.runOfInput]
    rw [ReferenceActivePhysicalHorizon.run_successor_step]
    have he : (⟨s + (t.val - s), by omega, by omega⟩ :
        ReferenceActivePhysicalHorizon.CalendarEntry p s) = ⟨t.val, hs, t.isLt⟩ :=
      Subtype.ext (Nat.add_sub_of_le hs)
    rw [he]
    rfl
  apply List.mem_of_mem_take (i := t.val - s + 1)
  change _ ∈ (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input).records.take _
  change (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input).records.take _ =
    (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s + 1) (by omega) input).records at ht
  rw [ht, hsplit]
  exact List.mem_append_right _ List.mem_cons_self

private theorem current_record_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (t : Fin p.T) (s total : ℕ) (hs : s ≤ t.val) (hspan : s + total ≤ p.T)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch (rate := rate)
      rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source) t (1, i) s)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross) s)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : record ∈ (ReferenceActivePhysicalHorizon.run
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s total hspan active).records)
    (htime : record.input.time = t) :
    ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source)
        t s hs control0 i ⟨source, hz⟩ = record := by
  let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross
  let rows := source.1.2
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  have hinput := source_run_input_eq rate source rewards C_star C_h hcross t s hs control0 i hz active
  have hcurrent := original_current_mem rewards C_star C_h J t s hs control0 i ⟨source, hz⟩
  rw [hinput] at hcurrent
  have hprefix := prefix_records I rows J rewards s (p.T - s) (by omega) active total (by omega)
  have hrecordFull : record ∈ (ReferenceActivePhysicalHorizon.run I rows J rewards s
      (p.T - s) (by omega) active).records := by
    apply List.mem_of_mem_take (i := total)
    rw [hprefix]
    exact hmem
  apply ReferenceAssignmentPayloadChronology.run_records_time_injective I rows J rewards
    s (p.T - s) (by omega) active hcurrent hrecordFull
  exact (congrArg Fin.val
    (ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentInput_original_fields
      (rate := rate) rewards C_star C_h J t s hs control0 i ⟨source, hz⟩).2.2.1).trans
        (congrArg Fin.val htime).symm

private theorem record_mem_interval_of_bounds
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s total a b : ℕ) (hspan : s + total ≤ p.T) (hb : b ≤ total)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards s total hspan active).records)
    (hlower : s + a ≤ record.input.time.val) (hupper : record.input.time.val < s + b) :
    record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards s b (by omega) active).records.drop a := by
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards s total hspan active
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
  have htime := record_time_index initial rows selected rewards s total hspan active k hk
  rw [hget] at htime
  have hak : a ≤ k := by omega
  have hkb : k < b := by omega
  have hprefix := prefix_records initial rows selected rewards s total hspan active b hb
  rw [← hprefix, List.drop_take]
  apply List.mem_iff_getElem.mpr
  have hbound : k - a < ((full.records.drop a).take (b - a)).length := by
    have hlen : full.records.length = total :=
      ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards s total hspan active
    simp only [List.length_take, List.length_drop, hlen]
    omega
  refine ⟨k - a, hbound, ?_⟩
  simpa only [List.getElem_take, List.getElem_drop, Nat.add_sub_of_le hak] using hget

private theorem eligible_call_fields
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate) (i : Fin (p.m - 1))
    (hd : record.output.coordinator.up = some d) (hi : d.input.selectedFollower = i)
    (heligible : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input)) :
    ReferenceSelectedAffinePairLaw.selectedChannel p (record.input.row.2 record.input.time).1 = some (1, i) ∧
      ReferenceActiveAffinePositiveTest.upPositive record.input = true := by
  classical
  obtain ⟨ledger, _hsite, _hledger, _hbank, _htime, _hobs, hindex,
    _hsample, hslot, _henabled, hgate, _hroundSample, _hreward, _hfeedback⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields record d hd
  have hs := heligible.1
  rw [hgate] at hs
  have hslotUp : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
      PublicDiscreteDraws.upSlot := hslot.symm.trans (of_decide_eq_true hs).2.1
  have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i := hindex.symm.trans hi
  constructor
  · rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _ hslotUp, hdraw]
    rfl
  · rw [ReferenceActiveAffinePositiveTest.record_upPositive, hd]
    exact decide_eq_true heligible

private theorem accepted_prefix_not_mem
    (B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (h k : ℕ) (hh : h ≤ k)
    (hnot : i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (B.take k)).toFinset) :
    i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (B.take h)).toFinset := by
  intro hmem
  apply hnot
  rw [List.mem_toFinset] at hmem ⊢
  obtain ⟨record, hr, he⟩ := List.mem_filterMap.mp hmem
  exact List.mem_filterMap.mpr ⟨record, (List.take_prefix_take_left hh).subset hr, he⟩

/-- Conditional finite-prefix gate lemma. Its sender and receiver inputs are
literal per-record fields, produced from the public physical root below. -/
private theorem selected_prefix_gates
    (initial final : ReferenceActivePhysicalStep.State p rate)
    (records B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (n : ℕ) (hn : n ≤ B.length) (hrecords : records = B.take n)
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : Fin (p.m - 1)) (endpoint : ReferencePrelaunchFollower.State p rate.eta)
    (endpointMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hEndpoint : final.followers i = .ordinary endpoint endpointMemory)
    (hOrd : ∀ r ∈ records, r.output.next.coordinator ≠ .dagger)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (k : ℕ) (hk : k < n)
    (hnot : i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (B.take k)).toFinset)
    (hchoices : ∀ a : Fin B.length,
      (ReferenceFollowerFixedReply.actualChoice B[a.val] i).configuration = .dagger ∨
      ∃ choice memory,
        (ReferenceFollowerFixedReply.actualChoice B[a.val] i).configuration = .ordinary choice memory ∧
        ∀ (_hs : PublicDiscreteDraws.slotDraw (B[a.val].input.row.2 B[a.val].input.time).1 = PublicDiscreteDraws.upSlot)
          (_hi : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (B[a.val].input.row.2 B[a.val].input.time).1 = i),
          ReferenceActiveAffinePositiveTest.upSent B[a.val].input =
            some (ActiveFollowerArmChoice.offeredUpWord rate.eta U))
    (hreceivers : ∀ a : Fin B.length, B[a.val].output.next.coordinator ≠ .dagger →
      ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
        B[a.val].output.coordinator.up = some d ∧
        ∀ (_hs : PublicDiscreteDraws.slotDraw (B[a.val].input.row.2 B[a.val].input.time).1 = PublicDiscreteDraws.upSlot)
          (_hi : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (B[a.val].input.row.2 B[a.val].input.time).1 = i),
          i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (B.take a.val)).toFinset →
          d.input.selectedFollower = i ∧ (CoordinatorUpReception.roundInput d.input).selected = true ∧
          (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
          CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i U = true) :
    ∀ a : Fin B.length, a.val ≤ k →
      ReferenceSelectedAffinePairLaw.selectedChannel p (B[a.val].input.row.2 B[a.val].input.time).1 = some (1, i) →
      ReferenceActiveAffinePositiveTest.upSent B[a.val].input = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
      ∃ d, B[a.val].output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
        (CoordinatorUpReception.roundInput d.input).selected = true ∧
        (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
        CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i U = true := by
  intro a ha hchannel
  obtain ⟨hslot, hdraw⟩ := selected_up_fields _ i hchannel
  have haN : a.val < n := lt_of_le_of_lt ha hk
  have hmem : B[a.val] ∈ records := by
    rw [hrecords]
    have hb : a.val < (B.take n).length := by rw [List.length_take, Nat.min_eq_left hn]; exact haN
    have hget : (B.take n)[a.val]'hb = B[a.val] := List.getElem_take
    rw [← hget]
    exact List.getElem_mem hb
  obtain ⟨q, hq, hget⟩ := List.mem_iff_getElem.mp hmem
  obtain ⟨next, nextMemory, hnext, _⟩ := ReferenceFollowerReplyChronology.connected_output_chronology
    chain i endpoint endpointMemory hEndpoint q hq
  rw [hget] at hnext
  obtain ⟨choice, choiceMemory, hc, _⟩ :=
    ReferenceFollowerReplyChronology.record_choice_chronology B[a.val] i next nextMemory hnext
  have hsent : ReferenceActiveAffinePositiveTest.upSent B[a.val].input =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
    rcases hchoices a with hd | ⟨_choice, _memory, _hc, hsender⟩
    · cases hd.symm.trans hc
    · exact hsender hslot hdraw
  obtain ⟨d, hd, hgates⟩ := hreceivers a (hOrd B[a.val] hmem)
  exact ⟨hsent, d, hd, hgates hslot hdraw (accepted_prefix_not_mem B i a.val k ha hnot)⟩

private theorem original_source_trace_of_gates
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsLaunch : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s)
    (w n : ℕ) (hspan : s + (w + n) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross) s)
    (B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hn : n ≤ B.length) (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (t : Fin p.T)
    (hmem : record ∈ (ReferenceActivePhysicalHorizon.run
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s (w + n) hspan active).records.drop w)
    (htime : record.input.time = t) (hlower : s + w ≤ t.val) (hupper : t.val < s + (w + n))
    (hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p
      ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t).1 = some (1, i))
    (hinterval : (ReferenceActivePhysicalHorizon.run
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s (w + n) hspan active).records.drop w = B.take n)
    (hBtime : ∀ a : Fin B.length, B[a.val].input.time.val = s + w + a.val)
    (k : ℕ) (hkTime : t.val = s + w + k)
    (hgates : ∀ a : Fin B.length, a.val ≤ k →
      ReferenceSelectedAffinePairLaw.selectedChannel p (B[a.val].input.row.2 B[a.val].input.time).1 = some (1, i) →
      ReferenceActiveAffinePositiveTest.upSent B[a.val].input = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
      ∃ d, B[a.val].output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
        (CoordinatorUpReception.roundInput d.input).selected = true ∧
        (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
        CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i U = true) :
    ∀ control0 : ContinuousLearningRows.TimeControl p,
      ∃ (hs : s ≤ t.val)
        (hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch (rate := rate)
          rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source) t (1, i) s),
      let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource (rate := rate)
        rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source) t s i := ⟨source, hz⟩
      ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source) t s hs control0 i z = record ∧
      ReferenceGeneratedUpAwaitedBatchCoverage.awaited_up_source_trace rewards C_star C_h
        (ActualInitializationPhysicalStep.selectedRowIndex p source) t s hs control0 i z (s + w) U := by
  intro control0
  have hs : s ≤ t.val := by omega
  have hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch (rate := rate)
      rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source) t (1, i) s :=
    ⟨Prod.ext rfl hchannel, hcross, hsLaunch⟩
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross
  let rows := source.1.2
  let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource (rate := rate)
    rewards C_star C_h J t s i := ⟨source, hz⟩
  refine ⟨hs, hz, current_record_eq rate source rewards C_star C_h hcross t s (w + n)
    hs hspan control0 i hz active record (List.mem_of_mem_drop hmem) htime, ?_⟩
  refine ⟨Nat.le_add_right s w, hlower, ?_⟩
  intro r hr hl hu hselected
  have hrunInput := source_run_input_eq rate source rewards C_star C_h hcross t s hs control0 i hz active
  change r ∈ (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
    (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput (rate := rate)
      rewards C_star C_h J t s hs control0 i z)).records at hr
  rw [hrunInput] at hr
  have hrInterval := record_mem_interval_of_bounds I rows J rewards s (p.T - s) w (w + n)
    (by omega) (by omega) active r hr hl (by omega)
  have hrTake : r ∈ B.take n := by rw [← hinterval]; exact hrInterval
  obtain ⟨aVal, haVal, hget⟩ := List.mem_iff_getElem.mp hrTake
  have haN : aVal < n := lt_of_lt_of_le haVal (List.length_take_le _ _)
  let a : Fin B.length := ⟨aVal, haN.trans_le hn⟩
  have hBa : B[a.val] = r := by simpa only [List.getElem_take] using hget
  have haTime := hBtime a
  rw [hBa] at haTime
  have haK : a.val ≤ k := by omega
  have hf := hgates a haK
  rw [hBa] at hf
  exact hf hselected

/-- Conditional identification of the public early sender/receiver witnesses.
The cut, pre-cut follower and reply inputs are literal equalities supplied by
E. The conclusion retains the two exceptional alternatives. -/
private theorem early_gate_inputs
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (_hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let Erun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
    ∀ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      (∃ hindex : w < Erun.records.length, cut = Erun.records[w]'hindex) →
      ∀ (i : Fin (p.m - 1)) (j : Fin Erun.records.length)
        (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
      j.val < w → ReferenceAcceptedUpFollowerHistory.RetainedDown Erun.records[j.val] i M →
      ∀ (before : ReferencePrelaunchFollower.State p rate.eta) (memory : ActiveFollowerLifecycle.LocalMemory p)
        (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
      cut.input.state.followers i = .ordinary before memory →
      U.val = OrdinaryMessageCodec.UpFields.mk (s + 1) before.S before.delta before.backlog →
      cut.output.next.coordinator = .dagger ∨ cut.output.next.followers i = .dagger ∨
      (∀ a : Fin B.length,
      (ReferenceFollowerFixedReply.actualChoice B[a.val] i).configuration = .dagger ∨
      ∃ choice memory,
        (ReferenceFollowerFixedReply.actualChoice B[a.val] i).configuration = .ordinary choice memory ∧
        ∀ (_hs : PublicDiscreteDraws.slotDraw (B[a.val].input.row.2 B[a.val].input.time).1 = PublicDiscreteDraws.upSlot)
          (_hi : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (B[a.val].input.row.2 B[a.val].input.time).1 = i),
          ReferenceActiveAffinePositiveTest.upSent B[a.val].input =
            some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
      (∀ a : Fin B.length, B[a.val].output.next.coordinator ≠ .dagger →
      ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
        B[a.val].output.coordinator.up = some d ∧
        ∀ (_hs : PublicDiscreteDraws.slotDraw (B[a.val].input.row.2 B[a.val].input.time).1 = PublicDiscreteDraws.upSlot)
          (_hi : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (B[a.val].input.row.2 B[a.val].input.time).1 = i),
          i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (B.take a.val)).toFinset →
          d.input.selectedFollower = i ∧ (CoordinatorUpReception.roundInput d.input).selected = true ∧
          (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
          CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i U = true) := by
  classical
  intro s Erun w B cut hcutIndex i j M hj hretained before memory U hbefore hUfields
  have hSR := ReferenceFirstCollectionEarlyUpSenderReceiver.actual_first_collection_early_up_sender_receiver
    rate source rewards C_star C_h count hcross hspan _hshort
  rcases hSR with ⟨cut₂, _suffix₂, _registers₂, _owned₂, _base₂, _P₂, _birth₂,
    _hsplit₂, _hconnected₂, hcutIndex₂, _hcutTime₂, _hcutState₂, _hcutoff₂, _hpayload₂,
    _hsigma₂, _hqueues₂, _hfirstCutoff₂, _hbirthMem₂, _hbirthInstall₂, _hbirthTime₂,
    _hbirthFirst₂, _hrecords₂, _hb, _hBsplit₂, _hwindowEnd, _hWearlyBound,
    _hphysicalEnd, _hterminal, _hEarly, _hwindow₂, _hdispatch, _hcoordNext₂, hqueries₂⟩
  have hcutEq : cut₂ = cut := by
    obtain ⟨_hindex, hget⟩ := hcutIndex
    obtain ⟨_hindex₂, hget₂⟩ := hcutIndex₂
    exact hget₂.trans hget.symm
  rw [hcutEq] at hqueries₂
  rcases hqueries₂ i j M hj hretained with
    ⟨before₂, _memory₂, _token₂, U₂, hbefore₂, _hlast₂, _hMpayload₂, _hoccupied₂,
      _hstart₂, _hMstart₂, _hdomain₂, _htoken₂, _htokenTime₂, _htokenBit₂, _hstartRound₂,
      _hcutChoice₂, hUfields₂, _hUpositive₂, _hcutSender₂, _hcutFollower₂, _hcutNoDown₂,
      hcutCollection⟩
  have hbeforeEq : before₂ = before :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hbefore₂.symm.trans hbefore)).1
  have hUEq : U₂ = U := Subtype.ext (hUfields₂.trans (by rw [hbeforeEq]; exact hUfields.symm))
  rw [hUEq] at hcutCollection
  rcases hcutCollection with hd | ⟨_nextLedger, _nextSaved, _hcutCollection, hcutFollowers⟩
  · exact Or.inl hd
  rcases hcutFollowers with hd | ⟨_out, _outMemory, _hout, _houtStatus, _houtReply, _hlastOut, _hstartOut,
    _hprefixStart, _hnextSigma, _hnextPending, _hmovement, hBqueries⟩
  · exact Or.inr (Or.inl hd)
  refine Or.inr (Or.inr ⟨?_, ?_⟩)
  · intro a
    rcases (hBqueries a).1 with hd | ⟨choice, mem, hc, _hs, _hr, _hoffer, hsender⟩
    · exact Or.inl hd
    · exact Or.inr ⟨choice, mem, hc, fun hs hi => (hsender hs hi).2.2.1⟩
  · intro a hrecordOrd
    obtain ⟨_tail, _recording, ledger, d, _receivedLedger, _bank, _finished, _clockFinished,
      _htail, _htailPending, _htailSigma, _hsite, _hrecording, _hstart, _hcheck, hinputD, hup,
      _htailReception, _hnotInvalid, _hreceiveAlternatives, _hfinish, _hclock, _hdecoder, _hraw,
      _hparsed, _hlocal, _hexpected, _hrawMatches, _hbank, _htime, _hsample,
      _hobservation, _hwrong, _hLpending, _hLsigma, _hcursorLower, _hcursor, _hcutFields, hlocalQueries⟩ :=
      (hBqueries a).2.1 hrecordOrd
    refine ⟨d, hup, ?_⟩
    intro hs hi hnotEarlier
    obtain ⟨hi, _hgate, hs, he, haccept, _hzero⟩ := (hlocalQueries hs hi).1 hnotEarlier
    have hledgerD : d.input.ledger = ledger := by rw [hinputD]; rfl
    exact ⟨hi, hs, he, by rw [hledgerD]; exact haccept⟩

private theorem positive_time_le_decision
    (trace : AffineBatchDecoder.Trace p) (rounds : List (Fin p.T))
    (hchron : rounds.Pairwise (fun a b => a.val < b.val))
    (skip : ℕ) (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hdecision : AffineBatchDecoder.decisionTime
      ((AffineBatchDecoder.positives p trace rounds).drop skip) = some last.time)
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hentry : entry ∈ AffineBatchDecoder.positives p trace rounds) :
    entry.time.val ≤ last.time.val := by
  classical
  let positive := AffineBatchDecoder.positives p trace rounds
  have hlt : skip < positive.length := by
    by_contra h
    have hnil : positive.drop skip = [] := List.drop_eq_nil_iff.mpr (Nat.le_of_not_gt h)
    change AffineBatchDecoder.decisionTime (positive.drop skip) = some last.time at hdecision
    simp only [hnil, AffineBatchDecoder.decisionTime, List.map_nil, List.getLast?_nil] at hdecision
    cases hdecision
  have hpairs : positive.Pairwise (fun a b => a.time.val ≤ b.time.val) := by
    apply List.Pairwise.imp (fun h => Nat.le_of_lt h)
    change ((rounds.filter (fun t => decide (AffineBatchDecoder.eligible (trace t)))).map
      (AffineBatchDecoder.entry p trace)).Pairwise (fun a b => a.time.val < b.time.val)
    exact List.pairwise_map.mpr (hchron.filter _)
  have hne : positive ≠ [] := List.ne_nil_of_mem hentry
  have hlast : (positive.getLast hne).time = last.time := by
    change ((positive.drop skip).map AffineBatchDecoder.Entry.time).getLast? = some last.time at hdecision
    rw [List.getLast?_map, List.getLast?_drop, ite_eq_right (Nat.not_le.mpr hlt)] at hdecision
    simpa only [List.getLast?_eq_some_getLast hne, Option.map_some, Option.some.injEq] using hdecision
  have hmax := hpairs.rel_getLast_of_rel_getLast_getLast hentry (Nat.le_refl _)
  simpa only [hlast] using hmax

/-- A positive focal final calendar record is the saved last positive record.
The decision and chronology inputs are produced by E and the actual calendar. -/
private theorem saved_record_eq_endpoint
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s a n : ℕ) (hspan : s + (a + n) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (i : Fin (p.m - 1)) (hn : 0 < n)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) (skip : ℕ)
    (hmem : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards s (a + n) hspan active).records.drop a)
    (htime : record.input.time = last.time)
    (hchron : ((ReferenceActivePhysicalHorizon.run initial rows selected rewards s (a + n) hspan active).records.drop a).Pairwise
      (fun r r' => r.input.time.val < r'.input.time.val))
    (hdecision : AffineBatchDecoder.decisionTime
      ((AffineBatchDecoder.positives p
        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
          ((ReferenceActivePhysicalHorizon.run initial rows selected rewards s (a + n) hspan active).records.drop a) i)
        (((ReferenceActivePhysicalHorizon.run initial rows selected rewards s (a + n) hspan active).records.drop a).map
          fun r => r.input.time)).drop skip) = some last.time) :
    let Cn := ReferenceActivePhysicalHorizon.run initial rows selected rewards s (a + n) hspan active
    ∃ hend : a + n - 1 < Cn.records.length,
      let ending := Cn.records[a + n - 1]'hend
      ReferenceSelectedAffinePairLaw.selectedChannel p ((rows selected).2 ending.input.time).1 = some (1, i) →
      ReferenceActiveAffinePositiveTest.upPositive ending.input = true → record = ending := by
  classical
  intro Cn
  have hend : a + n - 1 < Cn.records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    omega
  refine ⟨hend, ?_⟩
  intro ending hchannel hpositive
  have heMem : ending ∈ Cn.records := List.getElem_mem hend
  have heTime := record_time_index initial rows selected rewards s (a + n) hspan active (a + n - 1) hend
  change ending.input.time.val = s + (a + n - 1) at heTime
  have heInt := record_mem_interval_of_bounds initial rows selected rewards s (a + n) a (a + n)
    hspan le_rfl active ending heMem (by omega) (by omega)
  have hfields := ReferenceActivePhysicalHorizon.run_record_inputs initial rows selected rewards
    s (a + n) hspan active ending heMem
  have hchannelActual : ReferenceSelectedAffinePairLaw.selectedChannel p
      (ending.input.row.2 ending.input.time).1 = some (1, i) := by
    change ReferenceSelectedAffinePairLaw.selectedChannel p
      ((ending.input.rows ending.input.selected).2 ending.input.time).1 = some (1, i)
    rw [hfields.1, hfields.2.1]
    exact hchannel
  obtain ⟨_hslot, hdraw⟩ := selected_up_fields _ i hchannelActual
  obtain ⟨d, hd, heligible⟩ : ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
      ending.output.coordinator.up = some d ∧
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) := by
    rw [ReferenceActiveAffinePositiveTest.record_upPositive] at hpositive
    cases hc : ending.output.coordinator.up with
    | none => simp only [hc, ReferenceActiveAffinePositiveTest.upDiagnosticPositive, Bool.false_eq_true] at hpositive
    | some d =>
        rw [hc] at hpositive
        exact ⟨d, rfl, of_decide_eq_true hpositive⟩
  obtain ⟨_ledger, _hsite, _hledger, _hbank, _htime, _hobs, hindex, _hsample,
    _hslot, _henabled, _hgate, _hroundSample, _hreward, _hfeedback⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields ending d hd
  have hi : d.input.selectedFollower = i := by
    rw [CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw] at hindex
    exact hindex.trans hdraw
  let interval := Cn.records.drop a
  let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
  let rounds := interval.map fun r => r.input.time
  have htrace : trace ending.input.time = CoordinatorUpReception.roundInput d.input := by
    change ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i ending.input.time = _
    rw [ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record interval i hchron ending heInt]
    simp only [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hd, hi,
      ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput, ite_true]
  have hePositive : AffineBatchDecoder.entry p trace ending.input.time ∈ AffineBatchDecoder.positives p trace rounds := by
    apply (AffineBatchDecoder.mem_positives_iff p trace rounds _).mpr
    refine ⟨List.mem_map.mpr ⟨ending, heInt, rfl⟩, ?_, rfl⟩
    change AffineBatchDecoder.eligible (trace ending.input.time)
    rw [htrace]
    exact heligible
  have hmax := positive_time_le_decision trace rounds (List.pairwise_map.mpr hchron)
    skip last hdecision _ hePositive
  change ending.input.time.val ≤ last.time.val at hmax
  have hrBound : record.input.time.val ≤ ending.input.time.val := by
    obtain ⟨q, hq, hget⟩ := List.mem_iff_getElem.mp (List.mem_of_mem_drop hmem)
    have hrt := record_time_index initial rows selected rewards s (a + n) hspan active q hq
    rw [hget] at hrt
    have hqn : q < a + n := by rw [ReferenceActivePhysicalHorizon.run_record_count] at hq; exact hq
    omega
  apply ReferenceAssignmentPayloadChronology.run_records_time_injective initial rows selected rewards
    s (a + n) hspan active (List.mem_of_mem_drop hmem) heMem
  have ht := congrArg Fin.val htime
  omega

/-- Conditional extension of E's literal saved-prefix output. The public root
supplies its entire input from E, the launch seed and the actual gate producer. -/
private theorem source_awaited_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsLaunch : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s)
    (w : ℕ) (originalRecords B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (rest : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (P0 : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) (before : ReferencePrelaunchFollower.State p rate.eta)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross) s)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross))
    (hBsplit : B = cut :: rest)
    (hwindow : ∀ a : Fin B.length, originalRecords[w + a.val]? = some B[a.val] ∧
      B[a.val].input.time.val + 1 = s + w + 1 + a.val)
    (hgateInputs :
      cut.output.next.coordinator = .dagger ∨ cut.output.next.followers i = .dagger ∨
      (∀ a : Fin B.length,
      (ReferenceFollowerFixedReply.actualChoice B[a.val] i).configuration = .dagger ∨
      ∃ choice memory,
        (ReferenceFollowerFixedReply.actualChoice B[a.val] i).configuration = .ordinary choice memory ∧
        ∀ (_hs : PublicDiscreteDraws.slotDraw (B[a.val].input.row.2 B[a.val].input.time).1 = PublicDiscreteDraws.upSlot)
          (_hi : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (B[a.val].input.row.2 B[a.val].input.time).1 = i),
          ReferenceActiveAffinePositiveTest.upSent B[a.val].input =
            some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
      (∀ a : Fin B.length, B[a.val].output.next.coordinator ≠ .dagger →
      ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
        B[a.val].output.coordinator.up = some d ∧
        ∀ (_hs : PublicDiscreteDraws.slotDraw (B[a.val].input.row.2 B[a.val].input.time).1 = PublicDiscreteDraws.upSlot)
          (_hi : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (B[a.val].input.row.2 B[a.val].input.time).1 = i),
          i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (B.take a.val)).toFinset →
          d.input.selectedFollower = i ∧ (CoordinatorUpReception.roundInput d.input).selected = true ∧
          (CoordinatorUpReception.roundInput d.input).receiverEnabled = true ∧
          CoordinatorCollectionLedger.acceptUpCheck d.input.ledger i U = true)) :
    let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState rate source rewards C_star C_h hcross
    let rows := source.1.2
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    (          ∀ (n : ℕ) (_hn : n ≤ B.length),
            ∃ hspanN : s + (w + n) ≤ p.T,
            let Cn := ReferenceActivePhysicalHorizon.run I rows J rewards s (w + n) hspanN active
            Cn.finalState.coordinator = .dagger ∨
            Cn.finalState.followers i = .dagger ∨
            (let preRun := ReferenceActivePhysicalHorizon.run I rows J rewards s w
               ((Nat.add_le_add_left (Nat.le_add_right w n) s).trans hspanN) active
             let interval := Cn.records.drop w
             let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
             let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds
               I rows J rewards s w (w + n) hspanN active
             let positive := AffineBatchDecoder.positives p trace rounds
             let channel := preRun.finalState.upDecoderBank i
             let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
             positive.length = AffineBatchDecoder.quota p - channel.pending.length +
               AffineBatchDecoder.quota p →
             ∃ (endpoint : ReferencePrelaunchFollower.State p rate.eta)
               (endpointMemory : ActiveFollowerLifecycle.LocalMemory p)
               (moving : ReferenceActivePhysicalStep.Ledger rate)
               (movingSaved : Option (Fin p.T × Bool)),
               Cn.finalState.followers i = .ordinary endpoint endpointMemory ∧
               endpoint.status = .unoccupied ∧
               ReferenceFollowerReplyChronology.reply endpoint =
                 ReferenceFollowerReplyChronology.reply before ∧
               Cn.finalState.coordinator = .collection P0 moving movingSaved ∧
               moving.sigma = s + 1 ∧
               moving.pending = Finset.univ \
                 (ReferenceCollectionPhaseHistory.acceptedLabels (B.take n)).toFinset ∧
               interval = B.take n ∧
               ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
                 (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
                 (index : Fin rounds.length)
                 (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
                 (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                 let decoderBefore := AffineBatchDecoder.run p trace (rounds.take index.val) channel
                 first = channel.pending ++ positive.take
                     (AffineBatchDecoder.quota p - channel.pending.length) ∧
                 first.length = AffineBatchDecoder.quota p ∧
                 window.length = AffineBatchDecoder.quota p ∧
                 window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
                 last ∈ window ∧
                 AffineBatchDecoder.decisionTime window = some last.time ∧
                 rounds.get index = last.time ∧
                 record ∈ interval ∧
                 record.input.time = last.time ∧
                 record.output.coordinator.up = some diagnostic ∧
                 diagnostic.input.selectedFollower = i ∧
                 diagnostic.input.time = record.input.time ∧
                 last = AffineBatchDecoder.entry p trace last.time ∧
                 last.sample = ((record.input.rows record.input.selected).2 record.input.time).2
                   (1, CoordinatorUpMeasurability.selectedChannelFollower
                     ((record.input.rows record.input.selected).2 record.input.time)) ∧
                 (∃ ledger,
                   ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
                   CoordinatorUpReception.receptionInputCheck
                     (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
                   diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) ∧
                 ReferenceActivePhysicalHorizon.Connected preRun.finalState
                   (interval.take index.val) record.input.state ∧
                 record.input.state.upDecoderBank =
                   ReferenceCoordinatorUpDecoderReplay.replay preRun.finalState.upDecoderBank
                     (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics (interval.take index.val)) ∧
                 diagnostic.input.upDecoderBank = record.input.state.upDecoderBank ∧
                 decoderBefore = diagnostic.input.upDecoderBank i ∧
                 decoderBefore.pending ++ [AffineBatchDecoder.entry p trace last.time] = window ∧
                 (CoordinatorUpReception.decoderTransition diagnostic.input).1.pending = [] ∧
                 (CoordinatorUpReception.decoderTransition diagnostic.input).1.completed =
                   channel.completed ++ [first, window] ∧
                 diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition diagnostic.input).1 ∧
                 diagnostic.raw = (CoordinatorUpReception.decoderTransition diagnostic.input).2 ∧
                 diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
                 CoordinatorUpReception.decoderTransition diagnostic.input =
                   (⟨[], channel.completed ++ [first, window]⟩, AffineBatchDecoder.batchOutput window) ∧
                 AffineBatchDecoder.run p trace rounds channel = ⟨[], channel.completed ++ [first, window]⟩ ∧
                 AffineBatchDecoder.run p trace rounds channel = Cn.finalState.upDecoderBank i ∧
                 (∀ entry, entry ∈ window →
                   AffineBatchDecoder.equation entry.sample
                     (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                 AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window)
                   (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                 ∃ (k : Fin B.length) (Lsite : ReferenceActivePhysicalStep.Ledger rate)
                   (received : ReferenceActivePhysicalStep.Ledger rate)
                   (receivedBank : CoordinatorUpReception.UpDecoderBank p),
                   record = B[k.val] ∧
                   originalRecords[w + k.val]? = some record ∧
                   ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some Lsite ∧
                   diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input Lsite ∧
                   Lsite.pending = Finset.univ \
                     (ReferenceCollectionPhaseHistory.acceptedLabels (B.take k.val)).toFinset ∧
                   ((ReferenceActivePhysicalStep.receiveUp
                       (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
                         .success (received, receivedBank) ∨
                     (ReferenceActivePhysicalStep.receiveUp
                       (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
                         .rejected (received, receivedBank)) ∧
                   ((∃! word, AffineBatchDecoder.satisfies
                       (AffineBatchDecoder.samples window) word) →
                     diagnostic.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                     diagnostic.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                     CoordinatorCollectionLedger.acceptUpCheck Lsite i U = true ∧
                     OrdinaryMessageCodec.acceptUp
                       (CoordinatorCollectionLedger.codecParams p rate.eta.val)
                       Lsite.cutoff Lsite.cursor i.val
                       (CoordinatorCollectionLedger.pendingNaturalLabels Lsite) Lsite.sigma U ∧
                     ReferenceCollectionPhaseHistory.filteredParsed record.input Lsite = some U ∧
                     diagnostic.parsed = some U ∧ diagnostic.locallyAccepted = true ∧
                     diagnostic.rawMatches = true ∧
                     ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
                       (bank : CoordinatorUpReception.UpDecoderBank p),
                       (ReferenceActivePhysicalStep.receiveUp
                         (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
                           .success (decoded, bank) ∧
                       ReferenceCollectionPhaseHistory.AcceptedUp record.input i U ∧
                       ReferenceCollectionPhaseHistory.acceptedLabel record.input = some i))) →
          ∀ (n : ℕ) (_hn : n ≤ B.length),
            ∃ hspanN : s + (w + n) ≤ p.T,
            let Cn := ReferenceActivePhysicalHorizon.run I rows J rewards s (w + n) hspanN active
            Cn.finalState.coordinator = .dagger ∨
            Cn.finalState.followers i = .dagger ∨
            (let preRun := ReferenceActivePhysicalHorizon.run I rows J rewards s w
               ((Nat.add_le_add_left (Nat.le_add_right w n) s).trans hspanN) active
             let interval := Cn.records.drop w
             let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
             let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds
               I rows J rewards s w (w + n) hspanN active
             let positive := AffineBatchDecoder.positives p trace rounds
             let channel := preRun.finalState.upDecoderBank i
             let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
             positive.length = AffineBatchDecoder.quota p - channel.pending.length +
               AffineBatchDecoder.quota p →
             ∃ (endpoint : ReferencePrelaunchFollower.State p rate.eta)
               (endpointMemory : ActiveFollowerLifecycle.LocalMemory p)
               (moving : ReferenceActivePhysicalStep.Ledger rate)
               (movingSaved : Option (Fin p.T × Bool)),
               Cn.finalState.followers i = .ordinary endpoint endpointMemory ∧
               endpoint.status = .unoccupied ∧
               ReferenceFollowerReplyChronology.reply endpoint =
                 ReferenceFollowerReplyChronology.reply before ∧
               Cn.finalState.coordinator = .collection P0 moving movingSaved ∧
               moving.sigma = s + 1 ∧
               moving.pending = Finset.univ \
                 (ReferenceCollectionPhaseHistory.acceptedLabels (B.take n)).toFinset ∧
               interval = B.take n ∧
               ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
                 (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
                 (index : Fin rounds.length)
                 (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
                 (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                 let decoderBefore := AffineBatchDecoder.run p trace (rounds.take index.val) channel
                 first = channel.pending ++ positive.take
                     (AffineBatchDecoder.quota p - channel.pending.length) ∧
                 first.length = AffineBatchDecoder.quota p ∧
                 window.length = AffineBatchDecoder.quota p ∧
                 window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
                 last ∈ window ∧
                 AffineBatchDecoder.decisionTime window = some last.time ∧
                 rounds.get index = last.time ∧
                 record ∈ interval ∧
                 record.input.time = last.time ∧
                 record.output.coordinator.up = some diagnostic ∧
                 diagnostic.input.selectedFollower = i ∧
                 diagnostic.input.time = record.input.time ∧
                 last = AffineBatchDecoder.entry p trace last.time ∧
                 last.sample = ((record.input.rows record.input.selected).2 record.input.time).2
                   (1, CoordinatorUpMeasurability.selectedChannelFollower
                     ((record.input.rows record.input.selected).2 record.input.time)) ∧
                 (∃ ledger,
                   ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
                   CoordinatorUpReception.receptionInputCheck
                     (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
                   diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) ∧
                 ReferenceActivePhysicalHorizon.Connected preRun.finalState
                   (interval.take index.val) record.input.state ∧
                 record.input.state.upDecoderBank =
                   ReferenceCoordinatorUpDecoderReplay.replay preRun.finalState.upDecoderBank
                     (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics (interval.take index.val)) ∧
                 diagnostic.input.upDecoderBank = record.input.state.upDecoderBank ∧
                 decoderBefore = diagnostic.input.upDecoderBank i ∧
                 decoderBefore.pending ++ [AffineBatchDecoder.entry p trace last.time] = window ∧
                 (CoordinatorUpReception.decoderTransition diagnostic.input).1.pending = [] ∧
                 (CoordinatorUpReception.decoderTransition diagnostic.input).1.completed =
                   channel.completed ++ [first, window] ∧
                 diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition diagnostic.input).1 ∧
                 diagnostic.raw = (CoordinatorUpReception.decoderTransition diagnostic.input).2 ∧
                 diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
                 CoordinatorUpReception.decoderTransition diagnostic.input =
                   (⟨[], channel.completed ++ [first, window]⟩, AffineBatchDecoder.batchOutput window) ∧
                 AffineBatchDecoder.run p trace rounds channel = ⟨[], channel.completed ++ [first, window]⟩ ∧
                 AffineBatchDecoder.run p trace rounds channel = Cn.finalState.upDecoderBank i ∧
                 (∀ entry, entry ∈ window →
                   AffineBatchDecoder.equation entry.sample
                     (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                 AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window)
                   (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                 0 < n ∧
                 (∃ hend : w + n - 1 < Cn.records.length,
                   let ending := Cn.records[w + n - 1]'hend
                   ReferenceSelectedAffinePairLaw.selectedChannel p ((rows J).2 ending.input.time).1 = some (1, i) →
                   ReferenceActiveAffinePositiveTest.upPositive ending.input = true → record = ending) ∧
                 (∀ entry ∈ window, s + w ≤ entry.time.val) ∧
                 ReferenceSelectedAffinePairLaw.selectedChannel p ((rows J).2 last.time).1 = some (1, i) ∧
                 ReferenceActiveAffinePositiveTest.upPositive record.input = true ∧
                 (record.input.state.upDecoderBank i).pending ++
                   [AffineBatchDecoder.entry p
                     (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
                     diagnostic.input.time] = window ∧
                 (record.input.state.upDecoderBank i).pending.length + 1 = AffineBatchDecoder.quota p ∧
                 CoordinatorCollectionLedger.codecParams p rate.eta.val =
                   ReferencePrelaunchFollower.codecParams p rate.eta ∧
                 (∀ control0 : ContinuousLearningRows.TimeControl p,
                   ∃ (hs : s ≤ last.time.val)
                     (hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
                       (rate := rate) rewards C_star C_h J last.time (1, i) s),
                   let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource (rate := rate)
                     rewards C_star C_h J last.time s i := ⟨source, hz⟩
                   ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord (rate := rate)
                     rewards C_star C_h J last.time s hs control0 i z = record ∧
                   ReferenceGeneratedUpAwaitedBatchCoverage.awaited_up_source_trace
                     rewards C_star C_h J last.time s hs control0 i z (s + w) U ∧
                   ((∃ v₁ v₂ : AffineChannelLaw.Word (AffineBatchDecoder.width p),
                     v₁ ≠ v₂ ∧ AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v₁ ∧
                       AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v₂) →
                     source ∈ ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEvent
                       (rate := rate) rewards C_star C_h control0)) ∧
                 ∃ (k : Fin B.length) (Lsite : ReferenceActivePhysicalStep.Ledger rate)
                   (received : ReferenceActivePhysicalStep.Ledger rate)
                   (receivedBank : CoordinatorUpReception.UpDecoderBank p),
                   record = B[k.val] ∧
                   originalRecords[w + k.val]? = some record ∧
                   ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some Lsite ∧
                   diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input Lsite ∧
                   Lsite.pending = Finset.univ \
                     (ReferenceCollectionPhaseHistory.acceptedLabels (B.take k.val)).toFinset ∧
                   ((ReferenceActivePhysicalStep.receiveUp
                       (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
                         .success (received, receivedBank) ∨
                     (ReferenceActivePhysicalStep.receiveUp
                       (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
                         .rejected (received, receivedBank)) ∧
                   ((∃! word, AffineBatchDecoder.satisfies
                       (AffineBatchDecoder.samples window) word) →
                     diagnostic.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                     diagnostic.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                     CoordinatorCollectionLedger.acceptUpCheck Lsite i U = true ∧
                     OrdinaryMessageCodec.acceptUp
                       (CoordinatorCollectionLedger.codecParams p rate.eta.val)
                       Lsite.cutoff Lsite.cursor i.val
                       (CoordinatorCollectionLedger.pendingNaturalLabels Lsite) Lsite.sigma U ∧
                     ReferenceCollectionPhaseHistory.filteredParsed record.input Lsite = some U ∧
                     diagnostic.parsed = some U ∧ diagnostic.locallyAccepted = true ∧
                     diagnostic.rawMatches = true ∧
                     ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
                       (bank : CoordinatorUpReception.UpDecoderBank p),
                       (ReferenceActivePhysicalStep.receiveUp
                         (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
                           .success (decoded, bank) ∧
                       ReferenceCollectionPhaseHistory.AcceptedUp record.input i U ∧
                       ReferenceCollectionPhaseHistory.acceptedLabel record.input = some i)) := by
  classical
  intro I rows J hprefix n hn
  obtain ⟨hspanN, hbranch⟩ := hprefix n hn
  refine ⟨hspanN, ?_⟩
  intro Cn
  rcases hbranch with hdagger | hdagger | hordinary
  · exact Or.inl hdagger
  · exact Or.inr (Or.inl hdagger)
  refine Or.inr (Or.inr ?_)
  intro preRun interval trace rounds positive channel window hCount
  rcases hordinary hCount with ⟨endpoint, endpointMemory, moving, movingSaved,
    hEndpoint, hEndpointStatus, hEndpointReply, hmoving, hmovingSigma, hmovingPending,
    hintervalEq, first, last, index, record, diagnostic, hfirst, hfirstLen, hwindowLen,
    hwindowPairwise, hlastWindow, hdecision, hindexRound, hrecordMem, hrecordTime,
    hdiagnostic, hselected, hdiagnosticTime, hlastEntry, hsample, hledgerFacts,
    hconnectedCut, hbankReplay, hdiagnosticBank, hbeforeBank, hbeforePending,
    htransitionPending, htransitionCompleted, hdecoderAfter, hrawTransition,
    hrawBatch, htransitionPair, hrunReplay, hfinalBank, hequations, hsolves,
    k, Lsite, received, receivedBank, hBrecord, hlookup, hsite, hinput, hpending,
    hcases, hunique⟩
  have hOrd : Cn.finalState.coordinator ≠ .dagger := by rw [hmoving]; nofun
  have hcutInterval := ReferenceCoordinatorUpIntervalWindow.run_interval_cut
    I rows J rewards s w (w + n) (Nat.le_add_right w n) hspanN active hinitial hOrd
  have hroundsPairwise := ReferenceCoordinatorUpIntervalWindow.run_interval_rounds_chronological
    I rows J rewards s w (w + n) (Nat.le_add_right w n) hspanN active hinitial hOrd
  have hchron : interval.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val) := by
    have hvalues := List.pairwise_map.mpr hroundsPairwise
    have htimeValues : (interval.map fun r => r.input.time.val).Pairwise LT.lt := by
      simpa only [ReferenceCoordinatorUpIntervalWindow.intervalRounds,
        ReferenceCoordinatorUpIntervalWindow.intervalRecords, List.map_map,
        Function.comp_def] using hvalues
    exact List.pairwise_map.mp htimeValues
  have htraceRecord : trace record.input.time = CoordinatorUpReception.roundInput diagnostic.input := by
    change ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i record.input.time = _
    rw [ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record interval i hchron record hrecordMem]
    simp only [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hdiagnostic, hselected,
      ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput, ite_true]
  have hlastPositive := (AffineBatchDecoder.mem_positives_iff p trace rounds last).mp
    (List.mem_of_mem_drop hlastWindow)
  have heligible : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input) := by
    rw [← htraceRecord, hrecordTime]
    exact hlastPositive.2.1
  obtain ⟨hselectedChannel, hpositive⟩ := eligible_call_fields record diagnostic i hdiagnostic hselected heligible
  have hinputs := ReferenceActivePhysicalHorizon.run_record_inputs I rows J rewards
    s (w + n) hspanN active record (List.mem_of_mem_drop hrecordMem)
  have hselectedSource : ReferenceSelectedAffinePairLaw.selectedChannel p
      ((rows J).2 last.time).1 = some (1, i) := by
    change ReferenceSelectedAffinePairLaw.selectedChannel p
      ((record.input.rows record.input.selected).2 record.input.time).1 = some (1, i) at hselectedChannel
    rw [hinputs.1, hinputs.2.1, hrecordTime] at hselectedChannel
    exact hselectedChannel
  have hlastConstant : last = AffineBatchDecoder.entry p
      (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input) diagnostic.input.time := by
    calc
      last = AffineBatchDecoder.entry p trace last.time := hlastEntry
      _ = _ := by
        simp only [AffineBatchDecoder.entry, ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
          hdiagnosticTime, ← hrecordTime, htraceRecord]
  have hbankBefore : AffineBatchDecoder.run p trace (rounds.take index.val) channel =
      record.input.state.upDecoderBank i :=
    hbeforeBank.trans (congrArg (fun bank => bank i) hdiagnosticBank)
  have hbankWindow : (record.input.state.upDecoderBank i).pending ++
      [AffineBatchDecoder.entry p (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
        diagnostic.input.time] = window := by
    rw [← hbankBefore, ← hlastConstant]
    exact (congrArg (fun entry =>
      (AffineBatchDecoder.run p trace (rounds.take index.val) channel).pending ++ [entry])
        hlastEntry).trans hbeforePending
  have hQ : (record.input.state.upDecoderBank i).pending.length + 1 = AffineBatchDecoder.quota p := by
    have hlen := congrArg List.length hbankWindow
    simp only [List.length_append, List.length_singleton] at hlen
    exact hlen.trans hwindowLen
  have htimes : ∀ entry ∈ window, s + w ≤ entry.time.val := by
    intro entry he
    have hmem := (AffineBatchDecoder.mem_positives_iff p trace rounds entry).mp (List.mem_of_mem_drop he)
    exact (ReferenceCoordinatorUpIntervalWindow.run_interval_round_time_bounds I rows J rewards
      s w (w + n) (Nat.le_add_right w n) hspanN active hinitial hOrd entry.time hmem.1).1
  have hlastLower := htimes last hlastWindow
  have hrecordBounds := ReferenceCoordinatorUpIntervalWindow.run_interval_record_time_bounds I rows J rewards
    s w (w + n) (Nat.le_add_right w n) hspanN active hinitial hOrd record hrecordMem
  have htimeK : record.input.time.val = s + w + k.val := by
    have ht := (hwindow k).2
    rw [← hBrecord] at ht
    clear * - ht
    omega
  have hkN : k.val < n := by
    clear * - hrecordBounds htimeK
    omega
  have hnPos : 0 < n := Nat.zero_lt_of_lt hkN
  have hcutMem : cut ∈ interval := by
    change interval = B.take n at hintervalEq
    rw [hintervalEq, hBsplit]
    obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnPos)
    rw [hn', List.take_succ_cons]
    exact List.mem_cons_self
  have hcutOrd := hcutInterval.2.2.2.2.2.2 cut (List.mem_of_mem_drop hcutMem)
  have hcutFollowerOrd : cut.output.next.followers i ≠ .dagger := by
    obtain ⟨q, hq, hget⟩ := List.mem_iff_getElem.mp hcutMem
    obtain ⟨next, nextMemory, hf, _⟩ := ReferenceFollowerReplyChronology.connected_output_chronology
      hcutInterval.2.2.1 i endpoint endpointMemory hEndpoint q hq
    rw [hget] at hf
    rw [hf]
    nofun
  obtain ⟨hchoices, hreceivers⟩ := (hgateInputs.resolve_left hcutOrd).resolve_left hcutFollowerOrd
  have hgate := (CoordinatorUpReception.roundInput_selected_iff_gate diagnostic.input).mp heligible.1
  have hledger : diagnostic.input.ledger = Lsite := by rw [hinput]; rfl
  have hpendingAt : i ∈ Lsite.pending := by rw [← hledger, ← hselected]; exact hgate.2.2
  have hnotAt : i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (B.take k.val)).toFinset := by
    rw [hpending] at hpendingAt
    exact (Finset.mem_sdiff.mp hpendingAt).2
  have hendpoint := saved_record_eq_endpoint I rows J rewards s w n hspanN active i hnPos
    record last (AffineBatchDecoder.quota p - channel.pending.length) hrecordMem hrecordTime hchron hdecision
  have hfamily := selected_prefix_gates preRun.finalState Cn.finalState interval B n hn
    hintervalEq hcutInterval.2.2.1 i endpoint endpointMemory hEndpoint
    (fun r hr => hcutInterval.2.2.2.2.2.2 r (List.mem_of_mem_drop hr)) U k.val hkN hnotAt
    hchoices hreceivers
  have hsourceFacts := original_source_trace_of_gates rate source rewards C_star C_h hcross s hsLaunch
    w n hspanN active B hn i U record last.time hrecordMem hrecordTime hlastLower
    (by
      have hrt := congrArg Fin.val hrecordTime
      clear * - hrecordBounds hrt
      omega) hselectedSource hintervalEq
    (fun a => by
      have ht := (hwindow a).2
      clear * - ht
      omega)
    k.val (by rw [← hrecordTime]; exact htimeK) hfamily
  refine ⟨endpoint, endpointMemory, moving, movingSaved, hEndpoint, hEndpointStatus,
    hEndpointReply, hmoving, hmovingSigma, hmovingPending, hintervalEq,
    first, last, index, record, diagnostic, hfirst, hfirstLen, hwindowLen,
    hwindowPairwise, hlastWindow, hdecision, hindexRound, hrecordMem, hrecordTime,
    hdiagnostic, hselected, hdiagnosticTime, hlastEntry, hsample, hledgerFacts,
    hconnectedCut, hbankReplay, hdiagnosticBank, hbeforeBank, hbeforePending,
    htransitionPending, htransitionCompleted, hdecoderAfter, hrawTransition,
    hrawBatch, htransitionPair, hrunReplay, hfinalBank, hequations, hsolves,
    hnPos, hendpoint, htimes, hselectedSource, hpositive, hbankWindow, hQ,
    ReferenceUpReception.ledgerCodecParams_eq_followerCodecParams rate, ?_,
    k, Lsite, received, receivedBank, hBrecord, hlookup, hsite, hinput, hpending, hcases, hunique⟩
  intro control0
  obtain ⟨hs, hz, hcurrent, hawaited⟩ := hsourceFacts control0
  refine ⟨hs, hz, hcurrent, hawaited, ?_⟩
  rintro ⟨v₁, v₂, hne, hv₁, hv₂⟩
  refine ⟨J, last.time, s, hs, i, hz, diagnostic, ?_⟩
  dsimp only
  rw [hcurrent]
  refine ⟨hdiagnostic, hselected, hpositive, hQ, ⟨U, s + w, hawaited, ?_⟩, ?_⟩
  · rw [hbankWindow]
    exact htimes
  · rw [hbankWindow]
    exact ⟨v₁, v₂, hne, hv₁, hv₂⟩

/-- Original-source awaitedness and exact whole-bank coverage for the saved
early second window. The single reply precedes all prefix/control queries. -/
theorem actual_first_collection_early_up_source_awaited :
    ∀
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (_hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count),
    let x0 := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b0 := ReferenceInitializationRun.output x0
    let s := ReferenceInitializationRun.elapsed p b0.completed
    let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let Erun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
    let u := s + w + 1
    let rows := source.1.2
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    ∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (P0 : ReferenceActivePhysicalStep.Payload rate)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      Erun.records = W ++ cut :: suffix ∧
      ReferenceActivePhysicalHorizon.Connected I W cut.input.state ∧
      (∃ hindex : w < Erun.records.length, cut = Erun.records[w]'hindex) ∧
      cut.input.time.val = s + w ∧
      cut.input.state.coordinator = .live registers owned base ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true ∧
      P0 = registers.payload ∧ P0.sigma.val = s ∧
      (∀ arm, P0.queues arm = 0) ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) = u ∧
      birth ∈ Erun.records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
      birth.input.time.val = s ∧
      (∃ installed birthSelection,
        birth.output.preparation.coordinator = .first (.chosen installed birthSelection) ∧
          installed.registers.payload = P0) ∧
      Erun.records.length = count ∧
      B = cut :: (Erun.records.drop (w + 1)).takeWhile
        (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) ∧
      (∀ k : Fin B.length,
        Erun.records[w + k.val]? = some B[k.val] ∧
          B[k.val].input.time.val + 1 = u + k.val) ∧
      (cut.output.next.coordinator = .dagger ∨
        ∃ nextLedger saved, cut.output.next.coordinator = .collection P0 nextLedger saved) ∧
      ∀ (i : Fin (p.m - 1)) (j : Fin Erun.records.length)
        (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
        j.val < w → ReferenceAcceptedUpFollowerHistory.RetainedDown Erun.records[j.val] i M →
        ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p)
          (token : ActiveFollowerLifecycle.ProposalRead p)
          (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
          cut.input.state.followers i = .ordinary before memory ∧
          before.lastDown = some M ∧ M = P0.downRecord i ∧
          before.status ≠ .unoccupied ∧
          ReferencePrelaunchFollower.acceptedStart before = s + 1 ∧
          M.val.sigma = s + 1 ∧
          ActiveFollowerLifecycle.localStateDomainValid before ∧
          memory.lastProposalRead = some token ∧
          token.timestamp.val + 1 = cut.input.time.val ∧
          token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) token.timestamp ∧
          ActiveFollowerLifecycle.startRound rate.eta cut.input.time before memory =
            .ok ({before with status := .unoccupied}, memory) ∧
          ((ReferenceFollowerFixedReply.actualChoice cut i).configuration = .dagger ∨
            (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
              .ordinary {before with status := .unoccupied} memory ∧
            ∀ arrival,
              ActiveFollowerQueueOperation.serviceOutput rate.n
                {before with status := .unoccupied} arrival =
                  {before with status := .unoccupied}) ∧
          U.val = OrdinaryMessageCodec.UpFields.mk (s + 1) before.S before.delta before.backlog ∧
          0 < U.val.sigma ∧
          (∀ (_hslot : PublicDiscreteDraws.slotDraw
              (cut.input.row.2 cut.input.time).1 = PublicDiscreteDraws.upSlot)
            (_hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (cut.input.row.2 cut.input.time).1 = i),
            (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
              .ordinary {before with status := .unoccupied} memory ∧
            ActiveFollowerQueueOperation.checkedUpOffer rate.eta i cut.input.row
              (cut.input.state.activations i) cut.input.time
                {before with status := .unoccupied} = .offer U ∧
            ActiveFollowerQueueOperation.checkedUpOffer rate.eta
              (ReferenceFollowerFixedReply.actualChoice cut i).follower (ReferenceFollowerFixedReply.actualChoice cut i).row
              (ReferenceFollowerFixedReply.actualChoice cut i).activation (ReferenceFollowerFixedReply.actualChoice cut i).time
                {before with status := .unoccupied} = .offer U ∧
            ReferenceActiveAffinePositiveTest.upSent cut.input =
              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
            ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare cut.input) =
              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
          (cut.output.next.followers i = .dagger ∨
            ∃ out outMemory,
              cut.output.next.followers i = .ordinary out outMemory ∧
              out.status = .unoccupied ∧
              ReferenceFollowerReplyChronology.reply out =
                ReferenceFollowerReplyChronology.reply before ∧
              out.lastDown = some M ∧
              ReferencePrelaunchFollower.acceptedStart out = P0.sigma.val + 1) ∧
          (∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown cut i sigma) ∧
          ∀ (n : ℕ) (_hn : n ≤ B.length),
            ∃ hspanN : s + (w + n) ≤ p.T,
            let Cn := ReferenceActivePhysicalHorizon.run I rows J rewards s (w + n) hspanN active
            Cn.finalState.coordinator = .dagger ∨
            Cn.finalState.followers i = .dagger ∨
            (let preRun := ReferenceActivePhysicalHorizon.run I rows J rewards s w
               ((Nat.add_le_add_left (Nat.le_add_right w n) s).trans hspanN) active
             let interval := Cn.records.drop w
             let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
             let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds
               I rows J rewards s w (w + n) hspanN active
             let positive := AffineBatchDecoder.positives p trace rounds
             let channel := preRun.finalState.upDecoderBank i
             let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
             positive.length = AffineBatchDecoder.quota p - channel.pending.length +
               AffineBatchDecoder.quota p →
             ∃ (endpoint : ReferencePrelaunchFollower.State p rate.eta)
               (endpointMemory : ActiveFollowerLifecycle.LocalMemory p)
               (moving : ReferenceActivePhysicalStep.Ledger rate)
               (movingSaved : Option (Fin p.T × Bool)),
               Cn.finalState.followers i = .ordinary endpoint endpointMemory ∧
               endpoint.status = .unoccupied ∧
               ReferenceFollowerReplyChronology.reply endpoint =
                 ReferenceFollowerReplyChronology.reply before ∧
               Cn.finalState.coordinator = .collection P0 moving movingSaved ∧
               moving.sigma = s + 1 ∧
               moving.pending = Finset.univ \
                 (ReferenceCollectionPhaseHistory.acceptedLabels (B.take n)).toFinset ∧
               interval = B.take n ∧
               ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
                 (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
                 (index : Fin rounds.length)
                 (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
                 (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                 let decoderBefore := AffineBatchDecoder.run p trace (rounds.take index.val) channel
                 first = channel.pending ++ positive.take
                     (AffineBatchDecoder.quota p - channel.pending.length) ∧
                 first.length = AffineBatchDecoder.quota p ∧
                 window.length = AffineBatchDecoder.quota p ∧
                 window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
                 last ∈ window ∧
                 AffineBatchDecoder.decisionTime window = some last.time ∧
                 rounds.get index = last.time ∧
                 record ∈ interval ∧
                 record.input.time = last.time ∧
                 record.output.coordinator.up = some diagnostic ∧
                 diagnostic.input.selectedFollower = i ∧
                 diagnostic.input.time = record.input.time ∧
                 last = AffineBatchDecoder.entry p trace last.time ∧
                 last.sample = ((record.input.rows record.input.selected).2 record.input.time).2
                   (1, CoordinatorUpMeasurability.selectedChannelFollower
                     ((record.input.rows record.input.selected).2 record.input.time)) ∧
                 (∃ ledger,
                   ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
                   CoordinatorUpReception.receptionInputCheck
                     (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
                   diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) ∧
                 ReferenceActivePhysicalHorizon.Connected preRun.finalState
                   (interval.take index.val) record.input.state ∧
                 record.input.state.upDecoderBank =
                   ReferenceCoordinatorUpDecoderReplay.replay preRun.finalState.upDecoderBank
                     (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics (interval.take index.val)) ∧
                 diagnostic.input.upDecoderBank = record.input.state.upDecoderBank ∧
                 decoderBefore = diagnostic.input.upDecoderBank i ∧
                 decoderBefore.pending ++ [AffineBatchDecoder.entry p trace last.time] = window ∧
                 (CoordinatorUpReception.decoderTransition diagnostic.input).1.pending = [] ∧
                 (CoordinatorUpReception.decoderTransition diagnostic.input).1.completed =
                   channel.completed ++ [first, window] ∧
                 diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition diagnostic.input).1 ∧
                 diagnostic.raw = (CoordinatorUpReception.decoderTransition diagnostic.input).2 ∧
                 diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
                 CoordinatorUpReception.decoderTransition diagnostic.input =
                   (⟨[], channel.completed ++ [first, window]⟩, AffineBatchDecoder.batchOutput window) ∧
                 AffineBatchDecoder.run p trace rounds channel = ⟨[], channel.completed ++ [first, window]⟩ ∧
                 AffineBatchDecoder.run p trace rounds channel = Cn.finalState.upDecoderBank i ∧
                 (∀ entry, entry ∈ window →
                   AffineBatchDecoder.equation entry.sample
                     (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                 AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window)
                   (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                 0 < n ∧
                 (∃ hend : w + n - 1 < Cn.records.length,
                   let ending := Cn.records[w + n - 1]'hend
                   ReferenceSelectedAffinePairLaw.selectedChannel p ((rows J).2 ending.input.time).1 = some (1, i) →
                   ReferenceActiveAffinePositiveTest.upPositive ending.input = true → record = ending) ∧
                 (∀ entry ∈ window, s + w ≤ entry.time.val) ∧
                 ReferenceSelectedAffinePairLaw.selectedChannel p ((rows J).2 last.time).1 = some (1, i) ∧
                 ReferenceActiveAffinePositiveTest.upPositive record.input = true ∧
                 (record.input.state.upDecoderBank i).pending ++
                   [AffineBatchDecoder.entry p
                     (ReferenceCoordinatorUpDecoderReplay.constantInputTrace diagnostic.input)
                     diagnostic.input.time] = window ∧
                 (record.input.state.upDecoderBank i).pending.length + 1 = AffineBatchDecoder.quota p ∧
                 CoordinatorCollectionLedger.codecParams p rate.eta.val =
                   ReferencePrelaunchFollower.codecParams p rate.eta ∧
                 (∀ control0 : ContinuousLearningRows.TimeControl p,
                   ∃ (hs : s ≤ last.time.val)
                     (hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
                       (rate := rate) rewards C_star C_h J last.time (1, i) s),
                   let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource (rate := rate)
                     rewards C_star C_h J last.time s i := ⟨source, hz⟩
                   ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord (rate := rate)
                     rewards C_star C_h J last.time s hs control0 i z = record ∧
                   ReferenceGeneratedUpAwaitedBatchCoverage.awaited_up_source_trace
                     rewards C_star C_h J last.time s hs control0 i z (s + w) U ∧
                   ((∃ v₁ v₂ : AffineChannelLaw.Word (AffineBatchDecoder.width p),
                     v₁ ≠ v₂ ∧ AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v₁ ∧
                       AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v₂) →
                     source ∈ ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEvent
                       (rate := rate) rewards C_star C_h control0)) ∧
                 ∃ (k : Fin B.length) (Lsite : ReferenceActivePhysicalStep.Ledger rate)
                   (received : ReferenceActivePhysicalStep.Ledger rate)
                   (receivedBank : CoordinatorUpReception.UpDecoderBank p),
                   record = B[k.val] ∧
                   Erun.records[w + k.val]? = some record ∧
                   ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some Lsite ∧
                   diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input Lsite ∧
                   Lsite.pending = Finset.univ \
                     (ReferenceCollectionPhaseHistory.acceptedLabels (B.take k.val)).toFinset ∧
                   ((ReferenceActivePhysicalStep.receiveUp
                       (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
                         .success (received, receivedBank) ∨
                     (ReferenceActivePhysicalStep.receiveUp
                       (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
                         .rejected (received, receivedBank)) ∧
                   ((∃! word, AffineBatchDecoder.satisfies
                       (AffineBatchDecoder.samples window) word) →
                     diagnostic.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                     diagnostic.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                     CoordinatorCollectionLedger.acceptUpCheck Lsite i U = true ∧
                     OrdinaryMessageCodec.acceptUp
                       (CoordinatorCollectionLedger.codecParams p rate.eta.val)
                       Lsite.cutoff Lsite.cursor i.val
                       (CoordinatorCollectionLedger.pendingNaturalLabels Lsite) Lsite.sigma U ∧
                     ReferenceCollectionPhaseHistory.filteredParsed record.input Lsite = some U ∧
                     diagnostic.parsed = some U ∧ diagnostic.locallyAccepted = true ∧
                     diagnostic.rawMatches = true ∧
                     ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
                       (bank : CoordinatorUpReception.UpDecoderBank p),
                       (ReferenceActivePhysicalStep.receiveUp
                         (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
                           .success (decoded, bank) ∧
                       ReferenceCollectionPhaseHistory.AcceptedUp record.input i U ∧
                       ReferenceCollectionPhaseHistory.acceptedLabel record.input = some i)) := by
  classical
  intro rate source rewards C_star C_h count hcross hspan hshort x0 b0 s I Erun W w B u rows J active
  have hE := ReferenceFirstCollectionEarlyUpWindowAcceptance.actual_first_collection_early_up_window_acceptance
    rate source rewards C_star C_h count hcross hspan hshort
  rcases hE with ⟨cut, suffix, registers, owned, base, P0, birth,
    hsplit, hconnected, hcutIndex, hcutTime, hcutState, hcutoff, hpayload,
    hsigma, hqueues, hfirstCutoff, hbirthMem, hbirthInstall, hbirthTime,
    hbirthFirst, hrecords, hBsplit, hwindow, hcoordNext, hqueries⟩
  have hlaunch := ReferenceFirstCollectionLateUpSecondWindow.actual_launch_up_bank_seed
    rate source rewards C_star C_h count hcross hspan
  have hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant I := hlaunch.1
  refine ⟨cut, suffix, registers, owned, base, P0, birth,
    hsplit, hconnected, hcutIndex, hcutTime, hcutState, hcutoff, hpayload,
    hsigma, hqueues, hfirstCutoff, hbirthMem, hbirthInstall, hbirthTime,
    hbirthFirst, hrecords, hBsplit, hwindow, hcoordNext, ?_⟩
  intro i j M hj hretained
  rcases hqueries i j M hj hretained with
    ⟨before, memory, token, U, hbefore, hlast, hMpayload, hoccupied, hstart,
      hMstart, hdomain, htoken, htokenTime, htokenBit, hstartRound, hcutChoice,
      hUfields, hUpositive, hcutSender, hcutFollower, hcutNoDown, hprefix⟩
  have hgateInputs := early_gate_inputs rate source rewards C_star C_h count hcross hspan hshort
    cut hcutIndex i j M hj hretained before memory U hbefore hUfields
  refine ⟨before, memory, token, U, hbefore, hlast, hMpayload, hoccupied,
    hstart, hMstart, hdomain, htoken, htokenTime, htokenBit, hstartRound,
    hcutChoice, hUfields, hUpositive, hcutSender, hcutFollower, hcutNoDown, ?_⟩
  exact source_awaited_prefix rate source rewards C_star C_h hcross s rfl w Erun.records B cut _
    P0 i before U active hinitial hBsplit hwindow hgateInputs hprefix

/-- The same actual early query and positive-count branch, projected to the
literal original-source event for two distinct solvers of the whole window.
The fixed reply and awaited trace are produced by the preceding theorem. -/
theorem actual_early_second_batch_ambiguous_source_coverage :
    ∀
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (_hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count),
    let x0 := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b0 := ReferenceInitializationRun.output x0
    let s := ReferenceInitializationRun.elapsed p b0.completed
    let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let Erun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
    let rows := source.1.2
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    ∀ (i : Fin (p.m - 1)) (j : Fin Erun.records.length)
      (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
    j.val < w → ReferenceAcceptedUpFollowerHistory.RetainedDown Erun.records[j.val] i M →
    ∀ (n : ℕ) (_hn : n ≤ B.length), ∃ hspanN : s + (w + n) ≤ p.T,
    let Cn := ReferenceActivePhysicalHorizon.run I rows J rewards s (w + n) hspanN active
    Cn.finalState.coordinator = .dagger ∨ Cn.finalState.followers i = .dagger ∨
      (let preRun := ReferenceActivePhysicalHorizon.run I rows J rewards s w
         ((Nat.add_le_add_left (Nat.le_add_right w n) s).trans hspanN) active
       let interval := Cn.records.drop w
       let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
       let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds I rows J rewards s w (w + n) hspanN active
       let positive := AffineBatchDecoder.positives p trace rounds
       let channel := preRun.finalState.upDecoderBank i
       let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
       positive.length = AffineBatchDecoder.quota p - channel.pending.length + AffineBatchDecoder.quota p →
       ∀ control0 : ContinuousLearningRows.TimeControl p,
       (∃ v₁ v₂ : AffineChannelLaw.Word (AffineBatchDecoder.width p), v₁ ≠ v₂ ∧
         AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v₁ ∧
         AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v₂) →
       source ∈ ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEvent
         (rate := rate) rewards C_star C_h control0) := by
  classical
  intro rate source rewards C_star C_h count hcross hspan hshort x0 b0 s I Erun W w B rows J active
  have hA := actual_first_collection_early_up_source_awaited
    rate source rewards C_star C_h count hcross hspan hshort
  rcases hA with ⟨_cut, _suffix, _registers, _owned, _base, _P0, _birth,
    _hsplit, _hconnected, _hcutIndex, _hcutTime, _hcutState, _hcutoff, _hpayload,
    _hsigma, _hqueues, _hfirstCutoff, _hbirthMem, _hbirthInstall, _hbirthTime,
    _hbirthFirst, _hrecords, _hBsplit, _hwindow, _hcoordNext, hqueries⟩
  intro i j M hj hretained
  rcases hqueries i j M hj hretained with
    ⟨_before, _memory, _token, _U, _hbefore, _hlast, _hMpayload, _hoccupied, _hstart,
      _hMstart, _hdomain, _htoken, _htokenTime, _htokenBit, _hstartRound, _hcutChoice,
      _hUfields, _hUpositive, _hcutSender, _hcutFollower, _hcutNoDown, hprefix⟩
  intro n hn
  obtain ⟨hspanN, hbranch⟩ := hprefix n hn
  refine ⟨hspanN, ?_⟩
  intro Cn
  rcases hbranch with hd | hd | hordinary
  · exact Or.inl hd
  · exact Or.inr (Or.inl hd)
  refine Or.inr (Or.inr ?_)
  intro preRun interval trace rounds positive channel window hCount
  rcases hordinary hCount with ⟨_endpoint, _endpointMemory, _moving, _movingSaved,
    _hEndpoint, _hEndpointStatus, _hEndpointReply, _hmoving, _hmovingSigma, _hmovingPending,
    _hintervalEq, _first, _last, _index, _record, _diagnostic, _hfirst, _hfirstLen, _hwindowLen,
    _hwindowPairwise, _hlastWindow, _hdecision, _hindexRound, _hrecordMem, _hrecordTime,
    _hdiagnostic, _hselected, _hdiagnosticTime, _hlastEntry, _hsample, _hledgerFacts,
    _hconnectedCut, _hbankReplay, _hdiagnosticBank, _hbeforeBank, _hbeforePending,
    _htransitionPending, _htransitionCompleted, _hdecoderAfter, _hrawTransition,
    _hrawBatch, _htransitionPair, _hrunReplay, _hfinalBank, _hequations, _hsolves,
    _hnPos, _hendpoint, _htimes, _hselectedSource, _hpositive, _hbankWindow, _hQ, _hcodec,
    hsourceFacts, _rest⟩
  intro control0 hamb
  obtain ⟨_hs, _hz, _hcurrent, _hawaited, hcoverage⟩ := hsourceFacts control0
  exact hcoverage hamb

end Bandits.Support.ReferenceFirstCollectionEarlyUpSourceAwaited

end
