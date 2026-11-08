/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionSelectedUpAwaitedFields
public import Bandits.Support.ReferenceGeneratedUpAwaitedAmbiguityTail

import Lean.Elab.Tactic.Omega

/-!
# Original-source awaited trace for the second pure UP batch of the first replacement collection

Sources: `sources/zip4/manuscript/06_interruptions.tex:110-177,246-299,477-487`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:100-157`, and
`sources/zip4/manuscript/05_binary_transport.tex:20-55,180-239`.

This producer transports the actual second pure batch from the replacement
collection to the literal original-source awaited ambiguity event. The source,
private coordinates, complete reward table, physical record, and reply remain
shared throughout; no probability or stopping estimate is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceFirstReplacementCollectionPureUpAcceptanceRoot
open ReferenceFirstReplacementCollectionSelectedUpAwaitedFields

namespace Bandits.Support.ReferenceFirstReplacementCollectionPureUpSourceAwaited

private theorem fields_of_not_dagger
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (coordinator : ReferenceActivePhysicalStep.CoordinatorConfiguration p rate)
    {P : Prop} (h : match coordinator with | .dagger => True | _ => P)
    (hne : coordinator ≠ .dagger) : P := by
  cases coordinator <;> try exact h
  exact False.elim (hne rfl)

private theorem mem_positive_drop_tail
    {p : ConstructorDimensions.Parameters}
    (trace : AffineBatchDecoder.Trace p)
    (rounds : List (Fin p.T)) (skip : ℕ)
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hskip : 0 < skip)
    (hentry : entry ∈
      (AffineBatchDecoder.positives p trace rounds).drop skip) :
    entry.time ∈ rounds.drop 1 := by
  induction rounds generalizing skip with
  | nil => simp [AffineBatchDecoder.positives] at hentry
  | cons round rest ih =>
      cases skip with
      | zero => omega
      | succ skip =>
          by_cases hpositive : AffineBatchDecoder.eligible (trace round)
          · have htail : entry ∈
                (AffineBatchDecoder.positives p trace rest).drop skip := by
              simpa [AffineBatchDecoder.positives_cons,
                AffineBatchDecoder.positiveAt, hpositive] using hentry
            cases skip with
            | zero =>
                have hmem := (AffineBatchDecoder.mem_positives_iff p trace rest entry).mp
                  (by simpa using htail)
                simpa using hmem.1
            | succ skip =>
                simpa using List.mem_of_mem_drop (ih (skip + 1) (by omega) htail)
          · have htail : entry ∈
                (AffineBatchDecoder.positives p trace rest).drop (skip + 1) := by
              simpa [AffineBatchDecoder.positives_cons,
                AffineBatchDecoder.positiveAt, hpositive] using hentry
            simpa using List.mem_of_mem_drop (ih (skip + 1) (by omega) htail)

private theorem original_run_record_time
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (s count n : ℕ) (hspan : s + count ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hget : (ReferenceActiveHorizonMeasurability.runOfInput s count hspan input).records[n]? =
      some record) : record.input.time.val = s + n := by
  obtain ⟨hn, _⟩ := List.getElem?_eq_some_iff.mp hget
  have hlen := ReferenceActivePhysicalHorizon.run_record_count input.val.1
    input.val.2.1 input.val.2.2.1 input.val.2.2.2 s count hspan input.property
  have hn' : n < count := by
    change n < (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1
      input.val.2.2.1 input.val.2.2.2 s count hspan input.property).records.length at hn
    rw [hlen] at hn
    exact hn
  have htimes := ReferenceActivePhysicalHorizon.run_time_values input.val.1
    input.val.2.1 input.val.2.2.1 input.val.2.2.2 s count hspan input.property
  have h := congrArg (fun xs : List ℕ => xs[n]?) htimes
  dsimp only [ReferenceActiveHorizonMeasurability.runOfInput] at hget
  rw [List.getElem?_map, hget] at h
  simpa only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range', hn',
    ↓reduceIte, Nat.one_mul, Option.map_some, Option.some.injEq] using h

private theorem selected_up_fields
    {p : ConstructorDimensions.Parameters}
    (slice : ContinuousLearningRows.Slice p) (i : Fin (p.m - 1))
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

private theorem accepted_prefix_exclusion
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      )
    (i : Fin (p.m - 1)) (h k : ℕ) (hh : h ≤ k)
    (hnot : i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels
      (records.take k)).toFinset) :
    i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (records.take h)).toFinset := by
  intro hmem
  apply hnot
  rw [List.mem_toFinset] at hmem ⊢
  obtain ⟨record, hr, he⟩ := List.mem_filterMap.mp hmem
  exact List.mem_filterMap.mpr ⟨record,
    (List.take_prefix_take_left hh).subset hr, he⟩

private theorem run_prefix_records
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (ConstructorDimensions.M p))
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

private theorem original_source_run_input_eq
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch (rate := rate)
      rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source)
        t (1, i) s)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross) s) :
    ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput (rate := rate)
      rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source)
        t s hs control0 i ⟨source, hz⟩ =
      ⟨(ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hcross,
        source.1.2, ActualInitializationPhysicalStep.selectedRowIndex p source, rewards), active⟩ := by
  have hlaunch := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput_launch
    (rate := rate) rewards C_star C_h
    (ActualInitializationPhysicalStep.selectedRowIndex p source)
    t s hs control0 i ⟨source, hz⟩
  have hseed : (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
      (rate := rate) rewards C_star C_h
        (ActualInitializationPhysicalStep.selectedRowIndex p source)
        t s hs control0 i ⟨source, hz⟩).val.1 =
      ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross := by
    exact Option.some.inj (hlaunch.symm.trans
      (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate source rewards C_star C_h hcross))
  apply Subtype.ext
  exact Prod.ext hseed rfl

private theorem original_current_mem
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
      (rate := rate) rewards C_star C_h q t s hs control0 i z ∈
      (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z)).records := by
  let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  let left := t.val - s + 1
  have hprefix := run_prefix_records input.val.1 input.val.2.1 input.val.2.2.1
    input.val.2.2.2 s (p.T - s) (by omega) input.property left (by omega)
  have hsplit : (ReferenceActiveHorizonMeasurability.runOfInput s
      left (by omega) input).records =
      (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s)
        (by omega) input).records ++
        [ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
          (rate := rate) rewards C_star C_h q t s hs control0 i z] := by
    dsimp only [ReferenceActiveHorizonMeasurability.runOfInput]
    rw [ReferenceActivePhysicalHorizon.run_successor_step]
    have hentry : (⟨s + (t.val - s), by omega, by omega⟩ :
        ReferenceActivePhysicalHorizon.CalendarEntry p s) = ⟨t.val, hs, t.isLt⟩ :=
      Subtype.ext (Nat.add_sub_of_le hs)
    rw [hentry]
    rfl
  apply List.mem_of_mem_take (i := left)
  change _ ∈ (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 s (p.T - s) (by omega)
      input.property).records.take left
  rw [hprefix]
  dsimp only [ReferenceActiveHorizonMeasurability.runOfInput] at hsplit
  rw [hsplit]
  exact List.mem_append_right _ List.mem_cons_self

theorem complete_first_replacement_collection_pure_up_source_awaited
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        let X := (R.drop v).take (1 + tail.length)
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let M := fun i => payload.downRecord i
            (∀ i : Fin (p.m - 1),
              (∃ (b : ℕ) (anchor : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p)
                (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
                ((b = 0 ∧
                  (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                    .ordinary anchor memory ∧
                  ∃! x : Fin X.length,
                    ReferenceAcceptedUpFollowerHistory.RetainedDown (X.get x) i (M i)) ∨
                 (∃ q : Fin K.length, b = q.val + 1 ∧
                  ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i) ∧
                  (∀ a : Fin K.length, a.val < q.val →
                    ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get a) i (M i)) ∧
                  (K.get q).output.next.followers i = .ordinary anchor memory)) ∧
                b ≤ K.length ∧ anchor.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid anchor ∧
                anchor.lastDown = some (M i) ∧
                U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
                U.val.sigma = (M i).val.sigma ∧ 0 < U.val.sigma ∧
                let H := K.drop b
                let channel := (Z b).upDecoderBank i
                let Q := AffineBatchDecoder.quota p
                let need := Q - channel.pending.length + Q
                ((∃ (q : Fin K.length) (reason : ReferenceActivePhysicalStep.CoordinatorFailure),
                    b ≤ q.val + 1 ∧ (Z q.val).coordinator ≠ .dagger ∧
                    (K.get q).output.next.coordinator = .dagger ∧
                    (K.get q).output.coordinator.failure = some reason ∧
                    (∀ a : Fin K.length, a.val < q.val →
                      (K.get a).output.next.coordinator ≠ .dagger) ∧
                    (ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives
                      (K.take (q.val + 1)) i).length =
                    (ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives
                      (K.take q.val) i).length +
                      (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries (K.get q) i).length) ∨
                 ((∀ q : Fin K.length, (K.get q).output.next.coordinator ≠ .dagger) ∧
                  (((ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives H i).length < need ∧
                     ((∀ r ∈ H, ReferenceCollectionPhaseHistory.acceptedLabel r.input ≠ some i) ∨
                      ∃ r ∈ H, ReferenceCollectionPhaseHistory.acceptedLabel r.input = some i ∧
                        ∃ message, ReferenceCollectionPhaseHistory.AcceptedUp r.input i message ∧
                          ∃ ledger saved, (E W.length).coordinator = .collection payload ledger saved ∧
                            i ∉ ledger.pending ∧ ((E W.length).upDecoderBank i).pending = [])) ∨
                   ∃ m : ℕ, 2 ≤ m ∧ m ≤ H.length ∧
                     (ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives
                       (H.take m) i).length = need ∧
                     (∀ n : ℕ, n < m →
                       (ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives
                         (H.take n) i).length < need) ∧
                     let positive := ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives
                       (H.take m) i
                     let window := positive.drop (Q - channel.pending.length)
                     let beta := u + b
                     ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
                       (k : Fin K.length) (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                       let r := K.get k
                       first = channel.pending ++ positive.take (Q - channel.pending.length) ∧
                       first.length = Q ∧ window.length = Q ∧
                       window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
                       (∀ e ∈ window, AffineBatchDecoder.equation e.sample
                         (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                       k.val = b + m - 1 ∧ 0 < k.val ∧ R[c + k.val]? = some r ∧
                       r.input.time.val + 1 = u + k.val ∧
                       r.input.rows = source.1.2 ∧ r.input.selected = J ∧ r.input.rewards = rewards ∧
                       r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
                       d.input.time = r.input.time ∧
                       ReferenceActiveAffinePositiveTest.upPositive r.input = true ∧
                       (r.input.state.upDecoderBank i).pending.length + 1 = Q ∧
                       window = (r.input.state.upDecoderBank i).pending ++
                         [AffineBatchDecoder.entry p
                           (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time] ∧
                       d.decoderAfter = ⟨[], channel.completed ++ [first, window]⟩ ∧
                       (Z (b + m)).upDecoderBank i = ⟨[], channel.completed ++ [first, window]⟩ ∧
                       d.raw = AffineBatchDecoder.batchOutput window ∧
                       d.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                       (∀ entry ∈ window, beta ≤ entry.time.val) ∧
                       (∀ control0 : ContinuousLearningRows.TimeControl p,
                         ∃ (hs : s ≤ r.input.time.val)
                           (hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
                             (rate := rate) rewards C_star C_h J r.input.time (1, i) s),
                           let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
                             (rate := rate) rewards C_star C_h J r.input.time s i := ⟨source, hz⟩
                           ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
                             (rate := rate) rewards C_star C_h J r.input.time s hs control0 i z = r ∧
                           (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
                             (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
                               (rate := rate) rewards C_star C_h J r.input.time s hs control0 i z)).records = R ∧
                           ReferenceGeneratedUpAwaitedBatchCoverage.awaited_up_source_trace
                             (rate := rate) rewards C_star C_h J r.input.time s hs control0 i z beta U) ∧
                       ((d.raw = none ∧
                         (∃ other, other ≠ ActiveFollowerArmChoice.offeredUpWord rate.eta U ∧
                           ∀ entry ∈ window, AffineBatchDecoder.equation entry.sample other) ∧
                         ∀ control0 : ContinuousLearningRows.TimeControl p,
                           source ∈ ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEvent
                             (rate := rate) rewards C_star C_h control0 ∧
                           source ∈ ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope
                             (rate := rate) rewards C_star C_h control0) ∨
                        (d.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                         (∀ other, (∀ entry ∈ window,
                           AffineBatchDecoder.equation entry.sample other) →
                           other = ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                         ReferenceCollectionPhaseHistory.AcceptedUp r.input i U ∧
                         ∃ (started decoded : ReferenceActivePhysicalStep.Ledger rate)
                           (bank : CoordinatorUpReception.UpDecoderBank p),
                           ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some started ∧
                           d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input started ∧
                           CoordinatorCollectionLedger.acceptUpCheck started i U = true ∧
                           d.parsed = some U ∧ d.locallyAccepted = true ∧ d.rawMatches = true ∧
                           d.wrongUniqueAccepted = false ∧
                           (ReferenceActivePhysicalStep.receiveUp
                             (ReferenceActivePhysicalStep.prepare r.input) started).result =
                               .success (decoded, bank) ∧
                           decoded.pending = started.pending.erase i ∧
                           bank = CoordinatorUpReception.decoderBankAfter d.input ∧
                           r.output.next.upDecoderBank = bank ∧
                           (Z (b + m)).upDecoderBank = bank ∧
                           bank i = ⟨[], channel.completed ++ [first, window]⟩)))))) ∨
              ((∀ a : Fin K.length, ∃ state memory,
                  (ReferenceFollowerFixedReply.actualChoice (K.get a) i).configuration =
                    .ordinary state memory ∧ state.status = .unoccupied ∧
                  state.lastDown ≠ some (M i) ∧
                  ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∧
                  ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
                   ∃ old, state.lastDown = some old ∧ 0 < old.val.sigma ∧ old.val.sigma < (M i).val.sigma)) ∧
               (∀ q : Fin K.length, ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i)) ∧
               R[c + 1 + W.length]? = none)) ∧
            match R[c + 1 + W.length]? with
            | none => c + 1 + W.length = R.length ∧
                ReferenceCompletePhysicalHistory.completeTerminalState rate source rewards C_star C_h =
                  some (E W.length)
            | some next => next.input.state = E W.length ∧
                ReferenceCollectionPhaseHistory.laterChosen next.input = true ∧
                ∃ ledger saved, (E W.length).coordinator = .collection payload ledger saved ∧
                  ledger.pending = ∅ ∧
                  ∀ i : Fin (p.m - 1), ∃ r ∈ K, ∃ U,
                    ReferenceCollectionPhaseHistory.AcceptedUp r.input i U
          | _ => True
      | _ => True := by
  classical
  have hRoot :=
    ReferenceFirstReplacementCollectionPureUpAcceptanceRoot.complete_first_replacement_collection_pure_up_acceptance
      rate source rewards C_star C_h
  have hSelected :=
    ReferenceFirstReplacementCollectionSelectedUpAwaitedFields.complete_first_replacement_collection_selected_up_awaited_fields
      rate source rewards C_star C_h
  simp (config := { zeta := true }) only [] at hRoot hSelected ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set J := ActualInitializationPhysicalStep.selectedRowIndex p source
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hRoot hSelected ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hRoot hSelected ⊢
      cases outcome <;> try trivial
      rename_i core consistent birthStarted hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hRoot hSelected ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      rcases hRoot with ⟨_, _, hRoot⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [hc] at hRoot hSelected ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hRoot hSelected ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hRoot hSelected ⊢
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.output.next (W.take j)
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := fun i => payload.downRecord i
          rcases hRoot with ⟨hcalendar, hZ, hfollowers, hboundary⟩
          have hKprefix : K <+: R.drop c := by
            obtain ⟨hci, hce⟩ := List.getElem?_eq_some_iff.mp hc
            rw [List.drop_eq_getElem_cons hci, hce]
            refine ⟨(R.drop (c + 1)).dropWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input), ?_⟩
            simp only [K, W, List.cons_append, List.takeWhile_append_dropWhile]
          obtain ⟨initial, active, hlaunch, hfirst, hbank, hInvInitial,
              _hcollectedEmpty, hfull, hRuns⟩ :=
            ReferenceFirstReplacementCollectionPureUpWindowCut.source_interval_runs
              rate source rewards C_star C_h c cut hc K hKprefix
          have hInv : ∀ j, j ≤ K.length →
              ReferenceUpDecoderBankInvariant.upBankInvariant (Z j) := by
            intro j hj
            obtain ⟨span, _, hend⟩ := hRuns j hj
            change (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
              (c + j) span active).finalState = Z j at hend
            rw [← hend]
            exact ReferenceUpDecoderBankInvariant.run_upBankInvariant initial source.1.2
              J rewards s (c + j) span active hInvInitial
          refine ⟨?_, ?_⟩
          · intro i
            rcases hfollowers i with hcurrent | habsent
            · rcases hcurrent with ⟨b, anchor, memory, horigin, hbK, hstatus,
                hdomain, hlastDown, _hfinal, U, hfields, hsigma, hpositive,
                hchoices, hentries, hpure, hcases⟩
              refine Or.inl ⟨b, anchor, memory, U, ?_⟩
              refine ⟨?_, hbK, hstatus, hdomain, hlastDown, hfields, hsigma,
                hpositive, ?_⟩
              · rcases horigin with hzero | hlater
                · exact Or.inl hzero
                · rcases hlater with ⟨q, hbq, hretained, hbefore, hget, _hZget, _hcut⟩
                  exact Or.inr ⟨q, hbq, hretained, hbefore, hget⟩
              · let H := K.drop b
                let channel := (Z b).upDecoderBank i
                let Q := AffineBatchDecoder.quota p
                let need := Q - channel.pending.length + Q
                rcases hcases with hfailed | ⟨hsurvive, hsurviving⟩
                · rcases hfailed with ⟨q, reason, hbq, hbefore, hafter, hreason,
                    hprevious, _hreplay, _hrun, _hsuffix, hcount, _hsingle,
                    _hstage, _hdiagnostics⟩
                  exact Or.inl ⟨q, reason, hbq, hbefore, hafter, hreason,
                    hprevious, hcount⟩
                · refine Or.inr ⟨hsurvive, ?_⟩
                  rcases hsurviving with hshort | hthreshold
                  · exact Or.inl hshort
                  · rcases hthreshold with ⟨m, hm, hmH, hcount, hleast,
                      first, last, index, r, d, hfirst, hfirstLength,
                      hwindowLength, hchronological, hequations, hlast,
                      hdecisionTime, hr, hrtime, hd, hselected, hdtime,
                      hsample, hbankAtCall, hreplay, hwindow, hafter,
                      hraw, hexpected, hendpoint, hrawCases⟩
                    rcases hrawCases with ⟨hmTwo, k, hk, hkpos, hget,
                      hlookup, htime, hrows, hselectedRow, hrewards,
                      _hstate, _hpositiveEntries, hsender, heligible, hrawBranches⟩
                    let positive := ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives
                      (H.take m) i
                    let window := positive.drop (Q - channel.pending.length)
                    let beta := u + b
                    have hnotDagger : ∀ q : Fin K.length,
                        (K.get q).output.next.coordinator ≠ .dagger := hsurvive
                    have hnonDagger : r.output.next.coordinator ≠ .dagger := by
                      rw [← hget]
                      exact hnotDagger k
                    have hjbound : k.val - 1 < W.length := by
                      have hklt := k.isLt
                      change k.val < W.length + 1 at hklt
                      omega
                    let j : Fin W.length := ⟨k.val - 1, hjbound⟩
                    have hjplus : j.val + 1 = k.val := by dsimp only [j]; omega
                    have hrW : W.get j = r := by
                      have hkget : K.get k = r := hget
                      have hkval : k.val = j.val + 1 := hjplus.symm
                      simpa only [K, List.get_eq_getElem, hkval,
                        List.getElem_cons_succ] using hkget
                    have hselectedRecord := hSelected j
                    rw [hrW] at hselectedRecord
                    have hselectedRecord := fields_of_not_dagger
                      r.output.next.coordinator hselectedRecord hnonDagger
                    obtain ⟨_, _, _, _, _, _, _, _, hslotDetect,
                      _henabledDetect, _hselectedGateDetect, _, _, _, _⟩ :=
                      ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
                        r d hd
                    have hgateDetect :
                        CoordinatorUpReception.receptionGate d.input := by
                      exact (CoordinatorUpReception.roundInput_selected_iff_gate d.input).mp
                        heligible.1
                    have hphysicalSlot :
                        PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
                          PublicDiscreteDraws.upSlot :=
                      hslotDetect.symm.trans hgateDetect.2.1
                    have hdrawDetect :
                        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                          (r.input.row.2 r.input.time).1 = i := by
                      change CoordinatorUpMeasurability.selectedFollowerIndex
                        (r.input.row.2 r.input.time) = i at hsender
                      exact (CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw
                        (r.input.row.2 r.input.time)).symm.trans hsender
                    have hchannelDetect :
                        ReferenceSelectedAffinePairLaw.selectedChannel p
                          (r.input.row.2 r.input.time).1 =
                            some (1, Fin.cast
                              (show p.m - 1 = ContinuousLearningRows.d p by rfl) i) := by
                      rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _
                        hphysicalSlot, hdrawDetect]
                      rfl
                    rcases hselectedRecord i hchannelDetect with
                      ⟨stateDetect, memoryDetect, UDetect, ledgerDetect,
                        diagnosticDetect, hconfigDetect, hstatusDetect,
                        hfieldsDetect, hcheckedDetect, hsentDetect,
                        hsiteDetect, hcheckDetect, hdiagnosticDetect,
                        hinputDetect, hselectedDetect, hexpectedDetect,
                        hsigmaDetect, hcutoffDetect, hcursorDetect,
                        hcutCursorDetect, hpendingDetect, hselectedIffDetect,
                        henabledDetect, hcaseDetect⟩
                    have hdiagnosticEq : diagnosticDetect = d :=
                      Option.some.inj (hdiagnosticDetect.symm.trans hd)
                    subst diagnosticDetect
                    have hnotK : i ∉
                        (ReferenceCollectionPhaseHistory.acceptedLabels
                          (K.take k.val)).toFinset := by
                      have h := hselectedIffDetect.mp heligible.1
                      simpa only [hjplus] using h
                    have hpendingLt : channel.pending.length < Q := by
                      have hinvariant := hInv b hbK
                      change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
                        (Z b).coordinator (Z b).upDecoderBank at hinvariant
                      exact (hinvariant.1 i).1
                    have hskip : 0 < Q - channel.pending.length := by omega
                    have hlastEntry : last =
                        AffineBatchDecoder.entry p
                          (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
                          d.input.time := by
                      cases last with
                      | mk lastTime lastSample =>
                          simp only [AffineBatchDecoder.entry,
                            ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
                            AffineBatchDecoder.Entry.mk.injEq]
                          exact ⟨(hdtime.trans hrtime).symm, hsample⟩
                    have hwindowBank :
                        (r.input.state.upDecoderBank i).pending ++
                          [AffineBatchDecoder.entry p
                            (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
                            d.input.time] = window := by
                      have h := hwindow
                      rw [hbankAtCall, hlastEntry] at h
                      exact h
                    have hQ : (r.input.state.upDecoderBank i).pending.length + 1 = Q := by
                      calc
                        (r.input.state.upDecoderBank i).pending.length + 1 =
                            ((r.input.state.upDecoderBank i).pending ++
                              [AffineBatchDecoder.entry p
                                (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
                                d.input.time]).length := by simp
                        _ = window.length := congrArg List.length hwindowBank
                        _ = Q := hwindowLength
                    have hpositiveAtCall :
                        ReferenceActiveAffinePositiveTest.upPositive r.input = true := by
                      rw [ReferenceActiveAffinePositiveTest.record_upPositive, hd]
                      simp [ReferenceActiveAffinePositiveTest.upDiagnosticPositive, heligible]
                    have hwindowTimes : ∀ entry ∈ window,
                        beta ≤ entry.time.val := by
                      intro entry hentry
                      dsimp only [window, positive,
                        ReferenceFirstReplacementCollectionPureUpWindowCut.physicalPositives]
                        at hentry
                      have htail := mem_positive_drop_tail
                        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace (H.take m) i)
                        ((H.take m).map (fun record => record.input.time))
                        (Q - channel.pending.length) entry hskip hentry
                      have htailMap : entry.time ∈
                          ((H.take m).drop 1).map (fun record => record.input.time) := by
                        simpa only [List.map_drop] using htail
                      have htakePrefix : (H.take m).drop 1 <+: H.drop 1 :=
                        (List.take_prefix m H).drop 1
                      obtain ⟨round, hroundMem, hroundTime⟩ := List.mem_map.mp htailMap
                      have hroundK : round ∈ K.drop (b + 1) := by
                        simpa only [H, List.drop_drop, Nat.add_comm] using
                          htakePrefix.subset hroundMem
                      have htimeMem : entry.time ∈
                          (K.drop (b + 1)).map (fun record => record.input.time) := by
                        exact List.mem_map.mpr ⟨round, hroundK, hroundTime⟩
                      obtain ⟨n, hgetN⟩ := List.mem_iff_getElem?.mp hroundK
                      have hgetKN : K[n + (b + 1)]? = some round := by
                        simpa only [List.getElem?_drop, Nat.add_comm] using hgetN
                      obtain ⟨hn, hgetKN'⟩ := List.getElem?_eq_some_iff.mp hgetKN
                      let q : Fin K.length := ⟨n + (b + 1), hn⟩
                      have hq : q.val = n + (b + 1) := rfl
                      have htimeRound : (K.get q).input.time.val + 1 = u + q.val :=
                        hcalendar q
                      have htimeEq : K.get q = round := by
                        simpa only [List.get_eq_getElem] using hgetKN'
                      rw [htimeEq] at htimeRound
                      have hbeta : beta = u + b := rfl
                      rw [hroundTime] at htimeRound
                      rw [hbeta]
                      omega
                    have hawaited :
                        ∀ control0 : ContinuousLearningRows.TimeControl p,
                          ∃ (hs : s ≤ r.input.time.val)
                            (hz : source ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
                              (rate := rate) rewards C_star C_h J r.input.time (1, i) s),
                            let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
                                (rate := rate) rewards C_star C_h J r.input.time s i :=
                              ⟨source, hz⟩
                            ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
                                (rate := rate) rewards C_star C_h J r.input.time s hs control0 i z = r ∧
                              (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
                                (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
                                  (rate := rate) rewards C_star C_h J r.input.time s hs control0 i z)).records = R ∧
                              ReferenceGeneratedUpAwaitedBatchCoverage.awaited_up_source_trace
                                rewards C_star C_h J r.input.time s hs control0 i z beta U := by
                        intro control0
                        let query := r.input.time
                        have hchannelSource :
                            ReferenceSelectedAffinePairLaw.selectedChannel p
                              ((source.1.2 J).2 query).1 = some (1, i) := by
                          have hcast : Fin.cast
                              (show p.m - 1 = ContinuousLearningRows.d p by rfl) i = i :=
                            Fin.ext rfl
                          have hactual : ReferenceSelectedAffinePairLaw.selectedChannel p
                              ((r.input.rows r.input.selected).2 query).1 = some (1, i) := by
                            have hplain := hchannelDetect
                            have hcast : Fin.cast
                                (show p.m - 1 = ContinuousLearningRows.d p by rfl) i = i :=
                              Fin.ext rfl
                            rw [hcast] at hplain
                            change ReferenceSelectedAffinePairLaw.selectedChannel p
                              (r.input.row.2 r.input.time).1 = some (1, i)
                            exact hplain
                          simpa only [← hrows, ← hselectedRow, J] using hactual
                        have hselSource :=
                          (ReferenceSelectedAffinePairLaw.selector_eq_iff p J query
                            (1, i) source).2 ⟨rfl, hchannelSource⟩
                        have hcross :
                            (ReferenceInitializationRun.output
                              (ActualReferenceInitializationBlock.referenceInput
                                source rewards C_star C_h rate)).crossing.isSome = true := by
                          have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
                              rate source rewards C_star C_h).isSome = true := by
                            rw [hlaunch]
                            rfl
                          exact (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
                            rate source rewards C_star C_h).mp hsome
                        have hz : source ∈
                            ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
                              (rate := rate) rewards C_star C_h J query (1, i) s := by
                          change ReferenceSelectedAffinePairLaw.selector p query source =
                              (J, some (1, i)) ∧ _ ∧ _
                          exact ⟨hselSource, hcross, rfl⟩
                        have hlaunchState : initial =
                            ReferenceFirstLaunchNumericalCell.launchState
                              rate source rewards C_star C_h hcross := by
                          apply Option.some.inj
                          calc
                            some initial = ReferenceCorrectedInitializationLaunch.correctedLaunch
                                rate source rewards C_star C_h := hlaunch.symm
                            _ = some (ReferenceFirstLaunchNumericalCell.launchState
                                rate source rewards C_star C_h hcross) :=
                              ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
                                rate source rewards C_star C_h hcross
                        subst initial
                        have hspanFull : s + (p.T - s) ≤ p.T := by
                          have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T
                            rate source rewards C_star C_h
                          omega
                        let canonicalInput :
                            ReferenceActiveHorizonMeasurability.ActiveRunInput
                              (p := p) (rate := rate) s :=
                          ⟨(ReferenceFirstLaunchNumericalCell.launchState
                              rate source rewards C_star C_h hcross,
                            source.1.2, J, rewards), active⟩
                        have hcutGetRun :
                            (ReferenceActivePhysicalHorizon.run
                              (ReferenceFirstLaunchNumericalCell.launchState
                                rate source rewards C_star C_h hcross)
                              source.1.2 J rewards s (p.T - s) hspanFull active).records[c]? =
                              some cut := by
                          rw [← hfull]
                          exact hc
                        have hcutRunTime := original_run_record_time s (p.T - s) c
                          hspanFull canonicalInput cut
                          (by simpa [canonicalInput,
                            ReferenceActiveHorizonMeasurability.runOfInput] using hcutGetRun)
                        have huEq : u = s + c + 1 := by
                          have hcalendarCut := hcalendar
                            (⟨0, by simp [K]⟩ : Fin K.length)
                          have hcutIndex : K.get ⟨0, by simp [K]⟩ = cut := by simp [K]
                          rw [hcutIndex] at hcalendarCut
                          omega
                        have hrecordTime : r.input.time.val = s + c + k.val := by
                          have hcalendarK := hcalendar k
                          rw [hget] at hcalendarK
                          have hcalendarK' : r.input.time.val + 1 =
                              (s + c + k.val) + 1 := by
                            calc
                              r.input.time.val + 1 = u + k.val := hcalendarK
                              _ = (s + c + k.val) + 1 := by
                                simp only [huEq, Nat.add_assoc, Nat.add_comm 1, Nat.add_left_comm]
                          exact Nat.add_right_cancel hcalendarK'
                        have hsQuery : s ≤ query.val := by
                          change s ≤ r.input.time.val
                          rw [hrecordTime]
                          simpa only [Nat.add_assoc] using Nat.le_add_right s (c + k.val)
                        let z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
                            (rate := rate) rewards C_star C_h J query s i := ⟨source, hz⟩
                        have hsourceInput := original_source_run_input_eq rate source rewards
                          C_star C_h hcross query s hsQuery control0 i hz active
                        let full := ReferenceActiveHorizonMeasurability.runOfInput s
                          (p.T - s) (by omega)
                          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
                            (rate := rate) rewards C_star C_h J query s hsQuery control0 i z)
                        have hrunInputRecords := congrArg
                          (fun inp : ReferenceActiveHorizonMeasurability.ActiveRunInput
                              (p := p) (rate := rate) s =>
                            (ReferenceActiveHorizonMeasurability.runOfInput s
                              (p.T - s) (by omega) inp).records) hsourceInput
                        have hfullInput : full.records = R := by
                          change (ReferenceActiveHorizonMeasurability.runOfInput s
                            (p.T - s) (by omega)
                            (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
                              (rate := rate) rewards C_star C_h J query s hsQuery control0 i z)).records = R
                          calc
                            _ = (ReferenceActiveHorizonMeasurability.runOfInput s
                                (p.T - s) (by omega) canonicalInput).records := hrunInputRecords
                            _ = R := by
                              change (ReferenceActivePhysicalHorizon.run
                                (ReferenceFirstLaunchNumericalCell.launchState
                                  rate source rewards C_star C_h hcross)
                                source.1.2 J rewards s (p.T - s) (by omega) active).records = R
                              exact hfull.symm
                        let current :=
                          ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
                            (rate := rate) rewards C_star C_h J query s hsQuery control0 i z
                        have hcurrentMem : current ∈ full.records := by
                          exact original_current_mem rate rewards C_star C_h J query s hsQuery
                            control0 i z
                        have hrecordMem : r ∈ full.records := by
                          rw [hfullInput]
                          obtain ⟨hn, hgetN⟩ := List.getElem?_eq_some_iff.mp hlookup
                          exact List.mem_iff_getElem.mpr ⟨c + k.val, hn, hgetN⟩
                        have hcanonicalRecords : full.records =
                            (ReferenceActivePhysicalHorizon.run
                              (ReferenceFirstLaunchNumericalCell.launchState
                                rate source rewards C_star C_h hcross)
                              source.1.2 J rewards s (p.T - s) (by omega) active).records := by
                          calc
                            full.records = R := hfullInput
                            _ = (ReferenceActivePhysicalHorizon.run
                                (ReferenceFirstLaunchNumericalCell.launchState
                                  rate source rewards C_star C_h hcross)
                                source.1.2 J rewards s (p.T - s) (by omega) active).records := hfull
                        have hcurrentRunMem : current ∈
                            (ReferenceActivePhysicalHorizon.run
                              (ReferenceFirstLaunchNumericalCell.launchState
                                rate source rewards C_star C_h hcross)
                              source.1.2 J rewards s (p.T - s) (by omega) active).records := by
                          rw [← hcanonicalRecords]
                          exact hcurrentMem
                        have hrecordRunMem : r ∈
                            (ReferenceActivePhysicalHorizon.run
                              (ReferenceFirstLaunchNumericalCell.launchState
                                rate source rewards C_star C_h hcross)
                              source.1.2 J rewards s (p.T - s) (by omega) active).records := by
                          rw [← hcanonicalRecords]
                          exact hrecordMem
                        have hcurrentTime : current.input.time = query := by
                          exact (ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentInput_original_fields
                            (rate := rate) rewards C_star C_h J query s hsQuery control0 i z).2.2.1
                        have hcurrentEq : current = r := by
                          apply ReferenceAssignmentPayloadChronology.run_records_time_injective
                            (ReferenceFirstLaunchNumericalCell.launchState
                              rate source rewards C_star C_h hcross)
                            source.1.2 J rewards s (p.T - s) (by omega) active
                            hcurrentRunMem hrecordRunMem
                          calc
                            current.input.time.val = query.val := congrArg Fin.val hcurrentTime
                            _ = r.input.time.val := rfl
                        refine ⟨hsQuery, hz, ?_⟩
                        refine ⟨hcurrentEq, hfullInput, ?_⟩
                        change s ≤ beta ∧ beta ≤ query.val ∧
                          ∀ record ∈ full.records,
                            beta ≤ record.input.time.val →
                            record.input.time.val ≤ query.val →
                            ReferenceSelectedAffinePairLaw.selectedChannel p
                              (record.input.row.2 record.input.time).1 = some (1, i) →
                            ReferenceActiveAffinePositiveTest.upSent record.input =
                              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                            ∃ diagnostic, record.output.coordinator.up = some diagnostic ∧
                              diagnostic.input.selectedFollower = i ∧
                              (CoordinatorUpReception.roundInput diagnostic.input).selected = true ∧
                              (CoordinatorUpReception.roundInput diagnostic.input).receiverEnabled = true ∧
                              CoordinatorCollectionLedger.acceptUpCheck
                                diagnostic.input.ledger i U = true
                        refine ⟨?_, ?_, ?_⟩
                        · have hbetaEq : beta = s + c + b + 1 := by
                            dsimp [beta]
                            omega
                          omega
                        · have hbetaEq : beta = s + c + b + 1 := by
                            dsimp [beta]
                            omega
                          rw [hbetaEq]
                          dsimp [query]
                          omega
                        intro x hx hlow hupp hchannelX
                        have hxR : x ∈ R := by
                          rw [← hfullInput]
                          exact hx
                        obtain ⟨n, hxGet⟩ := List.mem_iff_getElem?.mp hx
                        have hrunGet : full.records[n]? = some x := hxGet
                        have hxTime := original_run_record_time s (p.T - s) n hspanFull
                          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
                            (rate := rate) rewards C_star C_h J query s hsQuery control0 i z)
                          x hrunGet
                        have huEq : u = s + c + 1 := by
                          have hcalendarCut := hcalendar
                            (⟨0, by simp [K]⟩ : Fin K.length)
                          have hcutIndex : K.get ⟨0, by simp [K]⟩ = cut := by simp [K]
                          rw [hcutIndex] at hcalendarCut
                          have hcutFull : full.records[c]? = some cut := by
                            rw [hfullInput]
                            exact hc
                          have hcutTime := original_run_record_time s (p.T - s) c
                            hspanFull
                            (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
                              (rate := rate) rewards C_star C_h J query s hsQuery control0 i z)
                            cut (by simpa [full] using hcutFull)
                          omega
                        have hrecordTime : r.input.time.val = s + c + k.val := by
                          have hcalendarK := hcalendar k
                          omega
                        have hnLower : c + b + 1 ≤ n := by
                          have hbetaEq : beta = s + c + b + 1 := by
                            dsimp [beta]
                            omega
                          omega
                        have hnUpper : n ≤ c + k.val := by
                          rw [hxTime, hrecordTime] at hupp
                          omega
                        let a := n - c
                        have haLower : b + 1 ≤ a := by dsimp [a]; omega
                        have haUpper : a ≤ k.val := by dsimp [a]; omega
                        have haLt : a < K.length := lt_of_le_of_lt haUpper k.isLt
                        have hRget : R[n]? = some x := by
                          simpa only [hfullInput] using hrunGet
                        have hdropGet : (R.drop c)[a]? = some x := by
                          have hsum : c + a = n := by dsimp [a]; omega
                          simpa only [List.getElem?_drop, hsum] using hRget
                        obtain ⟨suffix, hsuffix⟩ := hKprefix
                        have hKgetOpt : K[a]? = some x := by
                          rw [← hsuffix] at hdropGet
                          rw [List.getElem?_append_left haLt] at hdropGet
                          exact hdropGet
                        have hKget : K.get ⟨a, haLt⟩ = x :=
                          (List.getElem?_eq_some_iff.mp hKgetOpt).2
                        have hnotAtA := accepted_prefix_exclusion K i a k haUpper hnotK
                        let j : Fin W.length := ⟨a - 1, by
                          have hlen := k.isLt
                          change k.val < W.length + 1 at hlen
                          omega⟩
                        have hjplus : j.val + 1 = a := by dsimp [j]; omega
                        have hWget : W.get j = x := by
                          have hbound : a < (cut :: W).length := by
                            simpa only [K] using haLt
                          have hKget' : (cut :: W).get ⟨a, hbound⟩ = x := by
                            simpa only [K] using hKget
                          have haEq : a = j.val + 1 := by omega
                          have hindex : (⟨a, hbound⟩ : Fin (cut :: W).length) = Fin.succ j := by
                            apply Fin.ext
                            exact haEq
                          have hKget'' : (cut :: W).get (Fin.succ j) = x := by
                            rw [← hindex]
                            exact hKget'
                          simpa only [List.get_eq_getElem, Fin.val_succ,
                            List.getElem_cons_succ] using hKget''
                        have hnotDaggerX : x.output.next.coordinator ≠ .dagger := by
                          have h := hsurvive ⟨a, haLt⟩
                          rw [hKget] at h
                          exact h
                        have hSelectedFields := hSelected j
                        rw [hWget] at hSelectedFields
                        have hSelectedFields := fields_of_not_dagger
                          x.output.next.coordinator hSelectedFields hnotDaggerX
                        have hchannelCast :
                            ReferenceSelectedAffinePairLaw.selectedChannel p
                              (x.input.row.2 x.input.time).1 =
                                some (1, Fin.cast
                                  (show p.m - 1 = ContinuousLearningRows.d p by rfl) i) := by
                          have hcast : Fin.cast
                              (show p.m - 1 = ContinuousLearningRows.d p by rfl) i = i :=
                            Fin.ext rfl
                          rw [hcast]
                          exact hchannelX
                        rcases hSelectedFields i hchannelCast with
                          ⟨stateA, memoryA, UA, LA, diagnosticA, hconfigA,
                            hstatusA, hfieldsA, hcheckedA, hsentA, hsiteA,
                            hcheckA, hdiagnosticA, hinputA, hselectedA,
                            hexpectedA, hsigmaA, hcutoffA, hcursorA,
                            hcutCursorA, hpendingA, hselectedIffA,
                            henabledA, hcaseA⟩
                        have hqIndex : a < K.length := haLt
                        let qa : Fin K.length := ⟨a, hqIndex⟩
                        have hKx : K.get qa = x := hKget
                        obtain ⟨stateP, memoryP, hconfigP, _hstatusP,
                          hdownP, _hreplyP, hofferP, _hexpectedP⟩ :=
                          hchoices qa (by dsimp [qa]; omega)
                        have hconfigEq : stateA = stateP := by
                          have hcfg :
                              DeclaredFollowerLocalRound.LocalConfiguration.ordinary
                                stateA memoryA = .ordinary stateP memoryP := by
                            calc
                              _ = (ReferenceFollowerFixedReply.actualChoice x i).configuration :=
                                hconfigA.symm
                              _ = (ReferenceFollowerFixedReply.actualChoice (K.get qa) i).configuration := by
                                rw [hKx]
                              _ = .ordinary stateP memoryP := hconfigP
                          exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hcfg).1
                        have hsenderX :
                            ReferenceActivePhysicalStep.upSenderIndex x.input = i := by
                          obtain ⟨_, hdrawX⟩ := selected_up_fields
                            (x.input.row.2 x.input.time).1 i hchannelX
                          change CoordinatorUpMeasurability.selectedFollowerIndex
                            (x.input.row.2 x.input.time) = i
                          rw [CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
                          exact hdrawX
                        have hslotX :
                            PublicDiscreteDraws.slotDraw (x.input.row.2 x.input.time).1 =
                              PublicDiscreteDraws.upSlot :=
                          (selected_up_fields (x.input.row.2 x.input.time).1 i hchannelX).1
                        have hsenderP :
                            ReferenceActivePhysicalStep.upSenderIndex (K.get qa).input = i := by
                          simpa only [hKx] using hsenderX
                        have hslotP :
                            PublicDiscreteDraws.slotDraw
                              ((K.get qa).input.row.2 (K.get qa).input.time).1 =
                                PublicDiscreteDraws.upSlot := by
                          simpa only [hKx] using hslotX
                        have hrootOffer := hofferP hsenderP hslotP
                        have hcodec :=
                          ReferenceUpReception.ledgerCodecParams_eq_followerCodecParams rate
                        cases hcodec
                        have hUA : UA = U := by
                          apply ActiveFollowerQueueOperation.UpOfferResult.offer.inj
                          calc
                            .offer UA = ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
                                x.input.row (x.input.state.activations i) x.input.time stateA :=
                              hcheckedA.symm
                            _ = ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
                                (K.get qa).input.row
                                  ((K.get qa).input.state.activations i)
                                  (K.get qa).input.time stateP := by
                                rw [← hKx, hconfigEq]
                            _ = .offer U := hrootOffer.1
                        have hnotPrior : i ∉
                            (ReferenceCollectionPhaseHistory.acceptedLabels
                              (K.take a)).toFinset := by
                          simpa only [K, hjplus] using hnotAtA
                        have hnotPriorAtJ : i ∉
                            (ReferenceCollectionPhaseHistory.acceptedLabels
                              ((cut :: W).take (j.val + 1))).toFinset := by
                          simpa only [K, hjplus] using hnotPrior
                        have hacceptA :
                            CoordinatorCollectionLedger.acceptUpCheck LA i UA = true := by
                          rcases hcaseA with hbad | hgood
                          · have hsigUA : UA.val.sigma = (M i).val.sigma := by
                              rw [hUA]
                              exact hsigma
                            exact False.elim (by
                              rw [hsigUA] at hbad
                              exact (lt_irrefl _ hbad.2.1))
                          · have hiff := hgood.2.2
                            exact hiff.mpr hnotPriorAtJ
                        have hledgerEq : diagnosticA.input.ledger = LA := by
                          rw [hinputA]
                          rfl
                        refine ⟨?_, diagnosticA, hdiagnosticA, hselectedA,
                          ?_, henabledA, ?_⟩
                        · rw [hUA] at hsentA
                          exact hsentA
                        · exact hselectedIffA.mpr hnotPriorAtJ
                        · rw [hledgerEq]
                          cases hUA
                          exact hacceptA
                    refine Or.inr ⟨m, hmTwo, hmH, hcount, hleast,
                      first, k, d, ?_⟩
                    cases hget
                    let r := K.get k
                    refine ⟨hfirst, hfirstLength, hwindowLength, hchronological,
                      hequations, hk, hkpos, hlookup, htime, hrows, hselectedRow,
                      hrewards, hd, hselected, hdtime, hpositiveAtCall, hQ,
                      hwindowBank.symm, hafter, hendpoint, hraw, hexpected,
                      hwindowTimes, hawaited, ?_⟩
                    rcases hrawBranches with hambiguous | hsuccess
                    · rcases hambiguous with ⟨hrawNone, other, hother, hotherEquations⟩
                      refine Or.inl ⟨hrawNone, ⟨other, hother, hotherEquations⟩, ?_⟩
                      intro control0
                      obtain ⟨hsQuery', hz', hcurrentEq', _hfullSource', htrace'⟩ := hawaited control0
                      have hbatchEq :
                          ((ReferenceGeneratedUpPrefixPositiveHalf.originalSourceCurrentRecord
                            (rate := rate) rewards C_star C_h J r.input.time s hsQuery'
                              control0 i ⟨source, hz'⟩).input.state.upDecoderBank i).pending ++
                            [AffineBatchDecoder.entry p
                              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
                              d.input.time] = window := by
                        exact (congrArg (fun record : ReferenceCompletePhysicalHistory.RoundRecord p rate =>
                          (record.input.state.upDecoderBank i).pending ++
                            [AffineBatchDecoder.entry p
                              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input)
                              d.input.time]) hcurrentEq').trans hwindowBank
                      have hevent : source ∈
                          ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEvent
                            (rate := rate) rewards C_star C_h control0 := by
                        refine ⟨J, r.input.time, s, hsQuery', i, hz', d, ?_⟩
                        refine ⟨?_, hselected, ?_, ?_, ?_, ?_⟩
                        · exact (congrArg
                            (fun record : ReferenceCompletePhysicalHistory.RoundRecord p rate =>
                              record.output.coordinator.up) hcurrentEq').trans hd
                        · exact (congrArg
                            (fun record : ReferenceCompletePhysicalHistory.RoundRecord p rate =>
                              ReferenceActiveAffinePositiveTest.upPositive record.input)
                            hcurrentEq').trans hpositiveAtCall
                        · exact (congrArg
                            (fun record : ReferenceCompletePhysicalHistory.RoundRecord p rate =>
                              (record.input.state.upDecoderBank i).pending.length + 1)
                            hcurrentEq').trans hQ
                        · refine ⟨U, beta, htrace', ?_⟩
                          intro entry hentry
                          apply hwindowTimes entry
                          rw [← hbatchEq]
                          exact hentry
                        · refine ⟨ActiveFollowerArmChoice.offeredUpWord rate.eta U,
                            other, Ne.symm hother, ?_, ?_⟩
                          · apply (AffineBatchDecoder.satisfies_samples_iff
                              (B := AffineBatchDecoder.width p) _
                              (ActiveFollowerArmChoice.offeredUpWord rate.eta U)).2
                            intro entry hentry
                            have hmem : entry ∈ window := Eq.mp
                              (congrArg (fun batch : List
                                (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) =>
                                  entry ∈ batch) hbatchEq) hentry
                            exact hequations entry hmem
                          · apply (AffineBatchDecoder.satisfies_samples_iff
                              (B := AffineBatchDecoder.width p) _ other).2
                            intro entry hentry
                            have hmem : entry ∈ window := Eq.mp
                              (congrArg (fun batch : List
                                (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) =>
                                  entry ∈ batch) hbatchEq) hentry
                            exact hotherEquations entry hmem
                      constructor
                      · exact hevent
                      · exact ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEvent_subset_envelope
                          (rate := rate) rewards C_star C_h control0 hevent
                    · rcases hsuccess.2.2 with
                        ⟨ledger, saved, tail, recording, started, decoded, bank, finished,
                          clockFinished, hstate, htail, hrecording, hstart, hsite, hcheck,
                          hinput, htailReception, hstartedSigma, hcutoff, hcursor,
                          hcutCursor, hstartedPending, hmember, hnotAccepted, hstartedU,
                          hacceptCheck, hparsed, hparsedDiagnostic, hlocallyAccepted,
                          hrawMatches, hwrongUnique, hreceive, hdecodedPending, hbank,
                          hnextBank, hendpointBank, hbankI, hfinish, hclock, haccepted⟩
                      exact Or.inr ⟨hsuccess.1, hsuccess.2.1, haccepted,
                        started, decoded, bank, hsite, hinput, hacceptCheck,
                        hparsedDiagnostic, hlocallyAccepted, hrawMatches, hwrongUnique,
                        hreceive, hdecodedPending, hbank, hnextBank, hendpointBank, hbankI⟩

            · exact Or.inr ⟨habsent.1, habsent.2.2.1, habsent.2.2.2.2⟩
          · cases hterminal : R[c + 1 + W.length]? with
            | none =>
              simp only [W, hterminal] at hboundary ⊢
              exact hboundary
            | some next =>
              simp only [W, hterminal] at hboundary ⊢
              rcases hboundary with ⟨hstate, hlater, ledger, saved,
                hcoord, hnextCoord, hpending, haccepted⟩
              exact ⟨hstate, hlater, ledger, saved, hcoord, hpending, haccepted⟩

end Bandits.Support.ReferenceFirstReplacementCollectionPureUpSourceAwaited

end
