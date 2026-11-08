/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFormedUpSecondPureBatch

import Lean.Elab.Tactic.Omega

/-!
# Local actual formed-UP deciding receiver

Internal actual-run proofs retain the initialized dispatch, clipped formation,
inherited decoder bank, completed history, and deciding physical receiver.
The local formation and exact-count conditions do not assert service attainment.

This internal producer keeps the full actual-source telescope and explicit
per-slice geometry, endpoint, inherited-bank replay, invariant, and selected-UP
receiver premises. Their actual constructor is the same dispatch witness of
`ReferenceFirstCollectionFormedUpSecondPureBatch.actual_initialized_first_collection_formed_up_second_pure_batch`.
The mandatory next consumer is a fresh source-dispatch assembly applying that
constructor once and supplying these local premises from its same witness.
This module does not implement that assembly or assert manuscript closure.

Sources: `06_interruptions.tex:476-481`, `05_binary_transport.tex:20-55,70-124`,
and `appendix_a_local_protocol.tex:139-157` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalHorizon

namespace Bandits.Support.ReferenceFirstCollectionFormedUpLocalReceiverCut

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Every retained positive in the actual UP trace belongs to its physical
record and exposes the real checked receiver input, UP slot, and positive
rounded coordinator observation. -/
private theorem actual_positive_entry_physical_call
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (hchronological : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val))
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hentry : entry ∈ AffineBatchDecoder.positives p
      (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i)
      (records.map fun record => record.input.time)) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate),
      record ∈ records ∧
      record.input.time = entry.time ∧
      record.output.coordinator.up = some diagnostic ∧
      diagnostic.input.selectedFollower = i ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
      diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger ∧
      diagnostic.input.slot = PublicDiscreteDraws.upSlot ∧
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((record.input.rows record.input.selected).2 record.input.time).1 = some (1, i) ∧
      0 < CoordinatorUpReception.roundedObservationValue p diagnostic.input.ownObservation ∧
      ReferenceActiveAffinePositiveTest.upPositive record.input = true ∧
      diagnostic.input.time = record.input.time ∧
      diagnostic.input.affineSample =
        ((record.input.rows record.input.selected).2 record.input.time).2
          (1, i) ∧
      diagnostic.input.ownObservation =
        (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) := by
  classical
  have hpositive :=
    (AffineBatchDecoder.mem_positives_iff p
      (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i)
      (records.map fun record => record.input.time) entry).mp hentry
  obtain ⟨record, hrecord, hrecordTime⟩ := List.mem_map.mp hpositive.1
  have htrace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record
    records i hchronological record hrecord
  have hfocalEligible : AffineBatchDecoder.eligible
      (ReferenceCoordinatorUpIntervalWindow.recordFocalInput record i) := by
    rw [← htrace, hrecordTime]
    exact hpositive.2.1
  obtain ⟨diagnostic, hdiagnostic, hselected⟩ :
      ∃ diagnostic, record.output.coordinator.up = some diagnostic ∧
        diagnostic.input.selectedFollower = i := by
    cases hcall : record.output.coordinator.up with
    | none =>
        simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hcall,
          ReferenceCoordinatorUpIntervalWindow.administrativeNoCallInput,
          AffineBatchDecoder.eligible] at hfocalEligible
    | some diagnostic =>
        by_cases hsel : diagnostic.input.selectedFollower = i
        · exact ⟨diagnostic, rfl, hsel⟩
        · simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hcall, hsel,
            ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput,
            AffineBatchDecoder.eligible] at hfocalEligible
  have htraceInput : AffineBatchDecoder.eligible
      (CoordinatorUpReception.roundInput diagnostic.input) := by
    have hround : ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i
        entry.time = CoordinatorUpReception.roundInput diagnostic.input := by
      calc
        ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i entry.time =
            ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i record.input.time := by
              rw [hrecordTime]
        _ = ReferenceCoordinatorUpIntervalWindow.recordFocalInput record i := htrace
        _ = CoordinatorUpReception.roundInput diagnostic.input := by
              simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hdiagnostic,
                hselected, ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput]
    rw [← hround]
    exact hpositive.2.1
  obtain ⟨ledger, hphysical⟩ :=
    ReferenceCoordinatorUpIntervalWindow.record_retained_up_actual_call
      record diagnostic hdiagnostic
  have hsite := hphysical.1
  have hcheck := hphysical.2.1
  have hinput := hphysical.2.2.1
  have hdiagTime := hphysical.2.2.2.2.1
  have hselectedIndex := hphysical.2.2.2.2.2.1
  have hsample := hphysical.2.2.2.2.2.2.1
  have hownObservation := hphysical.2.2.2.2.2.2.2.1
  have hgate : CoordinatorUpReception.receptionGate diagnostic.input :=
    (CoordinatorUpReception.roundInput_selected_iff_gate diagnostic.input).mp
      htraceInput.1
  have hslot : PublicDiscreteDraws.slotDraw
      ((record.input.rows record.input.selected).2 record.input.time).1 =
        PublicDiscreteDraws.upSlot := by
    rw [hinput] at hgate
    simpa [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtControl,
      ReferenceActivePhysicalStep.RoundInput.row] using hgate.2.1
  have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      ((record.input.rows record.input.selected).2 record.input.time).1 = i := by
    rw [← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
    exact hselectedIndex.symm.trans hselected
  have hchannelFollower : CoordinatorUpMeasurability.selectedChannelFollower
      ((record.input.rows record.input.selected).2 record.input.time) = i := by
    apply Fin.ext
    rw [CoordinatorUpMeasurability.selectedChannelFollower_val,
      ← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
    simpa only [ContinuousLearningRows.d] using congrArg Fin.val
      (hselectedIndex.symm.trans hselected)
  have hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p
      ((record.input.rows record.input.selected).2 record.input.time).1 = some (1, i) := by
    rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _ hslot, hdraw]
    rfl
  have hpositiveObservation :
      0 < CoordinatorUpReception.roundedObservationValue p diagnostic.input.ownObservation :=
    htraceInput.2.2
  have hrecordPositive : ReferenceActiveAffinePositiveTest.upPositive record.input = true := by
    rw [ReferenceActiveAffinePositiveTest.record_upPositive, hdiagnostic]
    simp [ReferenceActiveAffinePositiveTest.upDiagnosticPositive, htraceInput]
  have hsample' : diagnostic.input.affineSample =
      ((record.input.rows record.input.selected).2 record.input.time).2
        (1, i) := by
    simpa [hchannelFollower] using hsample
  exact ⟨record, diagnostic, ledger, hrecord, hrecordTime, hdiagnostic,
    hselected, hsite, hcheck, hinput, hgate.2.1, hchannel,
    hpositiveObservation, hrecordPositive, hdiagTime, hsample', hownObservation⟩

/-- A known solution rules out an inconsistent completed batch.  The solver
therefore either returns that unique word or returns `none` with two distinct
solutions, the actual ambiguity case. -/
private theorem batch_output_matches_or_ambiguous
    {B : ℕ} (batch : List (AffineBatchDecoder.Entry p.T B))
    (word : AffineChannelLaw.Word B)
    (hsolution : AffineBatchDecoder.satisfies
      (AffineBatchDecoder.samples batch) word) :
    AffineBatchDecoder.batchOutput batch = some word ∨
      (AffineBatchDecoder.batchOutput batch = none ∧
        ∃ left right : AffineChannelLaw.Word B,
          left ≠ right ∧
          AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) left ∧
          AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) right) := by
  classical
  by_cases hunique : ∀ other, AffineBatchDecoder.satisfies
      (AffineBatchDecoder.samples batch) other → other = word
  · left
    apply (AffineBatchDecoder.batchOutput_eq_some_iff batch word).2
    refine ⟨(AffineBatchDecoder.satisfies_samples_iff batch word).mp hsolution, ?_⟩
    intro other hother
    exact hunique other ((AffineBatchDecoder.satisfies_samples_iff batch other).mpr hother)
  · right
    have hnone : AffineBatchDecoder.batchOutput batch = none := by
      cases houtput : AffineBatchDecoder.batchOutput batch with
      | none => rfl
      | some other =>
          have houtput' :=
            (AffineBatchDecoder.batchOutput_eq_some_iff batch other).mp houtput
          have hwordEq : word = other := houtput'.2 word
            ((AffineBatchDecoder.satisfies_samples_iff batch word).mp hsolution)
          have hall : ∀ candidate,
              AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) candidate →
                candidate = word := by
            intro candidate hcandidate
            calc
              candidate = other := houtput'.2 candidate
                ((AffineBatchDecoder.satisfies_samples_iff batch candidate).mp hcandidate)
              _ = word := hwordEq.symm
          exact False.elim (hunique hall)
    have hsolver : AffineBatchDecoder.solve (AffineBatchDecoder.samples batch) = none := by
      simpa [AffineBatchDecoder.batchOutput] using hnone
    rcases (AffineBatchDecoder.solve_eq_none_iff_empty_or_ambiguous
      (AffineBatchDecoder.samples batch)).mp hsolver with hempty | hambiguous
    · exact False.elim (hempty word hsolution)
    · rcases hambiguous with ⟨left, right, hleft, hright, hne⟩
      exact ⟨hnone, left, right, hne, hleft, hright⟩



private theorem run_prefix_records
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n ≤ total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
      (by omega) hmode).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
        hspan hmode).records.take n := by
  obtain ⟨suffix, hprefix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start n (total - n) (by omega) hmode
  have hadd : n + (total - n) = total := Nat.add_sub_of_le hn
  simp only [hadd] at hprefix
  rw [hprefix, List.take_append_of_le_length (by
    rw [ReferenceActivePhysicalHorizon.run_record_count])]
  symm
  apply List.take_of_length_le
  rw [ReferenceActivePhysicalHorizon.run_record_count]

private theorem collectionWindow_prefix
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w : ℕ) :
    ReferenceCollectionPhaseHistory.collectionWindow records w <+: records.drop w := by
  unfold ReferenceCollectionPhaseHistory.collectionWindow
  obtain ⟨suffix, hsuffix⟩ := List.takeWhile_prefix
    (l := records.drop (w + 1))
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  refine ⟨suffix, ?_⟩
  rw [List.append_assoc, hsuffix]
  simp

private theorem prefix_slice_eq {α : Type} (xs ys : List α)
    (w f b : ℕ) (hprefix : xs <+: ys.drop w)
    (hfb : f ≤ b) (hb : b ≤ xs.length) :
    (xs.drop f).take (b - f) = (ys.take (w + b)).drop (w + f) := by
  have htake : xs.take b = (ys.drop w).take b := by
    obtain ⟨suffix, hsuffix⟩ := hprefix
    rw [← hsuffix, List.take_append_of_le_length hb]
  calc
    (xs.drop f).take (b - f) = (xs.take b).drop f := by
      rw [List.take_drop, Nat.add_sub_of_le hfb]
    _ = ((ys.drop w).take b).drop f := congrArg (fun zs => zs.drop f) htake
    _ = (ys.take (w + b)).drop (w + f) := by
      rw [List.take_drop, List.drop_drop]

private theorem slice_member_index {α : Type} (xs : List α)
    (f b : ℕ) (record : α)
    (hrecord : record ∈ (xs.drop f).take (b - f)) :
    ∃ k : Fin xs.length, f ≤ k.val ∧ k.val < b ∧ xs[k.val] = record := by
  obtain ⟨q, hq, hrecord⟩ := List.mem_iff_getElem.mp hrecord
  have hqbound : q < b - f ∧ q < xs.length - f := by
    simpa only [List.length_take, List.length_drop, lt_min_iff] using hq
  have hk : f + q < xs.length := by omega
  refine ⟨⟨f + q, hk⟩, Nat.le_add_right f q, by change f + q < b; omega, ?_⟩
  simpa only [List.getElem_take, List.getElem_drop] using hrecord

/-- At an actual unoccupied UP choice, logging and DOWN are no-ops and both
lifecycle stages preserve the same local state and memory. This is a local
physical-output guard, with no later survival premise. -/
private theorem selected_up_unoccupied_follower_preserved
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice r i).configuration =
      .ordinary state memory)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid state)
    (hstatus : state.status = .unoccupied)
    (hslot : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
      PublicDiscreteDraws.upSlot) :
    let choice := ReferenceFollowerFixedReply.actualChoice r i
    let own := (ReferenceActivePhysicalStep.prepare r.input).feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    ActiveFollowerLogging.checkedLogging choice.follower choice.row choice.activation
      choice.time (choice.arm, own) state = .ok state ∧
    (ReferenceDownReception.referenceDownCut p
      (ReferenceActivePhysicalStep.prepare r.input).coordinator.downView
      choice.follower choice.row choice.time own rate state).outcome =
        .skipped state .notSelectedDown ∧
    DeclaredFollowerLocalRound.releaseAndFinish rate choice.follower choice.row
      choice.time own state memory state = .ok (state, memory) ∧
    r.output.next.followers i = .ordinary state memory := by
  classical
  intro choice own
  obtain ⟨hrow, hfollower, htime⟩ := ReferenceFollowerFixedReply.actualChoice_alignment r i
  have hslotChoice : PublicDiscreteDraws.slotDraw (choice.row.2 choice.time).1 =
      PublicDiscreteDraws.upSlot := by rw [hrow, htime]; exact hslot
  have hnotData : PublicDiscreteDraws.slotDraw (choice.row.2 choice.time).1 ≠
      PublicDiscreteDraws.dataSlot := by rw [hslotChoice]; decide
  have hnotDown : ¬ ActiveFollowerDownAcceptance.downSelected p
      choice.follower choice.row choice.time := by
    intro h
    have := h.1
    rw [hslotChoice] at this
    contradiction
  have hlogAt : ReferencePrelaunchFollower.logAt choice.follower choice.row
      choice.activation choice.time (choice.arm, own) = [] := by
    apply ite_eq_right
    intro h
    exact hnotData ((ReferencePrelaunchFollower.loggingTestsPass_iff _ _ _ _ _).mp h).2.1
  have hupdate : ActiveFollowerLogging.loggingUpdate choice.follower choice.row
      choice.activation choice.time (choice.arm, own) state = state := by
    unfold ActiveFollowerLogging.loggingUpdate
    split <;> simp [hlogAt]
  have hlogging : ActiveFollowerLogging.checkedLogging choice.follower choice.row
      choice.activation choice.time (choice.arm, own) state = .ok state := by
    simp only [ActiveFollowerLogging.checkedLogging, dite_eq_left hvalid.2.1, hupdate]
  have hdown : (ReferenceDownReception.referenceDownCut p
      (ReferenceActivePhysicalStep.prepare r.input).coordinator.downView
      choice.follower choice.row choice.time own rate state).outcome =
        .skipped state .notSelectedDown := by
    simp only [ReferenceDownReception.referenceDownCut, dite_eq_right hnotDown]
  have hrecord : (ReferenceActivePhysicalStep.recordFollower
      (ReferenceActivePhysicalStep.prepare r.input).coordinator.downView
      choice.follower choice.row choice.activation choice.time choice.active
      choice.arm own state).result = .ok state := by
    simp [ReferenceActivePhysicalStep.recordFollower, hstatus, hlogging,
      hdown, DeclaredFollowerLocalRound.consumeDownResult]
  have hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate choice.follower
      choice.row choice.time own state memory state = .ok (state, memory) := by
    rw [DeclaredFollowerLocalRound.releaseAndFinish,
      ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta choice.follower
        choice.time _ own state state hstatus]
    simp only [ActiveFollowerLifecycle.finishRound_unoccupied rate.eta choice.time
      choice.row state memory hvalid hstatus]
  have houtput := (ReferenceActivePhysicalStep.finishFollower_success
    (ReferenceActivePhysicalStep.prepare r.input).coordinator.downView choice own
    state state state memory memory hchoice hrecord hfinish).1
  refine ⟨hlogging, hdown, hfinish, ?_⟩
  have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  change r.output.next.followers i = _
  rw [r.output_eq]
  change (ReferenceActivePhysicalStep.finishFollower _
    ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i) own).configuration = _
  simpa only [choice, ReferenceFollowerFixedReply.actualChoice, hprep] using houtput



/-- Align the public saved completed-cut theorem with an already identified
actual slice and its inherited channel. The launch seed is used only at the
original run boundary; the formation channel is preserved in full. -/
private theorem saved_interval_transition
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start b hspan hmode).finalState.coordinator ≠ .dagger)
    (i : Fin (p.m - 1))
    (hseed : AffineBatchDecoder.collected (initial.upDecoderBank i) = [])
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hrecords : records = ReferenceCoordinatorUpIntervalWindow.intervalRecords
      initial rows selected rewards start a b hspan hmode)
    (channel final : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hchannel : channel = (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start a (by omega) hmode).finalState.upDecoderBank i)
    (hfinal : final = (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start b hspan hmode).finalState.upDecoderBank i) :
    let times := records.map (fun record => record.input.time)
    let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i
    let positive := AffineBatchDecoder.positives p trace times
    let first := channel.pending ++ positive.take
      (AffineBatchDecoder.quota p - channel.pending.length)
    let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
    positive.length = AffineBatchDecoder.quota p - channel.pending.length +
      AffineBatchDecoder.quota p →
    ∃ (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      first.length = AffineBatchDecoder.quota p ∧
      window.length = AffineBatchDecoder.quota p ∧
      window.Pairwise (fun x y => x.time.val < y.time.val) ∧
      last ∈ window ∧ AffineBatchDecoder.decisionTime window = some last.time ∧
      record ∈ records ∧ record.input.time = last.time ∧
      record.output.coordinator.up = some diagnostic ∧
      diagnostic.input.selectedFollower = i ∧ diagnostic.input.time = record.input.time ∧
      diagnostic.input.upDecoderBank = record.input.state.upDecoderBank ∧
      (diagnostic.input.upDecoderBank i).pending ++ [last] = window ∧
      CoordinatorUpReception.decoderTransition diagnostic.input =
        ({ pending := [], completed := channel.completed ++ [first, window] },
          AffineBatchDecoder.batchOutput window) ∧
      diagnostic.decoderAfter =
        { pending := [], completed := channel.completed ++ [first, window] } ∧
      diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
      final = diagnostic.decoderAfter := by
  subst records channel final
  intro times trace positive first window hcount
  have hcut := ReferenceCoordinatorUpWindowCompletedCut.run_interval_saved_completed_cut
    initial rows selected rewards start a b hab hspan hmode hinitial hordinary i hseed hcount
  obtain ⟨firstCut, last, _index, record, diagnostic, hfirstCut, hfirstLen,
    hwindowLen, hwindowChron, hlastWindow, hdecision, _hindex,
    hrecordMem, hrecordTime, hdiagnostic, hselected, hdiagTime, hlastEntry,
    _hlastSample, _hphysical, _hconnected, _hrecordBank, hdiagBank, hbefore,
    happend, _hcleared, _hcompletedCut, hafter, _hrawTransition, hraw,
    htransition, hrunCut, hfinalCut⟩ := hcut
  have hfirstEq : firstCut = first := hfirstCut
  subst firstCut
  have hafterBank : diagnostic.decoderAfter =
      { pending := [], completed :=
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
          (by omega) hmode).finalState.upDecoderBank i).completed ++ [first, window] } := by
    rw [hafter, htransition]
    rfl
  have happendLast : (diagnostic.input.upDecoderBank i).pending ++ [last] = window := by
    rw [← hbefore, hlastEntry]
    exact happend
  exact ⟨last, record, diagnostic, hfirstLen, hwindowLen, hwindowChron,
    hlastWindow, hdecision, hrecordMem, hrecordTime, hdiagnostic, hselected,
    hdiagTime, hdiagBank, happendLast, htransition, hafterBank, hraw,
    hfinalCut.symm.trans (hrunCut.trans hafterBank.symm)⟩

private theorem ordinary_successor_channel
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant record.input.state)
    (hordinary : record.output.next.coordinator ≠ .dagger)
    (i : Fin (p.m - 1)) (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (hselected : diagnostic.input.selectedFollower = i)
    (hbank : diagnostic.input.upDecoderBank = record.input.state.upDecoderBank)
    (hafter : diagnostic.decoderAfter =
      (CoordinatorUpReception.decoderTransition diagnostic.input).1) :
    record.output.next.upDecoderBank i = diagnostic.decoderAfter := by
  rw [ReferenceCoordinatorUpDecoderReplay.ordinaryRecord_upDecoderBank_replay
    record hinvariant hordinary, hdiagnostic]
  simp only [ReferenceCoordinatorUpDecoderReplay.replayOption, Option.elim,
    ReferenceCoordinatorUpDecoderReplay.replayOne,
    ReferenceCoordinatorUpDecoderReplay.retainedUpFollower, hselected,
    Function.update_self]
  rw [← hbank]
  have hstep := ReferenceCoordinatorUpDecoderReplay.decodeStep_constantInput_of_current_eq
    (CoordinatorUpReception.traceAt diagnostic.input) (diagnostic.input.upDecoderBank i)
    diagnostic.input.time diagnostic.input rfl
  have hafter' : (AffineBatchDecoder.decodeStep p
      (CoordinatorUpReception.traceAt diagnostic.input) (diagnostic.input.upDecoderBank i)
      diagnostic.input.time).1 = diagnostic.decoderAfter := by
    simpa only [CoordinatorUpReception.decoderTransition, hselected] using hafter.symm
  exact (congrArg Prod.fst hstep).symm.trans hafter'


private theorem actual_positive_record_flags
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (hchrono : records.Pairwise (fun a b => a.input.time.val < b.input.time.val))
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hentry : entry ∈ AffineBatchDecoder.positives p
      (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i)
      (records.map (fun r => r.input.time)))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ records) (htime : record.input.time = entry.time)
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : record.output.coordinator.up = some diagnostic) :
    PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
      PublicDiscreteDraws.upSlot ∧
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i ∧
    ReferenceSelectedAffinePairLaw.selectedChannel p
      ((record.input.rows record.input.selected).2 record.input.time).1 = some (1, i) ∧
    ReferenceActiveAffinePositiveTest.upPositive record.input = true ∧
    0 < CoordinatorUpReception.roundedObservationValue p diagnostic.input.ownObservation ∧
    diagnostic.input.affineSample =
      ((record.input.rows record.input.selected).2 record.input.time).2 (1, i) ∧
    diagnostic.input.ownObservation =
      (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback
        (ActiveRoundActions.coordinator p.two_le_m) := by
  obtain ⟨physicalRecord, physicalDiagnostic, physicalLedger, hphysicalMem, hphysicalTime,
    hphysicalDiagnostic, hselected, _hsite, _hcheck, hinput, hslotInput, hchannel,
    hpositive, hupPositive, _htime, hsample, hobs⟩ :=
      actual_positive_entry_physical_call records i hchrono entry hentry
  have hrecordEq : physicalRecord = record := by
    have htimes : (records.map (fun r => r.input.time.val)).Nodup :=
      (List.pairwise_map.mpr hchrono).nodup
    exact List.inj_on_of_nodup_map htimes hphysicalMem hrecord
      (congrArg Fin.val (hphysicalTime.trans htime.symm))
  subst physicalRecord
  have hdiagEq : physicalDiagnostic = diagnostic :=
    Option.some.inj (hphysicalDiagnostic.symm.trans hdiagnostic)
  subst physicalDiagnostic
  have hslot : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
      PublicDiscreteDraws.upSlot := by
    rw [hinput] at hslotInput
    exact hslotInput
  have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i := by
    obtain ⟨ledger, _hsite, _hcheck, _hinput, _hafter, _htime,
      hselectedIndex, _⟩ :=
      ReferenceCoordinatorUpIntervalWindow.record_retained_up_actual_call record diagnostic hdiagnostic
    rw [← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
    exact hselectedIndex.symm.trans hselected
  exact ⟨hslot, hdraw, hchannel, hupPositive, hpositive, hsample, hobs⟩


/-- Locate the actual deciding collection index and crop away any positive-free
suffix. The history input is literal collected-history conservation, supplied
by the actual run replay; it is not a threshold or survival assumption. -/
private theorem actual_interval_deciding_cut
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count w ell : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (i : Fin (p.m - 1))
    (hseed : AffineBatchDecoder.collected (initial.upDecoderBank i) = [])
    (B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hlen : w + ell ≤ count) (hBlength : ell ≤ B.length)
    (hprefix : B <+: (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records.drop w)
    (f b : ℕ) (hfb : f ≤ b) (hb : b ≤ ell) :
    let X (t : ℕ) (hwt : w + t ≤ count) :=
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (w + t)
        (by omega) hmode).finalState
    (∀ k : Fin ell,
      (B[k.val]'(Nat.lt_of_lt_of_le k.isLt hBlength)).output.next =
        X (k.val + 1) (by omega)) →
    (∀ (t : ℕ) (hft : f ≤ t) (ht : t ≤ b),
      let S := (B.drop f).take (t - f)
      let times := S.map (fun r => r.input.time)
      let P := AffineBatchDecoder.positives p
        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i) times
      AffineBatchDecoder.collected ((X t (by omega)).upDecoderBank i) =
        AffineBatchDecoder.collected ((X f (by omega)).upDecoderBank i) ++ P ∧
      times.Pairwise (fun a b => a.val < b.val) ∧
      ((X f (by omega)).upDecoderBank i).pending.length < AffineBatchDecoder.quota p) →
    (X b (by omega)).coordinator ≠ .dagger →
    let S := (B.drop f).take (b - f)
    let times := S.map (fun r => r.input.time)
    let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
    let P := AffineBatchDecoder.positives p tr times
    let ch := (X f (by omega)).upDecoderBank i
    let Q := AffineBatchDecoder.quota p
    let first := ch.pending ++ P.take (Q - ch.pending.length)
    let window := P.drop (Q - ch.pending.length)
    P.length = Q - ch.pending.length + Q →
    ∃ (q : Fin B.length) (hqb : q.val < b)
      (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      B[q.val] = record ∧ 0 < q.val ∧ f ≤ q.val ∧
      first.length = Q ∧ window.length = Q ∧ ch.pending.length < Q ∧
      window.Pairwise (fun a b => a.time.val < b.time.val) ∧
      last ∈ window ∧ AffineBatchDecoder.decisionTime window = some last.time ∧
      record.input.time = last.time ∧ record.output.coordinator.up = some diagnostic ∧
      diagnostic.input.selectedFollower = i ∧ diagnostic.input.time = record.input.time ∧
      PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 = PublicDiscreteDraws.upSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (record.input.row.2 record.input.time).1 = i ∧
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((record.input.rows record.input.selected).2 record.input.time).1 = some (1, i) ∧
      ReferenceActiveAffinePositiveTest.upPositive record.input = true ∧
      0 < CoordinatorUpReception.roundedObservationValue p diagnostic.input.ownObservation ∧
      diagnostic.input.affineSample =
        ((record.input.rows record.input.selected).2 record.input.time).2 (1, i) ∧
      diagnostic.input.ownObservation =
        (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) ∧
      diagnostic.input.upDecoderBank = record.input.state.upDecoderBank ∧
      (diagnostic.input.upDecoderBank i).pending ++ [last] = window ∧
      CoordinatorUpReception.decoderTransition diagnostic.input =
        ({ pending := [], completed := ch.completed ++ [first, window] },
          AffineBatchDecoder.batchOutput window) ∧
      diagnostic.decoderAfter = { pending := [], completed := ch.completed ++ [first, window] } ∧
      diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
      (X (q.val + 1) (by omega)).upDecoderBank i = diagnostic.decoderAfter ∧
      (X b (by omega)).upDecoderBank i = diagnostic.decoderAfter ∧
      AffineBatchDecoder.positives p
        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
          ((B.drop f).take (q.val + 1 - f)) i)
        (((B.drop f).take (q.val + 1 - f)).map (fun r => r.input.time)) = P ∧
      record.output.next.coordinator ≠ .dagger := by
  intro X hEndpoint hhistory hordinary S times tr P ch Q first window hcount
  have hwB : w + b ≤ count := (Nat.add_le_add_left hb w).trans hlen
  have hspanB : start + (w + b) ≤ p.T := (Nat.add_le_add_left hwB start).trans hspan
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start
    (w + b) hspanB hmode
  have hfullRecords := run_prefix_records initial rows selected rewards start count
    hspan hmode (w + b) hwB
  have hSinterval : S = ReferenceCoordinatorUpIntervalWindow.intervalRecords
      initial rows selected rewards start (w + f) (w + b) hspanB hmode := by
    change S = full.records.drop (w + f)
    rw [hfullRecords]
    exact prefix_slice_eq B _ w f b hprefix hfb (hb.trans hBlength)
  obtain ⟨last, record, diagnostic, hfirstLen, hwindowLen, hwindowChron,
    hlastWindow, hdecision, hrecordMem, hrecordTime, hdiagnostic, hselected,
    hdiagTime, hdiagBank, happendLast, htransition, hafterBank, hraw, hendBank⟩ :=
      saved_interval_transition initial rows selected rewards start (w + f) (w + b)
        (Nat.add_le_add_left hfb w) hspanB hmode hinitial hordinary i hseed S hSinterval
        ch ((X b hwB).upDecoderBank i) rfl rfl hcount
  obtain ⟨q, hfq, hqb, hrecordB⟩ := slice_member_index B f b record hrecordMem
  have hqEll : q.val < ell := Nat.lt_of_lt_of_le hqb hb
  have hq1Ell : q.val + 1 ≤ ell := Nat.succ_le_of_lt hqEll
  have hwq1 : w + (q.val + 1) ≤ count := (Nat.add_le_add_left hq1Ell w).trans hlen
  have hqNext : record.output.next = X (q.val + 1) hwq1 :=
    (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      r.output.next) hrecordB).symm.trans (hEndpoint ⟨q.val, hqEll⟩)
  have hrecordFull : record ∈ full.records := by
    apply List.mem_of_mem_drop
    change record ∈ ReferenceCoordinatorUpIntervalWindow.intervalRecords
      initial rows selected rewards start (w + f) (w + b) hspanB hmode
    rw [← hSinterval]
    exact hrecordMem
  have hfacts := ReferenceCoordinatorUpIntervalWindow.run_interval_cut initial rows selected
    rewards start (w + f) (w + b) (Nat.add_le_add_left hfb w) hspanB hmode hinitial hordinary
  have hqInvariant := hfacts.2.2.2.2.2.1 record hrecordFull
  have hqOrdinary := hfacts.2.2.2.2.2.2 record hrecordFull
  have hsuccessor : (X (q.val + 1) hwq1).upDecoderBank i = diagnostic.decoderAfter := by
    have hbank := ordinary_successor_channel record hqInvariant hqOrdinary i diagnostic
      hdiagnostic hselected hdiagBank (by rw [htransition, hafterBank])
    exact (congrArg (fun x : ReferenceActivePhysicalStep.State p rate =>
      x.upDecoderBank i) hqNext).symm.trans hbank
  have hPcrop : AffineBatchDecoder.positives p
      (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
        ((B.drop f).take (q.val + 1 - f)) i)
      (((B.drop f).take (q.val + 1 - f)).map (fun r => r.input.time)) = P := by
    have hcrop := hhistory (q.val + 1) (hfq.trans (Nat.le_succ q.val)) (Nat.succ_le_of_lt hqb)
    have hwhole := hhistory b hfb (Nat.le_refl b)
    have heq : AffineBatchDecoder.collected ((X (q.val + 1) hwq1).upDecoderBank i) =
        AffineBatchDecoder.collected ((X b hwB).upDecoderBank i) := by rw [hsuccessor, hendBank]
    rw [hcrop.1, hwhole.1] at heq
    exact List.append_right_injective _ heq
  have hpendingSmall : ch.pending.length < Q := (hhistory b hfb (Nat.le_refl b)).2.2
  have hqpos : 0 < q.val := by
    have hQpos : 0 < Q := AffineBatchDecoder.quota_pos p
    have hlength : P.length ≤ q.val + 1 - f := by
      rw [← hPcrop]
      unfold AffineBatchDecoder.positives
      rw [List.length_map]
      exact (List.length_filter_le _ _).trans (by simp)
    omega
  have hchrono : S.Pairwise (fun a b => a.input.time.val < b.input.time.val) :=
    (List.pairwise_map (f := fun r : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate) => r.input.time)
      (R := fun a b : Fin p.T => a.val < b.val)).mp (hhistory b hfb (Nat.le_refl b)).2.1
  have hlastP : last ∈ P := List.mem_of_mem_drop hlastWindow
  obtain ⟨hslot, hdraw, hchannel, hupPositive, hpositive, hsample, hobs⟩ :=
    actual_positive_record_flags S i hchrono last hlastP record hrecordMem hrecordTime
      diagnostic hdiagnostic
  exact ⟨q, hqb, last, record, diagnostic, hrecordB, hqpos, hfq, hfirstLen,
    hwindowLen, hpendingSmall, hwindowChron, hlastWindow, hdecision, hrecordTime,
    hdiagnostic, hselected, hdiagTime, hslot, hdraw, hchannel, hupPositive,
    hpositive, hsample, hobs, hdiagBank, happendLast, htransition, hafterBank,
    hraw, hsuccessor, hendBank, hPcrop, hqOrdinary⟩


private theorem actual_collection_choice_at
    (B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) (q : Fin B.length)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : B[q.val] = record) :
    ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice B i q =
      ReferenceFollowerFixedReply.actualChoice record i := by
  unfold ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice
    ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord
  rw [hrecord]


/-- Match the actual filtered receiver to a known solution. A `none` output
with that solution has two distinct solvers; inconsistency is impossible. -/
private theorem receiver_matching_or_ambiguous
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (tail : ReferenceCollectionPhaseHistory.Tail r.input)
    (hstate : r.input.state.coordinator = .collection payload ledger saved)
    (htail : ReferenceCollectionPhaseHistory.executedTail r.input = some tail)
    (hordinary : r.output.next.coordinator ≠ .dagger)
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (L : ReferenceActivePhysicalStep.Ledger rate)
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L)
    (hdiagnostic : r.output.coordinator.up = some diagnostic)
    (hsender : ReferenceActivePhysicalStep.upSenderIndex r.input = i)
    (haccept : CoordinatorCollectionLedger.acceptUpCheck L i U = true)
    (hexpected : ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
      some (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U))
    (window : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hraw : diagnostic.raw = AffineBatchDecoder.batchOutput window)
    (hsolution : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window)
      (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U)) :
    let word := ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U
    diagnostic.expected = some word ∧
    ((diagnostic.raw = some word ∧
      ReferenceCollectionPhaseHistory.filteredParsed r.input L = some U ∧
      ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
        (bank : CoordinatorUpReception.UpDecoderBank p),
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare r.input) L).result = .success (decoded, bank) ∧
        ReferenceCollectionPhaseHistory.AcceptedUp r.input i U) ∨
      (diagnostic.raw = none ∧
        ∃ left right : AffineChannelLaw.Word (AffineBatchDecoder.width p),
          left ≠ right ∧
          AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) left ∧
          AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) right)) := by
  intro word
  have hwordEq : word = ActiveFollowerArmChoice.offeredUpWord rate.eta U := by
    unfold word ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord
      ActiveFollowerArmChoice.offeredUpWord
    have hcodec := ReferenceUpReception.ledgerCodecParams_eq_followerCodecParams rate
    cases hcodec
    rfl
  obtain ⟨recordingR, LR, diagnosticR, _hrecordingR, _hstartR, hsiteR, _hcheckR,
    hdiagR, _hinputR, _hreceptionR, _hnoninvalidR, _hfinishedR, _hafterR,
    _hrawR, _hparsedR, _hlocalR, hexpectedR, _hrawMatchesR, _hbankR,
    _htimeR, _hsampleR, _hobsR, _hwrongR, hmatching⟩ :=
      ReferenceCollectionUpReceiverLocal.actual_collection_up_receiver_matching_word
        r payload ledger saved tail hstate htail hordinary
  have hledgerEq : LR = L := Option.some.inj (hsiteR.symm.trans hsite)
  subst LR
  have hdiagnosticREq : diagnosticR = diagnostic := Option.some.inj (hdiagR.symm.trans hdiagnostic)
  subst diagnosticR
  have hdiagExpected : diagnostic.expected = some word := hexpectedR.trans hexpected
  refine ⟨hdiagExpected, ?_⟩
  rcases batch_output_matches_or_ambiguous window word hsolution with hsome | ⟨hnone, hambiguous⟩
  · have hrawWord : diagnostic.raw = some word := hraw.trans hsome
    have hmatched := hmatching U (by rw [← hwordEq]; exact hrawWord)
      (by rw [← hwordEq]; exact hdiagExpected) (by rw [hsender]; exact haccept)
    rcases hmatched with ⟨hparsed, _hparsedD, _hlocal, _hrawMatches,
      _hwrong, decoded, bank, hreceived, haccepted⟩
    left
    exact ⟨hrawWord, hparsed, decoded, bank, hreceived, by simpa only [hsender] using haccepted⟩
  · exact Or.inr ⟨hraw.trans hnone, hambiguous⟩


/-- Adapt A's saved-bank clauses with the state function kept as a typed
parameter. The original slice, channel, and completed history stay literal. -/
private theorem actual_saved_slice_histories
    (start w count ell f n : ℕ) (hlen : w + ell ≤ count) (hn : n < ell)
    (X : (t : ℕ) → w + t ≤ count → ReferenceActivePhysicalStep.State p rate)
    (whole B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (hsaved : ∀ (b : ℕ) (hfb : f ≤ b) (hbn : b ≤ n + 1),
      let S := (B.drop f).take (b - f)
      let times := S.map (fun record => record.input.time)
      let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
      let P := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i
      (X b (by omega)).upDecoderBank =
        ReferenceCoordinatorUpDecoderReplay.replay (X f (by omega)).upDecoderBank
          (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics S) ∧
      AffineBatchDecoder.run p tr times ((X f (by omega)).upDecoderBank i) =
        (X b (by omega)).upDecoderBank i ∧
      AffineBatchDecoder.collected ((X b (by omega)).upDecoderBank i) =
        AffineBatchDecoder.collected ((X f (by omega)).upDecoderBank i) ++ P ∧
      AffineBatchDecoder.positives p tr times = P ∧
      times.Pairwise (fun a b => a.val < b.val) ∧
      ((X f (by omega)).upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
      ∀ e, e ∈ ((X f (by omega)).upDecoderBank i).pending →
        e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
          (whole.take (w + f)) i ∧
        e.time.val < start + w + f ∧
        ∀ t, t ∈ times → e.time.val < t.val) :
    ∀ (t : ℕ) (hft : f ≤ t) (ht : t ≤ n + 1),
      let S := (B.drop f).take (t - f)
      let times := S.map (fun record => record.input.time)
      let P := AffineBatchDecoder.positives p
        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i) times
      AffineBatchDecoder.collected ((X t (by omega)).upDecoderBank i) =
        AffineBatchDecoder.collected ((X f (by omega)).upDecoderBank i) ++ P ∧
      times.Pairwise (fun a b => a.val < b.val) ∧
      ((X f (by omega)).upDecoderBank i).pending.length < AffineBatchDecoder.quota p := by
  intro t hft ht S times P
  have h := hsaved t hft ht
  refine ⟨?_, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  change AffineBatchDecoder.collected ((X t (by omega)).upDecoderBank i) =
    AffineBatchDecoder.collected ((X f (by omega)).upDecoderBank i) ++
      AffineBatchDecoder.positives p
        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i) times
  rw [h.2.2.2.1]
  exact h.2.2.1

private theorem prefix_record_coordinates
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count w : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hprefix : B <+: (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records.drop w) :
    (∀ q : Fin B.length,
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records[w + q.val]? =
        some B[q.val]) ∧
    ∀ q : Fin B.length, B[q.val].input.time.val = start + w + q.val := by
  let E := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode
  have hElen : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards start count hspan hmode
  have hindex (q : Fin B.length) : E.records[w + q.val]? = some B[q.val] := by
    have h := hprefix.getElem q.isLt
    have hq : q.val < (E.records.drop w).length := q.isLt.trans_le hprefix.length_le
    have hget : (E.records.drop w)[q.val]? = some B[q.val] := by
      rw [List.getElem?_eq_getElem hq, ← h]
    simpa only [List.getElem?_drop] using hget
  have hcalendar : E.records.map (fun r => r.input.time.val) =
      ReferenceActivePhysicalHorizon.calendar start count :=
    ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards start count hspan hmode
  refine ⟨hindex, ?_⟩
  intro q
  have hget := hindex q
  have hq : w + q.val < count := by
    have := (List.getElem?_eq_some_iff.mp hget).1
    omega
  have hmap := congrArg (fun xs : List ℕ => xs[w + q.val]?) hcalendar
  rw [List.getElem?_map, hget] at hmap
  simpa [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range', hq,
    Nat.add_assoc] using hmap

private theorem actual_launch_bank_invariant
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    ReferenceUpDecoderBankInvariant.upBankInvariant initial ∧
    ∀ i : Fin (p.m - 1), AffineBatchDecoder.collected (initial.upDecoderBank i) = [] := by
  intro initial
  obtain ⟨_, _, _, hfirstSeed, hbankSeed, _, _, _⟩ :=
    ReferenceFirstLaunchNumericalCell.actual_launch_seed rate source rewards C_star C_h hcross
  have hfirst : initial.coordinator = .first := by
    simpa [initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hfirstSeed
  have hbank : initial.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p := by
    simpa [initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState] using hbankSeed
  constructor
  · change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
      initial.coordinator initial.upDecoderBank
    rw [hfirst, hbank]
    exact ⟨CoordinatorUpReception.initialUpDecoderBank_wellFormed p, fun _ => rfl⟩
  · intro i
    simp [hbank, CoordinatorUpReception.initialUpDecoderBank,
      AffineBatchDecoder.initial, AffineBatchDecoder.collected]


/-- Shared physical coordinates and the genuine launch-bank seed for the
supplied actual dispatch. No dispatch or run is chosen by this adapter. -/
private theorem actual_dispatch_run_facts
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
      source rewards C_star C_h count hcross hspan hshort) :
    let out := d.stream
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    out.window = B ∧ out.ell ≤ B.length ∧ B <+: E.records.drop w ∧
    (∀ q : Fin B.length, E.records[w + q.val]? = some B[q.val]) ∧
    (∀ q : Fin B.length, B[q.val].input.time.val = s + w + q.val) ∧
    ReferenceUpDecoderBankInvariant.upBankInvariant initial ∧
    ∀ i : Fin (p.m - 1), AffineBatchDecoder.collected (initial.upDecoderBank i) = [] := by
  intro out E w s B initial
  have hWindow : out.window = B := out.windowIsActual
  have hBlength : out.ell ≤ B.length := hWindow ▸ out.withinWindow
  have hprefix : B <+: E.records.drop w := collectionWindow_prefix E.records w
  obtain ⟨hindex, htime⟩ := prefix_record_coordinates (p := p) (rate := rate)
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    s count w hspan
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1 B hprefix
  obtain ⟨hinitial, hseed⟩ := actual_launch_bank_invariant rate source rewards C_star C_h hcross
  exact ⟨hWindow, hBlength, hprefix, hindex, htime, hinitial, hseed⟩

/-- Compose the actual deciding transition, pure-word equations, and the
continuing local receiver. Every replay and receiver input below is supplied
from the same original run; no stopped quota or service premise is used. -/
public theorem actual_formed_query_deciding_receiver
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
      source rewards C_star C_h count hcross hspan hshort) :
    let out := d.stream
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let rows := source.1.2
    let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
    let whole := E.records
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let hmode := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    let ell := out.ell
    let payload := out.payload
    let saved := out.saved
    ∀ (hlen : w + ell ≤ count) (hBlength : ell ≤ B.length) (i : Fin (p.m - 1))
      (f n : ℕ) (hfn : f ≤ n) (hn : n < ell)
      (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
    let X (t : ℕ) (hwt : w + t ≤ count) :=
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (w + t)
        (Nat.le_trans (Nat.add_le_add_left hwt start) hspan) hmode).finalState
    (∀ (b : ℕ) (_hfb : f ≤ b) (_hbn : b ≤ n + 1),
      let S := (B.drop f).take (b - f)
      let times := S.map (fun r => r.input.time)
      let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
      let P := AffineBatchDecoder.positives p tr times
      let ch := (X f (by omega)).upDecoderBank i
      let Q := AffineBatchDecoder.quota p
      let window := P.drop (Q - ch.pending.length)
      P.length = Q - ch.pending.length + Q →
      (∀ e, e ∈ ch.pending → e ∉ window) ∧ P.length ≤ 2 * Q ∧
      ∀ e, e ∈ window → start + w + f ≤ e.time.val ∧ e.time.val < start + w + b ∧
        AffineBatchDecoder.equation e.sample
          (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U)) →
    (∀ k : Fin ell,
      (B[k.val]'(Nat.lt_of_lt_of_le k.isLt hBlength)).input.state = X k.val (by omega) ∧
      (B[k.val]'(Nat.lt_of_lt_of_le k.isLt hBlength)).output.next =
        X (k.val + 1) (by omega)) →
    (∀ (b : ℕ) (_hfb : f ≤ b) (hbn : b ≤ n + 1),
      let S := (B.drop f).take (b - f)
      let times := S.map (fun record => record.input.time)
      let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
      let P := ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries S i
      (X b (by omega)).upDecoderBank =
        ReferenceCoordinatorUpDecoderReplay.replay (X f (by omega)).upDecoderBank
          (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics S) ∧
      AffineBatchDecoder.run p tr times ((X f (by omega)).upDecoderBank i) =
        (X b (by omega)).upDecoderBank i ∧
      AffineBatchDecoder.collected ((X b (by omega)).upDecoderBank i) =
        AffineBatchDecoder.collected ((X f (by omega)).upDecoderBank i) ++ P ∧
      AffineBatchDecoder.positives p tr times = P ∧
      times.Pairwise (fun a b => a.val < b.val) ∧
      ((X f (by omega)).upDecoderBank i).pending.length < AffineBatchDecoder.quota p ∧
      ∀ e, e ∈ ((X f (by omega)).upDecoderBank i).pending →
        e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
          (whole.take (w + f)) i ∧
        e.time.val < start + w + f ∧
        ∀ t, t ∈ times → e.time.val < t.val) →
    (∀ (t : ℕ) (ht : t ≤ ell),
      ReferenceUpDecoderBankInvariant.upBankInvariant (X t (by omega)) ∧
      (X t (by omega)).coordinator ≠ .dagger) →
    (∀ (q : Fin B.length) (_hqpos : 0 < q.val) (_hfq : f ≤ q.val) (_hqn : q.val ≤ n),
      let r := ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B q
      PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot →
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 r.input.time).1 = i →
      ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p)
        (incoming : ReferenceActivePhysicalStep.Ledger rate)
        (tail : ReferenceCollectionPhaseHistory.Tail r.input)
        (recording : CoordinatorRecordingOperation.Output p)
        (L : ReferenceActivePhysicalStep.Ledger rate)
        (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
        (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionChoice B i q).configuration =
          .ordinary choice memory ∧ ActiveFollowerLifecycle.localStateDomainValid choice ∧
        choice.status = .unoccupied ∧
        r.input.state.coordinator = .collection payload incoming saved ∧
        r.input.rows = rows ∧ r.input.selected = selected ∧ r.input.rewards = rewards ∧
        ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
          some (ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U) ∧
        ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare r.input)
            tail.payload tail.started tail.weights) = some recording ∧
        CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success L ∧
        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
        CoordinatorUpReception.receptionInputCheck
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true ∧
        r.output.coordinator.up = some diagnostic ∧
        diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
        tail.reception = some (L,
          ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
        i ∈ L.pending ∧ CoordinatorCollectionLedger.acceptUpCheck L i U = true) →
    ∀ (b : ℕ) (hfb : f ≤ b) (hbn : b ≤ n + 1),
      let S := (B.drop f).take (b - f)
      let times := S.map (fun record => record.input.time)
      let tr := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace S i
      let P := AffineBatchDecoder.positives p tr times
      let ch := (X f ((Nat.add_le_add_left
        (hfb.trans (hbn.trans (Nat.succ_le_of_lt hn))) w).trans hlen)).upDecoderBank i
      let Q := AffineBatchDecoder.quota p
      let first := ch.pending ++ P.take (Q - ch.pending.length)
      let window := P.drop (Q - ch.pending.length)
      let uword := ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord U
      P.length = Q - ch.pending.length + Q →
      ∃ (q : Fin B.length) (_hqn : q.val ≤ n)
        (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
        (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
        (tail : ReferenceCollectionPhaseHistory.Tail B[q.val].input)
        (recording : CoordinatorRecordingOperation.Output p)
        (L : ReferenceActivePhysicalStep.Ledger rate),
        let r := B[q.val]
        0 < q.val ∧ f ≤ q.val ∧ q.val < b ∧ q.val ≤ n ∧
        E.records[w + q.val]? = some r ∧
        r.input.time.val = start + w + q.val ∧
        r.input.rows = source.1.2 ∧ r.input.selected = selected ∧
        r.input.rewards = rewards ∧
        first.length = Q ∧ window.length = Q ∧ ch.pending.length < Q ∧
        P.length ≤ 2 * Q ∧
        window.Pairwise (fun a b => a.time.val < b.time.val) ∧
        (∀ e, e ∈ ch.pending → e ∉ window) ∧
        last ∈ window ∧ AffineBatchDecoder.decisionTime window = some last.time ∧
        r.input.time = last.time ∧
        r.output.coordinator.up = some diagnostic ∧
        diagnostic.input.selectedFollower = i ∧
        ReferenceSelectedAffinePairLaw.selectedChannel p
          ((source.1.2 selected).2 r.input.time).1 = some (1, i) ∧
        ReferenceActiveAffinePositiveTest.upPositive r.input = true ∧
        0 < CoordinatorUpReception.roundedObservationValue p
          diagnostic.input.ownObservation ∧
        ReferenceCollectionPhaseHistory.executedTail r.input = some tail ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput
            (ReferenceActivePhysicalStep.prepare r.input)
            tail.payload tail.started tail.weights) = some recording ∧
        CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
            .success L ∧
        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
        diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
        CoordinatorUpReception.receptionInputCheck diagnostic.input = true ∧
        tail.reception = some (L,
          ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
        i ∈ L.pending ∧ CoordinatorCollectionLedger.acceptUpCheck L i U = true ∧
        ReferenceActivePhysicalStep.upExpected
          (ReferenceActivePhysicalStep.prepare r.input) = some uword ∧
        diagnostic.expected = some uword ∧
        diagnostic.input.time = r.input.time ∧
        diagnostic.input.affineSample = ((source.1.2 selected).2 r.input.time).2 (1, i) ∧
        diagnostic.input.ownObservation =
          (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback
            (ActiveRoundActions.coordinator p.two_le_m) ∧
        diagnostic.input.upDecoderBank = r.input.state.upDecoderBank ∧
        (diagnostic.input.upDecoderBank i).pending ++ [last] = window ∧
        CoordinatorUpReception.decoderTransition diagnostic.input =
          ({ pending := [], completed := ch.completed ++ [first, window] },
            AffineBatchDecoder.batchOutput window) ∧
        diagnostic.decoderAfter =
          { pending := [], completed := ch.completed ++ [first, window] } ∧
        diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
        (X (q.val + 1) ((Nat.add_le_add_left
          ((Nat.succ_le_succ _hqn).trans (Nat.succ_le_of_lt hn)) w).trans hlen)).upDecoderBank i = diagnostic.decoderAfter ∧
        (X b ((Nat.add_le_add_left
          (hbn.trans (Nat.succ_le_of_lt hn)) w).trans hlen)).upDecoderBank i = diagnostic.decoderAfter ∧
        window ∈ diagnostic.decoderAfter.completed ∧
        (∀ e, e ∈ window → start + w + f ≤ e.time.val ∧
          e.time.val < start + w + b ∧ AffineBatchDecoder.equation e.sample uword) ∧
        AffineBatchDecoder.positives p
          (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
            ((B.drop f).take (q.val + 1 - f)) i)
          (((B.drop f).take (q.val + 1 - f)).map (fun r => r.input.time)) = P ∧
        r.output.next.coordinator ≠ .dagger ∧
        r.output.next.followers i ≠ .dagger ∧
        ((diagnostic.raw = some uword ∧
          ReferenceCollectionPhaseHistory.filteredParsed r.input L = some U ∧
          ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
            (bank : CoordinatorUpReception.UpDecoderBank p),
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare r.input) L).result =
                .success (decoded, bank) ∧
            ReferenceCollectionPhaseHistory.AcceptedUp r.input i U) ∨
          (diagnostic.raw = none ∧
            ∃ left right : AffineChannelLaw.Word (AffineBatchDecoder.width p),
              left ≠ right ∧
              AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) left ∧
              AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) right)) := by
  intro out E w start rows selected whole B initial hmode ell payload saved
    hlen hBlength i f n hfn hn U X hpure hEndpoints hsaved hstates hreceiver
    b hfb hbn S times tr P ch Q first window uword hcount
  obtain ⟨_hWindow, _hBlength, hprefix, hBindex, hBtime, hinitial, hseed⟩ :=
    actual_dispatch_run_facts rate source rewards C_star C_h count hcross hspan hshort d
  have hEndpoint := fun k => (hEndpoints k).2
  have hordinary := fun t ht => (hstates t ht).2
  have hhistory := actual_saved_slice_histories start w count ell f n hlen hn X whole B i hsaved
  obtain ⟨hdisjoint, hbound2, hwindowEquations⟩ := hpure b hfb hbn hcount
  have hb : b ≤ ell := hbn.trans (Nat.succ_le_of_lt hn)
  obtain ⟨q, hqb, last, record, diagnostic, hrecordB, hqpos, hfq, hfirstLen,
    hwindowLen, hpendingSmall, hwindowChron, hlastWindow, hdecision, hrecordTime,
    hdiagnostic, hselected, hdiagTime, hslot, hdraw, hchannel,
    hupPositive, hpositive, hsample, hobs, hdiagBank, happendLast, htransition,
    hafterBank, hraw, hsuccessor, hendBank, hPcrop, hqOrdinary⟩ :=
      actual_interval_deciding_cut initial rows selected rewards start count w ell
        hspan hmode hinitial i (hseed i) B hlen hBlength hprefix f b hfb hb
        hEndpoint (fun t hft ht => hhistory t hft (ht.trans hbn)) (hordinary b hb) hcount
  have hqn : q.val ≤ n := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hqb hbn)
  have hrecordEq : ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B q =
      record := hrecordB
  have hslotB : PublicDiscreteDraws.slotDraw
      ((ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B q).input.row.2
        (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B q).input.time).1 =
        PublicDiscreteDraws.upSlot := by rw [hrecordEq]; exact hslot
  have hdrawB : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      ((ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B q).input.row.2
        (ReferenceFirstCollectionFormedReplyStateInterval.actualCollectionRecord B q).input.time).1 = i := by
    rw [hrecordEq]
    exact hdraw
  have hreceiverAt := hreceiver q hqpos hfq hqn hslotB hdrawB
  rw [hrecordEq] at hreceiverAt
  obtain ⟨choice, memory, incoming, tail, recording, L, diagnosticR, hchoice,
    hvalid, hstatus, hcollection, hrows, hselectedRow, hrewards, hexpected,
    htail, hrecording, hstartL, hsite, hcheck, hdiagR, hinput, htailReception,
    hnoninvalid, hiL, haccept⟩ := hreceiverAt
  have hdiagEq : diagnosticR = diagnostic := Option.some.inj (hdiagR.symm.trans hdiagnostic)
  subst diagnosticR
  have hchoiceEq := actual_collection_choice_at B i q record hrecordB
  have hchoice : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary choice memory :=
    (congrArg (fun c : DeclaredFollowerLocalRound.PreparedRound p rate =>
      c.configuration) hchoiceEq).symm.trans hchoice
  have hinputCheck : CoordinatorUpReception.receptionInputCheck diagnostic.input = true := by
    rw [hinput]
    exact hcheck
  have hsolution : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) uword := by
    apply (AffineBatchDecoder.satisfies_samples_iff window uword).mpr
    intro e he
    exact (hwindowEquations e he).2.2
  obtain ⟨hdiagExpected, hacceptedOrAmbiguous⟩ := receiver_matching_or_ambiguous
    record payload incoming saved tail hcollection htail hqOrdinary i U L
    diagnostic hsite hdiagnostic hdraw haccept hexpected window hraw hsolution
  have hpreserved := selected_up_unoccupied_follower_preserved record i choice
    memory hchoice hvalid hstatus hslot
  have hfollowerOrdinary : record.output.next.followers i ≠ .dagger := by
    rw [hpreserved.2.2.2]
    intro hdagger
    cases hdagger
  have hmemCompleted : window ∈ diagnostic.decoderAfter.completed := by
    rw [hafterBank]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have hrecordIndex :
      whole[w + q.val]? = some record := (hBindex q).trans (congrArg some hrecordB)
  have hrecordDate : record.input.time.val = start + w + q.val :=
    (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      r.input.time.val) hrecordB).symm.trans (hBtime q)
  refine ⟨q, hqn, last, diagnostic, ?_⟩
  rw [hrecordB]
  refine ⟨tail, recording, L, hqpos, hfq, hqb, hqn, hrecordIndex, hrecordDate,
    hrows, hselectedRow, hrewards, hfirstLen, hwindowLen, hpendingSmall, hbound2,
    hwindowChron, hdisjoint, hlastWindow, hdecision, hrecordTime, hdiagnostic,
    hselected, ?_, hupPositive, hpositive, htail, hrecording, hstartL, hsite,
    hinput, hinputCheck, htailReception, hnoninvalid, hiL, haccept, hexpected,
    hdiagExpected, hdiagTime, ?_, hobs, hdiagBank, happendLast, htransition,
    hafterBank, hraw, hsuccessor, hendBank, hmemCompleted, hwindowEquations,
    hPcrop, hqOrdinary, hfollowerOrdinary, hacceptedOrAmbiguous⟩
  · simpa only [hrows, hselectedRow] using hchannel
  · simpa only [hrows, hselectedRow] using hsample


end Bandits.Support.ReferenceFirstCollectionFormedUpLocalReceiverCut

end
