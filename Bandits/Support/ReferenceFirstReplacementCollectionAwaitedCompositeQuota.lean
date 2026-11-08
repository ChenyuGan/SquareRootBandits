/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionAwaitedWaitingCost
public import Bandits.Support.ReferenceFirstCollectionCalendarPendingTotal

import Lean.Elab.Tactic.Omega

/-!
# Replacement collection: awaited decoder stop and inclusive composite quota

Sources: `05_binary_transport.tex:20-55,180-240,354-431`,
`06_interruptions.tex:110-177,246-296,425-437,459-487`, and
`appendix_a_local_protocol.tex:8-85,92-108,141-157`, under
`sources/zip4/manuscript/`.

The stop below is an internal decoder-faithful safety stop. Physical failure
is a retained operation failure, not the manuscript queue-overflow event.
No global stopped-charge domination or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open ReferenceFirstReplacementCollectionOldDownCallDates
open ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity
open ReferenceFirstReplacementCollectionStoppedPureUpQuota
open ReferenceFirstCollectionAwaitedDownFailureReadout
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCompositeQuota

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Literal decoder-faithful safety stop on the original calendar. -/
def safetyStopAt
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) : Prop :=
  acceptanceAt r i ∨ physicalFailureAt r ∨
    failureAt rate rewards C_star C_h source r.input.time ∨
    ReferenceFirstReplacementCollectionLocalStopSourceTransport.originalUpAwaitedAmbiguityAtDate
      (rate := rate) rewards C_star C_h control0 source i r.input.time

/-- First literal safety stop, with length when no stop occurs. -/
def safetyStopIndex
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) : ℕ :=
  K.findIdx fun r => decide (safetyStopAt source rewards C_star C_h control0 i r)

/-- Include the first detecting update in every sufficiently long query. -/
def safetyPrefixLength
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (j : ℕ) : ℕ :=
  min j (safetyStopIndex K source rewards C_star C_h control0 i + 1)

/-- A service coordinate is included exactly through the first stop. -/
theorem safetyPrefixLength_coordinate_iff
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (j a : ℕ) :
    a < safetyPrefixLength K source rewards C_star C_h control0 i j ↔
      a < j ∧ a ≤ safetyStopIndex K source rewards C_star C_h control0 i := by
  unfold safetyPrefixLength
  omega

/-- A witnessed stop bounds the first-stop coordinate. -/
theorem safetyStopIndex_le_of_at
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (a : Fin K.length)
    (ha : safetyStopAt source rewards C_star C_h control0 i (K.get a)) :
    safetyStopIndex K source rewards C_star C_h control0 i ≤ a.val := by
  by_contra hn
  have hlt : a.val < safetyStopIndex K source rewards C_star C_h control0 i := by omega
  have hno := List.not_of_lt_findIdx (xs := K)
    (p := fun r => decide (safetyStopAt source rewards C_star C_h control0 i r)) hlt
  exact (of_decide_eq_false hno) ha

/-- The new stop includes every source-aware local UP stop. -/
theorem safetyStopIndex_le_sourceStopIndex
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    safetyStopIndex K source rewards C_star C_h control0 i ≤
      ReferenceFirstReplacementCollectionLocalStopSourceTransport.commonSourceStopIndex
        K i U source rewards C_star C_h control0 := by
  let f := ReferenceFirstReplacementCollectionLocalStopSourceTransport.commonSourceStopIndex
    K i U source rewards C_star C_h control0
  by_cases hf : f < K.length
  · have hs : ReferenceFirstReplacementCollectionLocalStopSourceTransport.commonSourceStopAt
        K i U source rewards C_star C_h control0 (K.get ⟨f, hf⟩) :=
      of_decide_eq_true (List.findIdx_getElem (w := hf))
    apply safetyStopIndex_le_of_at K source rewards C_star C_h control0 i ⟨f, hf⟩
    rcases hs with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  · have heq : f = K.length := Nat.le_antisymm List.findIdx_le_length (by omega)
    change safetyStopIndex K source rewards C_star C_h control0 i ≤ f
    rw [heq]
    exact List.findIdx_le_length

/-- Identify awaitedness using the actual selected sender and retained call.
There is no positive-observation premise. -/
theorem awaitedDownAt_of_selected_sender
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hselected : r.output.preparation.coordinator.selection = some selected)
    (hpayload : selected.view.payload = payload)
    (hdown : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time)
    (hpending : i ∈ selected.view.pendingAtChoice)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (diag : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hi : (r.output.followers i).downInput = some logged)
    (hd : (r.output.followers i).down = some diag)
    (hc : diag.rawComparison.isSome = true)
    (haccept : ReferenceDownReception.ordinaryLocalAcceptanceTest p rate r.input.time logged
      (ReferenceDownReception.ordinaryParse p rate
        (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)))) :
    awaitedDownAt rate r i (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
  have hsender := ReferenceFirstReplacementCollectionOldDownSenderReadiness.selected_sender
    r payload i selected hselected hpayload hdown hpending
  have hfields := ReferenceFirstLiveDownCompletionReadout.retained_call_fields r i
    logged diag hi hd hc
  exact ⟨logged, diag, hi, hd, hc, hfields.2.2.2.2.2.2.1.trans hsender.2.2.1, haccept⟩

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

private theorem linked_prefix_connected
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (Z : ℕ → ReferenceActivePhysicalStep.State p rate)
    (hlinks : ∀ q : Fin K.length,
      (K.get q).input.state = Z q.val ∧ (K.get q).output.next = Z (q.val + 1))
    (n : ℕ) (hn : n ≤ K.length) :
    ReferenceActivePhysicalHorizon.Connected (Z 0) (K.take n) (Z n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n < K.length := by omega
    have hl := hlinks ⟨n, hlt⟩
    rw [← hl.2, List.take_succ_eq_append_getElem hlt]
    exact ReferenceActivePhysicalHorizon.Connected.append_one _ _ (ih (by omega)) hl.1

private theorem formed_entries_eq_drop
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (b : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hstage : ∀ a : Fin K.length, replyFormedAt (K.get a) i M ↔ b ≤ a.val)
    (n : ℕ) :
    formedPositiveEntries (K.take n) i M =
      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries ((K.take n).drop b) i := by
  induction K generalizing b n with
  | nil => simp [formedPositiveEntries, ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries]
  | cons head tail ih =>
    cases n with
    | zero => simp [formedPositiveEntries, ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries]
    | succ n =>
      cases b with
      | zero =>
        have hh : replyFormedAt head i M := (hstage ⟨0, by simp⟩).mpr (Nat.zero_le _)
        have ht : ∀ a : Fin tail.length, replyFormedAt (tail.get a) i M ↔ 0 ≤ a.val := by
          intro a
          simpa using hstage ⟨a.val + 1, by simp⟩
        simpa only [List.take_succ_cons, formedPositiveEntries, List.flatMap_cons,
          ite_eq_left hh, List.drop_zero,
          ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries] using
          congrArg (fun entries => ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries head i ++ entries)
            (ih 0 ht n)
      | succ b =>
        have hh : ¬ replyFormedAt head i M := by
          have h : replyFormedAt head i M ↔ b + 1 ≤ 0 := hstage ⟨0, by simp⟩
          exact fun hh => Nat.not_succ_le_zero b (h.mp hh)
        have ht : ∀ a : Fin tail.length, replyFormedAt (tail.get a) i M ↔ b ≤ a.val := by
          intro a
          simpa only [List.get_eq_getElem, List.getElem_cons_succ, Nat.add_le_add_iff_right]
            using hstage ⟨a.val + 1, by simp⟩
        simpa only [List.take_succ_cons, formedPositiveEntries, List.flatMap_cons,
          ite_eq_right hh, List.nil_append, List.drop_succ_cons] using ih b ht n

private theorem retained_prefix_length_mono
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (b i : ℕ) (follower : Fin (p.m - 1)) (n : ℕ) (hin : i ≤ n) :
    (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries ((K.take i).drop b) follower).length ≤
      (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries ((K.take n).drop b) follower).length := by
  have hprefix : K.take i <+: K.take n := List.take_isPrefix_take.mpr (Or.inl hin)
  exact (((hprefix.drop b).flatMap
    (fun r => ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r follower)).length_le)

private theorem not_formed_before_retained
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (Z : ℕ → ReferenceActivePhysicalStep.State p rate)
    (hchain : ReferenceActivePhysicalHorizon.Connected (Z 0) K (Z K.length))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (q : Fin K.length)
    (hq : ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i M)
    (anchor : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : (K.get q).output.next.followers i = .ordinary anchor memory)
    (a : Fin K.length) (haq : a.val ≤ q.val) :
    ¬ replyFormedAt (K.get a) i M := by
  obtain ⟨right, rightMemory, hr, hstrict, _⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict (K.get q) i M.val.sigma
      (ReferenceAcceptedUpFollowerHistory.retainedDown_appliedDown hq) anchor memory hout
  rintro ⟨left, leftMemory, hl, _, hlast⟩
  have hmono := (ReferenceFollowerReplyChronology.connected_choice_chronology hchain i
    a.val q.val a.isLt q.isLt haq left right leftMemory rightMemory hl hr).1
  have hleft : ReferencePrelaunchFollower.acceptedStart left = M.val.sigma := by
    simp only [ReferencePrelaunchFollower.acceptedStart, hlast]
  omega

private theorem selectedChannel_down_iff
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) (i : Fin (p.m - 1)) :
    ReferenceSelectedAffinePairLaw.selectedChannel p (r.input.row.2 r.input.time).1 =
      some (0, i) ↔
      ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time := by
  constructor
  · intro h
    have hdown : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
        PublicDiscreteDraws.downSlot := by
      by_contra hn
      unfold ReferenceSelectedAffinePairLaw.selectedChannel
        ReferenceSelectedAffinePairLaw.channelFromDraws at h
      simp only [ite_eq_right hn] at h
      by_cases hup : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
          PublicDiscreteDraws.upSlot
      · simp only [ite_eq_left hup] at h
        have hf := congrArg Prod.fst (Option.some.inj h)
        cases hf
      · simp only [ite_eq_right hup] at h
        cases h
    rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p
      (r.input.row.2 r.input.time).1 hdown] at h
    exact ⟨hdown, (Prod.mk.inj (Option.some.inj h)).2⟩
  · rintro ⟨hdown, hi⟩
    rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p
      (r.input.row.2 r.input.time).1 hdown, hi]
    rfl

/-- Original-calendar provenance of every equation and every selected point
of one fixed awaited word, including selected zero-feedback dates. -/
theorem actual_prefix_awaited_provenance
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (alpha : Fin p.T) (a : Fin K.length) (i : Fin (p.m - 1))
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (batch : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hlookup : ∀ b : Fin K.length,
      actualRecord rate rewards C_star C_h (K.get b).input.time source = some (K.get b))
    (hcalendar : ∀ b : Fin K.length, (K.get b).input.time.val = alpha.val + b.val)
    (hrows : ∀ b : Fin K.length, (K.get b).input.row =
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (hawait : ∀ b : Fin K.length, b.val ≤ a.val →
      ActiveFollowerDownAcceptance.downSelected p i (K.get b).input.row (K.get b).input.time →
      awaitedDownAt rate (K.get b) i word)
    (hmember : ∀ e ∈ batch,
      e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take (a.val + 1)))
    (hsolve : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) word)
    :
    (∀ e ∈ batch, alpha.val ≤ e.time.val ∧ e.time.val ≤ (K.get a).input.time.val ∧
      AffineBatchDecoder.equation e.sample word ∧
      ∃ r : ReferenceCompletePhysicalHistory.RoundRecord p rate,
        actualRecord rate rewards C_star C_h e.time source = some r ∧
        e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [r] ∧
        awaitedDownAt rate r i word) ∧
    (∀ t : Fin p.T, alpha.val ≤ t.val → t.val ≤ (K.get a).input.time.val →
      ReferenceSelectedAffinePairLaw.selectedChannel p
        ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t).1 =
          some (0, i) →
      ∃ r : ReferenceCompletePhysicalHistory.RoundRecord p rate,
        actualRecord rate rewards C_star C_h t source = some r ∧
        awaitedDownAt rate r i word) := by
  constructor
  · intro e he
    obtain ⟨r, hr, htime, hdown, hsingle⟩ := actual_down_positive_origin i
      (K.take (a.val + 1)) e (hmember e he)
    obtain ⟨b, hb, hget⟩ := List.mem_iff_getElem.mp hr
    have hbK : b < K.length := by simp only [List.length_take] at hb; omega
    have hba : b ≤ a.val := by simp only [List.length_take] at hb; omega
    have hrecord : K.get ⟨b, hbK⟩ = r := by
      simpa only [List.getElem_take, List.get_eq_getElem] using hget
    have hcal := hcalendar ⟨b, hbK⟩
    rw [hrecord] at hcal
    dsimp only [Fin.val_mk] at hcal
    have hcalA := hcalendar a
    have hactual := hlookup ⟨b, hbK⟩
    rw [hrecord, ← htime] at hactual
    have haw := hawait ⟨b, hbK⟩ hba (by rw [hrecord]; exact hdown)
    rw [hrecord] at haw
    refine ⟨?_, ?_, (AffineBatchDecoder.satisfies_samples_iff batch word).mp hsolve e he,
      r, hactual, hsingle, haw⟩
    · rw [htime, hcal]
      omega
    · rw [htime, hcal, hcalA]
      omega
  · intro t hstart hfinish hchannel
    let b := t.val - alpha.val
    have hba : b ≤ a.val := by have hc := hcalendar a; dsimp only [b]; omega
    have hbK : b < K.length := by omega
    let bK : Fin K.length := ⟨b, hbK⟩
    have htime : (K.get bK).input.time = t := by
      apply Fin.ext
      have hc := hcalendar bK
      change (K.get bK).input.time.val = alpha.val + b at hc
      dsimp only [b] at hc
      omega
    have hchannelK : ReferenceSelectedAffinePairLaw.selectedChannel p
        (((K.get bK).input.row).2 (K.get bK).input.time).1 = some (0, i) := by
      rw [hrows bK, htime]
      exact hchannel
    have hdown := (selectedChannel_down_iff (K.get bK) i).mp hchannelK
    refine ⟨K.get bK, ?_, hawait bK hba hdown⟩
    rw [← htime]
    exact hlookup bK

/-- Construct the literal fixed-awaited DOWN event from an actual consecutive
prefix. Entry provenance is recovered through the call filter and positive
flat map, while the calendar clause covers selected zero-feedback dates too. -/
theorem fixedAwaitedDownFailureAt_of_actual_prefix
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (alpha : Fin p.T) (a : Fin K.length) (i : Fin (p.m - 1))
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (batch : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hlookup : ∀ b : Fin K.length,
      actualRecord rate rewards C_star C_h (K.get b).input.time source = some (K.get b))
    (hcalendar : ∀ b : Fin K.length, (K.get b).input.time.val = alpha.val + b.val)
    (hrows : ∀ b : Fin K.length, (K.get b).input.row =
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (hawait : ∀ b : Fin K.length, b.val ≤ a.val →
      ActiveFollowerDownAcceptance.downSelected p i (K.get b).input.row (K.get b).input.time →
      awaitedDownAt rate (K.get b) i word)
    (hmember : ∀ e ∈ batch,
      e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take (a.val + 1)))
    (hsolve : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) word)
    (hcompleted : ReferenceFirstLiveDownCompletionReadout.completedDownBatch (K.get a) i = some batch)
    (hamb : ReferenceFirstLiveDownCompletionReadout.multipleSolutions batch) :
    fixedAwaitedDownFailureAt rate rewards C_star C_h source (K.get a).input.time := by
  have hw := actual_prefix_awaited_provenance source rewards C_star C_h K alpha a i word batch
    hlookup hcalendar hrows hawait hmember hsolve
  refine ⟨K.get a, i, word, batch, alpha, hlookup a, hcompleted, ?_, hamb, hw.1, hw.2⟩
  rw [hcalendar a]
  omega

private theorem oldCount_eq_card
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    oldDownCount K j i M = (oldDownServiceFinset K j i M).card := by
  have hn : (countedOldDownServiceIndices K j i M).Nodup :=
    (List.nodup_finRange K.length).filter _
  calc
    oldDownCount K j i M = ((countedOldDownServiceIndices K j i M).toFinset).card := by
      exact (List.toFinset_card_of_nodup hn).symm
    _ = (oldDownServiceFinset K j i M).card := by
      simp [countedOldDownServiceIndices, countedOldDownServiceAt,
        oldDownServiceFinset, oldDownServiceAt, List.toFinset_filter, List.toFinset_finRange]

/-- A retained old word excludes every later OLD service coordinate. -/
private theorem oldDownCount_le_after_retained
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hprior : ∀ b : Fin K.length, actualOldAt (K.get b) i M →
      ∀ d : Fin K.length, d.val < b.val →
        ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get d) i M)
    (a : Fin K.length) (ha : ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get a) i M)
    (j : ℕ) : oldDownCount K j i M ≤ oldDownCount K (a.val + 1) i M := by
  rw [oldCount_eq_card, oldCount_eq_card]
  apply Finset.card_le_card
  intro b hb
  simp only [oldDownServiceFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  refine ⟨?_, hb.2⟩
  by_contra hn
  exact hprior b hb.2.1 a (by omega) ha

private theorem actual_record_rows
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : actualRecord rate rewards C_star C_h r.input.time source = some r) :
    r.input.row = source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h r.input.time.val source
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate source rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h r.input.time source _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    exact congrArg (fun x : ReferenceCompletePhysicalHistory.RoundRecord p rate => x.input.row) heq
  · change ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h r.input.time source = some r at hr
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h r.input.time source hz] at hr
    cases hr

/-- The actual first replacement collection, with its inherited DOWN banks,
fixed-awaited pure batch, and the two quotas on the same inclusive prefix.
Every launch/birth/cutoff branch is matched inside the theorem. -/
theorem complete_first_replacement_collection_awaited_composite_quota
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
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
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let Q := AffineBatchDecoder.quota p
            (∀ b : Fin K.length,
              actualRecord rate rewards C_star C_h (K.get b).input.time source = some (K.get b) ∧
              (K.get b).input.time.val = s + c + b.val ∧
              (K.get b).input.row = source.1.2 J) ∧
            ∃ initial : ReferenceActivePhysicalStep.State p rate,
              ∃ active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s,
                ReferenceCorrectedInitializationLaunch.correctedLaunch
                  rate source rewards C_star C_h = some initial ∧
                ReferenceFollowerDecoderChronology.downBatchSeed initial s ∧
                ∀ i : Fin (p.m - 1),
                  let M := payload.downRecord i
                  let word := CoordinatorLocalArmChoice.storedDownFlatWord payload i
                  ∃ (base : ReferencePrelaunchFollower.State p rate.eta)
                    (baseMemory : ActiveFollowerLifecycle.LocalMemory p)
                    (span0 : s + c ≤ p.T),
                    (Z 0).followers i = .ordinary base baseMemory ∧
                    (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s c span0 active
                      ).finalState.followers i = .ordinary base baseMemory ∧
                    ReferenceFollowerDecoderChronology.downBatchEndpoint base (s + c) ∧
                    (base.lastDown = some M → ∀ j : ℕ, j ≤ K.length → oldDownCount K j i M = 0) ∧
                    let need := Q - base.downBatch.pending.length + Q
                    need ≤ 2 * Q ∧
                    (oldDownCount K K.length i M < need ∨
                      ∃ a : Fin K.length,
                        oldDownCount K (a.val + 1) i M = need ∧
                        (∀ j : ℕ, j ≤ a.val → oldDownCount K j i M < need) ∧
                        (physicalFailureAt (K.get a) ∨
                          (∀ b : Fin K.length, b.val ≤ a.val → actualOldAt (K.get b) i M) ∧
                          (∀ b : Fin K.length, b.val ≤ a.val →
                            ActiveFollowerDownAcceptance.downSelected p i
                              (K.get b).input.row (K.get b).input.time →
                            awaitedDownAt rate (K.get b) i word) ∧
                          let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i
                            (K.take (a.val + 1))
                          let first := base.downBatch.pending ++ P.take (Q - base.downBatch.pending.length)
                          let pure := P.drop (Q - base.downBatch.pending.length)
                          ∃ (d : Fin K.length)
                            (endpoint : ReferencePrelaunchFollower.State p rate.eta)
                            (memory : ActiveFollowerLifecycle.LocalMemory p),
                            d.val < a.val ∧
                            oldDownCount K (d.val + 1) i M = Q - base.downBatch.pending.length ∧
                            ReferenceFirstLiveDownCompletionReadout.completedDownBatch
                              (K.get d) i = some first ∧
                            (Z (a.val + 1)).followers i = .ordinary endpoint memory ∧
                            endpoint.downBatch = ⟨[], base.downBatch.completed ++ [first, pure]⟩ ∧
                            first.length = Q ∧ pure.length = Q ∧
                            ReferenceFirstLiveDownCompletionReadout.completedDownBatch
                              (K.get a) i = some pure ∧
                            AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure) word ∧
                            (∀ e ∈ pure,
                              cut.input.time.val ≤ e.time.val ∧ e.time.val ≤ (K.get a).input.time.val ∧
                              AffineBatchDecoder.equation e.sample word ∧
                              ∃ re : ReferenceCompletePhysicalHistory.RoundRecord p rate,
                                actualRecord rate rewards C_star C_h e.time source = some re ∧
                                e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i [re] ∧
                                awaitedDownAt rate re i word) ∧
                            (∀ t : Fin p.T, cut.input.time.val ≤ t.val →
                              t.val ≤ (K.get a).input.time.val →
                              ReferenceSelectedAffinePairLaw.selectedChannel p
                                ((source.1.2 J).2 t).1 = some (0, i) →
                              ∃ re : ReferenceCompletePhysicalHistory.RoundRecord p rate,
                                actualRecord rate rewards C_star C_h t source = some re ∧
                                awaitedDownAt rate re i word) ∧
                            (ReferenceFirstLiveDownCompletionReadout.multipleSolutions pure →
                              fixedAwaitedDownFailureAt rate rewards C_star C_h source
                                (K.get a).input.time) ∧
                            (AffineBatchDecoder.batchOutput pure = some word →
                              ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get a) i M ∧
                              ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
                                (recovered : ActiveFollowerDownAcceptance.ReplayRegisters)
                                (post : ReferencePrelaunchFollower.State p rate.eta)
                                (postMemory : ActiveFollowerLifecycle.LocalMemory p),
                                ((K.get a).output.followers i).downInput = some logged ∧
                                ActiveFollowerDownAcceptance.checkedRecovery p rate M logged
                                  (cut.input.time.val + 1) = .ok recovered ∧
                                recovered.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                                  (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                                    (cut.input.time.val + 1)) ∧
                                (∀ k : ℕ, ∃ middle,
                                  ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
                                    (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
                                    ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                                      (cut.input.time.val + 1)).take k) = .ok middle ∧
                                  middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                                    ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                                      (cut.input.time.val + 1)).take k)) ∧
                                post.lastDown = some M ∧ post.status = .unoccupied ∧ post.buffer = [] ∧
                                post.downBatch = ⟨[], base.downBatch.completed ++ [first, pure]⟩ ∧
                                (K.get a).output.next.followers i = .ordinary post postMemory ∧
                                (Z (a.val + 1)).followers i = .ordinary post postMemory))) ∧
                    ∀ j : ℕ, j ≤ K.length →
                      let h := safetyPrefixLength K source rewards C_star C_h control0 i j
                      oldDownCount K h i M ≤ 2 * Q ∧
                      (formedPositiveEntries (K.take h) i M).length ≤ 2 * Q ∧
                      oldDownCount K h i M + (formedPositiveEntries (K.take h) i M).length ≤ 4 * Q
          | _ => True
      | _ => True := by
  classical
  have hD := complete_first_replacement_collection_old_down_threshold_banks
    rate source rewards C_star C_h
  have hS :=
    ReferenceFirstReplacementCollectionLocalStopSourceTransport.complete_first_replacement_collection_local_stop_source_transport
      rate source rewards C_star C_h
  have hDates := complete_first_replacement_collection_old_down_call_dates
    rate source rewards C_star C_h
  have hRoot :=
    ReferenceFirstReplacementCollectionPureUpAcceptanceRoot.complete_first_replacement_collection_pure_up_acceptance
      rate source rewards C_star C_h
  dsimp only at hD hS hDates hRoot ⊢
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
    rw [hb] at hD hS hDates hRoot
    dsimp only at hD hS hDates hRoot ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      rw [hbirth] at hD hS hDates hRoot
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hD hS hDates hRoot ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      rcases hRoot with ⟨_, _, hRoot⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        rw [hc] at hD hS hDates hRoot
        dsimp only at hD hS hDates hRoot ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          rw [hcut] at hD hS hDates hRoot
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hD hS hDates hRoot ⊢
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := fun i => payload.downRecord i
          rcases hDates with ⟨hcuttime, hcalendar, _hinjective, _hE0, _hZ0,
            _hZE, hstates, _hRuns, _hCalls⟩
          rcases hRoot with ⟨_hcalendar, hZ, hrootFollowers, _hboundary⟩
          rcases hS with ⟨hsourceFollowers, _hdiagnostics, _hsourceBoundary⟩
          obtain ⟨initial, active, hlaunch, hseed, holdFollowers⟩ := hD
          have hchain : ReferenceActivePhysicalHorizon.Connected (Z 0) K (Z K.length) := by
            simpa only [List.take_length] using linked_prefix_connected K Z hZ.2.2 K.length le_rfl
          have hmem : ∀ b : Fin K.length, K.get b ∈ R := by
            intro b
            have hm : K.get b ∈ K := List.get_mem K b
            rcases List.mem_cons.mp hm with heq | ht
            · rw [heq]
              exact List.mem_of_getElem? hc
            · exact List.mem_of_mem_drop (List.takeWhile_subset _ ht)
          have hlookup : ∀ b : Fin K.length,
              actualRecord rate rewards C_star C_h (K.get b).input.time source = some (K.get b) := by
            intro b
            exact ReferenceFirstReplacementCollectionFreshPositiveService.actualRecord_of_mem
              rate source rewards C_star C_h (K.get b) (hmem b)
          have hdate : ∀ b : Fin K.length, (K.get b).input.time.val = cut.input.time.val + b.val := by
            intro b
            have hb := hcalendar b
            change (K.get b).input.time.val + 1 = cut.input.time.val + 1 + b.val at hb
            omega
          have hrows : ∀ b : Fin K.length, (K.get b).input.row = source.1.2 J := by
            intro b
            exact actual_record_rows source rewards C_star C_h (K.get b) (hlookup b)
          refine ⟨?_, initial, active, hlaunch, hseed, ?_⟩
          · intro b
            refine ⟨hlookup b, ?_, hrows b⟩
            rw [hdate b, hcuttime]
          intro i
          have hactual : ∀ a : Fin K.length, actualOldAt (K.get a) i (M i) →
              (K.get a).input.rows = source.1.2 ∧ (K.get a).input.selected = J ∧
              (K.get a).input.rewards = rewards ∧
              ∀ d : Fin K.length, d.val < a.val →
                ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get d) i (M i) := by
            intro a ha
            obtain ⟨state, memory, logged, post, diag, _hchoice, _hstatus, _hdomain,
              _heither, _hlog, _hbuffer, _hpair, _hbatch, _hinit, _hinput, _hdown,
              _hdiag, _hout, _hpostinit, _hpoststatus, _hpostdomain, _hselected,
              _holdiff, hsender⟩ := hstates a i
            obtain ⟨_htime, hrows, hJ, hrwd, _hstart, _hsigma, _hvalid, _hop,
              _hparse, _hacc, _hlabels, hprior, _hrest⟩ := hsender ha
            exact ⟨hrows, hJ, hrwd, hprior⟩
          obtain ⟨base0, baseMemory0, span0, hbase, hrun, hendpoint, hzero, hqueries⟩ := holdFollowers i
          let Q := AffineBatchDecoder.quota p
          let need := Q - base0.downBatch.pending.length + Q
          have hquery := hqueries K.length le_rfl
          have hneed : need ≤ 2 * Q := hquery.1
          have hUpBound : ∀ j : ℕ, j ≤ K.length →
              (formedPositiveEntries
                (K.take (safetyPrefixLength K source rewards C_star C_h control0 i j)) i (M i)).length ≤
                  2 * Q := by
            rcases hsourceFollowers i with hformed | habsent
            · rcases hformed with ⟨b, anchor, memory, U, horigin, _hbK, _hstatus, _hdomain,
                hlast, _hfields, _hsigma, _hpositive, _hsmall, hneedUp, _hlocalCount,
                hsourceCount, _hcertificate⟩
              have hstage : ∀ a : Fin K.length, replyFormedAt (K.get a) i (M i) ↔ b ≤ a.val := by
                rcases hrootFollowers i with hrootFormed | hrootAbsent
                · rcases hrootFormed with ⟨rb, ranchor, rmemory, rorigin, _hrbK,
                    _hrstatus, _hrdomain, _hrlast, _hrend, _rU, _hrfields, _hrsigma,
                    _hrpositive, hrchoices, _hrentries, _hrrest⟩
                  have hbeq : b = rb := by
                    rcases horigin with ⟨hb0, hc0, _⟩ | ⟨q, hbq, hq, hprior, hout⟩
                    · rcases rorigin with ⟨hrb0, _, _⟩ | ⟨rq, _hrbq, _hrq, _hrprior, _hrout, _hrZ, hrnot⟩
                      · omega
                      · exact (hrnot anchor memory hc0 hlast).elim
                    · rcases rorigin with ⟨hrb0, _, _⟩ | ⟨rq, hrbq, hrq, hrprior, _hrout, _hrZ, _hrnot⟩
                      · have hn := not_formed_before_retained K Z hchain i (M i) q hq anchor memory hout q le_rfl
                        obtain ⟨state, mem, hchoice, hstate, hdown, _⟩ := hrchoices q (by omega)
                        exact (hn ⟨state, mem, hchoice, hstate, hdown⟩).elim
                      · have heq : q.val = rq.val := by
                          by_contra hne
                          rcases lt_or_gt_of_ne hne with hlt | hgt
                          · exact hrprior q hlt hq
                          · exact hprior rq hgt hrq
                        omega
                  intro a
                  constructor
                  · intro hfa
                    rcases horigin with ⟨hb0, _⟩ | ⟨q, hbq, hq, _hprior, hout⟩
                    · omega
                    · by_contra hnot
                      exact not_formed_before_retained K Z hchain i (M i) q hq anchor memory
                        hout a (by omega) hfa
                  · intro hba
                    obtain ⟨state, mem, hchoice, hstate, hdown, _⟩ := hrchoices a (by omega)
                    exact ⟨state, mem, hchoice, hstate, hdown⟩
                · rcases horigin with ⟨_hb0, hc0, _⟩ | ⟨q, _hbq, hq, _⟩
                  · obtain ⟨state, mem, hchoice, _hstate, hnot, _⟩ :=
                      hrootAbsent.1 ⟨0, by simp⟩
                    have heq : state = anchor :=
                      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hchoice.symm.trans hc0)).1
                    exact (hnot (heq ▸ hlast)).elim
                  · exact (hrootAbsent.2.2.1 q hq).elim
              intro j hj
              rw [formed_entries_eq_drop K b i (M i) hstage]
              have hc := ((hsourceCount control0).2.2.2 j hj).2
              apply le_trans (retained_prefix_length_mono K b
                (safetyPrefixLength K source rewards C_star C_h control0 i j) i
                (min j (ReferenceFirstReplacementCollectionLocalStopSourceTransport.commonSourceStopIndex
                  K i U source rewards C_star C_h control0 + 1)) ?_) (hc.trans hneedUp)
              have ho := safetyStopIndex_le_sourceStopIndex K source rewards C_star C_h control0 i U
              dsimp only [safetyPrefixLength]
              omega
            · intro j hj
              have he := habsent.2.2.2
                (safetyPrefixLength K source rewards C_star C_h control0 i j)
                ((Nat.min_le_left _ _).trans hj)
              change formedPositiveEntries
                (K.take (safetyPrefixLength K source rewards C_star C_h control0 i j)) i (M i) = [] at he
              rw [he]
              exact Nat.zero_le _
          have hquotaOfOld :
              (∀ j : ℕ, j ≤ K.length →
                oldDownCount K (safetyPrefixLength K source rewards C_star C_h control0 i j) i (M i) ≤ need) →
              ∀ j : ℕ, j ≤ K.length →
                let h := safetyPrefixLength K source rewards C_star C_h control0 i j
                oldDownCount K h i (M i) ≤ 2 * Q ∧
                (formedPositiveEntries (K.take h) i (M i)).length ≤ 2 * Q ∧
                oldDownCount K h i (M i) + (formedPositiveEntries (K.take h) i (M i)).length ≤ 4 * Q := by
            intro hOld j hj
            have ho := (hOld j hj).trans hneed
            have hu := hUpBound j hj
            exact ⟨ho, hu, by omega⟩
          refine ⟨base0, baseMemory0, span0, hbase, hrun, hendpoint, hzero, hneed, ?_⟩
          rcases hquery.2 with hsmall | ⟨a, _haL, hat, hbefore, hservice, hresult⟩
          · refine ⟨Or.inl hsmall, hquotaOfOld ?_⟩
            intro j hj
            have hm := oldDownCount_mono K
              (safetyPrefixLength K source rewards C_star C_h control0 i j) K.length i (M i)
              ((Nat.min_le_left _ _).trans hj)
            exact Nat.le_of_lt (hm.trans_lt hsmall)
          rcases hresult with hfail | ⟨hfree, hallOld, hlen, hfixed, hfirst, hpure⟩
          · refine ⟨Or.inr ⟨a, hat, hbefore, Or.inl hfail⟩, hquotaOfOld ?_⟩
            intro j _
            have hs := safetyStopIndex_le_of_at K source rewards C_star C_h control0 i a
              (Or.inr (Or.inl hfail))
            have hm := oldDownCount_mono K
              (safetyPrefixLength K source rewards C_star C_h control0 i j) (a.val + 1) i (M i)
              (by dsimp only [safetyPrefixLength]; omega)
            exact hm.trans_eq hat
          have hawait : ∀ b : Fin K.length, b.val ≤ a.val →
              ActiveFollowerDownAcceptance.downSelected p i (K.get b).input.row (K.get b).input.time →
              awaitedDownAt rate (K.get b) i (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
            intro b hba hdown
            obtain ⟨state, memory, diag, hchoice, hi, hd, hc, _hcall, _hselected,
              _henabled, _hsample, _hsent, haccept⟩ := hfixed b hba hdown
            obtain ⟨other, otherMemory, logged, post, otherDiag, _hchoice0, _hstatus, _hdomain,
              _heither, _hlog, _hbuffer, _hpair, _hbatch, _hinit, _hinput, _hdown,
              _hdiag, _hout, _hpostinit, _hpoststatus, _hpostdomain, _hselected0,
              _holdiff, hsender⟩ := hstates b i
            obtain ⟨_htime, _hrows, _hJ, _hrwd, _hstart, _hsigma, _hvalid, _hop,
              _hparse, _hacc, _hlabels, _hprior, hsenderDown⟩ := hsender (hallOld b hba)
            have hfreeB : ∀ r ∈ K.take (b.val + 1), ¬ physicalFailureAt r := by
              intro r hr
              have hp : K.take (b.val + 1) <+: K.take (a.val + 1) :=
                List.take_isPrefix_take.mpr (Or.inl (by omega))
              exact hfree r (hp.subset hr)
            obtain ⟨selected, hselected, hpayload, hpending, _⟩ := (hsenderDown hdown).2.2 hfreeB
            exact awaitedDownAt_of_selected_sender (K.get b) payload i selected hselected hpayload
              hdown hpending state diag hi hd hc haccept
          obtain ⟨d, hda, _hdateDA, hdat, _hbeforeD, firstState, firstDiag, reset, resetMemory,
            _hpositiveD, _hfirstState, _hfirstInput, _hfirstDiag, _hfirstPass,
            hfirstComplete, _hfirstRaw, _hfirstDecode, _hresetState, _hresetBank⟩ := hfirst
          obtain ⟨endpoint, memory, _span, hpost, _hdrop, _hfinal,
            hbank, hfirstLen, hpureLen, _hpairwise, _hdisjoint, _htimes,
            logged, diag, hinput, _hdiag, _hpass, hcompleted, _hraw, _hdecode,
            hsatisfies, houtcome, hsuccess⟩ := hpure
          let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take (a.val + 1))
          let pure := P.drop (Q - base0.downBatch.pending.length)
          have hmember : ∀ e ∈ pure,
              e ∈ ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take (a.val + 1)) := by
            intro e he
            exact List.mem_of_mem_drop he
          have hprovenance := actual_prefix_awaited_provenance source rewards C_star C_h K
            cut.input.time a i (CoordinatorLocalArmChoice.storedDownFlatWord payload i) pure
            hlookup hdate hrows hawait hmember hsatisfies
          have hfailure : ReferenceFirstLiveDownCompletionReadout.multipleSolutions pure →
              fixedAwaitedDownFailureAt rate rewards C_star C_h source (K.get a).input.time := by
            intro hamb
            exact fixedAwaitedDownFailureAt_of_actual_prefix source rewards C_star C_h K
              cut.input.time a i (CoordinatorLocalArmChoice.storedDownFlatWord payload i) pure
              hlookup hdate hrows hawait hmember hsatisfies hcompleted hamb
          have hdetector : physicalFailureAt (K.get a) ∨
              fixedAwaitedDownFailureAt rate rewards C_star C_h source (K.get a).input.time ∨
              ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get a) i (M i) := by
            rcases houtcome with hunique | ⟨_hnone, hamb, _hother⟩
            · exact Or.inr (Or.inr (hsuccess hunique).1)
            · exact Or.inr (Or.inl (hfailure hamb))
          refine ⟨Or.inr ⟨a, hat, hbefore, Or.inr ⟨hallOld, hawait, d, endpoint, memory,
            hda, hdat, hfirstComplete, hpost, hbank, hfirstLen, hpureLen, hcompleted,
            hsatisfies, hprovenance.1, hprovenance.2, hfailure, ?_⟩⟩, hquotaOfOld ?_⟩
          · intro hword
            obtain ⟨hretained, _accepted, recovered, post, mem, _hscan, hrecover,
              hreplay, hprefixes, hlast, hstatus, hbuffer, hpostbank, _hdiagraw, _houtcome,
              _houtput, hnext, hZpost⟩ := hsuccess hword
            exact ⟨hretained, logged, recovered, post, mem, hinput, hrecover, hreplay,
              hprefixes, hlast, hstatus, hbuffer, hpostbank, hnext, hZpost⟩
          · intro j _
            rcases hdetector with hfail | hamb | hretained
            · have hs := safetyStopIndex_le_of_at K source rewards C_star C_h control0 i a
                (Or.inr (Or.inl hfail))
              have hm := oldDownCount_mono K
                (safetyPrefixLength K source rewards C_star C_h control0 i j) (a.val + 1) i (M i)
                (by dsimp only [safetyPrefixLength]; omega)
              exact hm.trans_eq hat
            · have hs := safetyStopIndex_le_of_at K source rewards C_star C_h control0 i a
                (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hamb)))))
              have hm := oldDownCount_mono K
                (safetyPrefixLength K source rewards C_star C_h control0 i j) (a.val + 1) i (M i)
                (by dsimp only [safetyPrefixLength]; omega)
              exact hm.trans_eq hat
            · have hm := oldDownCount_le_after_retained K i (M i)
                (fun b hb => (hactual b hb).2.2.2) a hretained
                (safetyPrefixLength K source rewards C_star C_h control0 i j)
              exact hm.trans_eq hat

end Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCompositeQuota
