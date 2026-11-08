/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionStoppedOldDownQuota
public import Bandits.Support.ReferenceFirstReplacementCollectionLocalStopSourceTransport

import Lean.Elab.Tactic.Omega

/-!
# One inclusive mask for the actual first-replacement composite task

Sources: `sources/zip4/manuscript/06_interruptions.tex:246-349,477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:20-55,180-239`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

The stop below is exactly acceptance, physical failure, a retained decoder
flag, or the original-source awaited-UP ambiguity at this record's date.
It is not asserted to exhaust all manuscript source failures. Physical play
continues to the horizon. Predictability and the fresh conditional service
hazard are separate obligations for the subsequent waiting construction.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open ReferenceFirstReplacementCollectionOldDownCallDates
open ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity
open ReferenceFirstReplacementCollectionStoppedPureUpQuota
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionStoppedCompositeQuota

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The common per-record stop, using the original source and whole rewards.
The last predicate has no reply-word parameter. -/
def commonStopAt (s : ℕ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) : Prop :=
  acceptanceAt r i ∨ physicalFailureAt r ∨
    ReferenceFirstLiveDecoderPastMeasurability.retainedDecoderRecordFlag s r = true ∨
    ReferenceFirstReplacementCollectionLocalStopSourceTransport.originalUpAwaitedAmbiguityAtDate
      (rate := rate) rewards C_star C_h control0 source i r.input.time

/-- First common stop, with the list length as the absent-stop value. -/
def commonStopIndex (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) : ℕ :=
  K.findIdx fun r => decide (commonStopAt s source rewards C_star C_h control0 i r)

/-- Requested prefix clipped inclusively at the first common stop. -/
def commonPrefixLength (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (j : ℕ) : ℕ :=
  min j (commonStopIndex s K source rewards C_star C_h control0 i + 1)

/-- OLD contribution on the common inclusive prefix. -/
def commonOldCount (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (j : ℕ) : ℕ :=
  oldDownCount K (commonPrefixLength s K source rewards C_star C_h control0 i j) i M

/-- UP contribution on exactly the same prefix, excluding unformed replies. -/
def commonUpCount (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (j : ℕ) : ℕ :=
  (formedPositiveEntries
    (K.take (commonPrefixLength s K source rewards C_star C_h control0 i j)) i M).length

/-- The composite is the sum of the two actual stage contributions. -/
def compositeCount (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (j : ℕ) : ℕ :=
  commonOldCount s K source rewards C_star C_h control0 i M j +
    commonUpCount s K source rewards C_star C_h control0 i M j

/-- Literal first-stop or absence certificate; the detecting record is retained. -/
theorem commonStopIndex_certificate (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) :
    (∃ a : Fin K.length,
      commonStopIndex s K source rewards C_star C_h control0 i = a.val ∧
      commonStopAt s source rewards C_star C_h control0 i (K.get a) ∧
      ∀ r ∈ K.take a.val, ¬ commonStopAt s source rewards C_star C_h control0 i r) ∨
    (commonStopIndex s K source rewards C_star C_h control0 i = K.length ∧
      ∀ r ∈ K, ¬ commonStopAt s source rewards C_star C_h control0 i r) := by
  let f := commonStopIndex s K source rewards C_star C_h control0 i
  have hle : f ≤ K.length := List.findIdx_le_length
  by_cases hlt : f < K.length
  · left
    refine ⟨⟨f, hlt⟩, rfl, of_decide_eq_true (List.findIdx_getElem (w := hlt)), ?_⟩
    intro r hr
    obtain ⟨a, ha, heq⟩ := List.mem_iff_getElem.mp hr
    have haf : a < f := by simp only [List.length_take] at ha; omega
    have hno := List.not_of_lt_findIdx (xs := K)
      (p := fun r => decide (commonStopAt s source rewards C_star C_h control0 i r)) haf
    simp only [List.getElem_take] at heq
    rw [heq] at hno
    exact of_decide_eq_false hno
  · right
    have heq : f = K.length := by omega
    refine ⟨heq, ?_⟩
    intro r hr
    exact of_decide_eq_false (List.findIdx_eq_length.mp heq r hr)

/-- A coordinate in the common inclusive mask has no earlier common stop. -/
theorem no_commonStop_before_counted (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (j : ℕ) (a : Fin K.length)
    (ha : a.val < commonPrefixLength s K source rewards C_star C_h control0 i j) :
    ∀ r ∈ K.take a.val, ¬ commonStopAt s source rewards C_star C_h control0 i r := by
  intro r hr
  obtain ⟨b, hb, heq⟩ := List.mem_iff_getElem.mp hr
  have hbf : b < commonStopIndex s K source rewards C_star C_h control0 i := by
    dsimp only [commonPrefixLength] at ha
    simp only [List.length_take] at hb
    omega
  have hno := List.not_of_lt_findIdx (xs := K)
    (p := fun r => decide (commonStopAt s source rewards C_star C_h control0 i r)) hbf
  simp only [List.getElem_take] at heq
  rw [heq] at hno
  exact of_decide_eq_false hno

/-- A service coordinate is retained precisely through the first stopping
record, including that record itself. -/
theorem commonPrefixLength_coordinate_iff (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (j a : ℕ) :
    a < commonPrefixLength s K source rewards C_star C_h control0 i j ↔
      a < j ∧ a ≤ commonStopIndex s K source rewards C_star C_h control0 i := by
  unfold commonPrefixLength
  omega

/-- Absence of every literal stop preserves each requested physical prefix. -/
theorem commonPrefixLength_eq_of_absent (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (j : ℕ) (hj : j ≤ K.length)
    (habsent : ∀ r ∈ K, ¬ commonStopAt s source rewards C_star C_h control0 i r) :
    commonPrefixLength s K source rewards C_star C_h control0 i j = j := by
  have hf : commonStopIndex s K source rewards C_star C_h control0 i = K.length := by
    apply List.findIdx_eq_length.mpr
    intro r hr
    exact decide_eq_false (habsent r hr)
  unfold commonPrefixLength
  rw [hf]
  omega

/-- Once the detecting update is included, every longer query uses that same
inclusive prefix; no physical run is truncated by this analytical operation. -/
theorem commonPrefixLength_eq_after_stop (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (j : ℕ)
    (hj : commonStopIndex s K source rewards C_star C_h control0 i + 1 ≤ j) :
    commonPrefixLength s K source rewards C_star C_h control0 i j =
      commonStopIndex s K source rewards C_star C_h control0 i + 1 := by
  exact Nat.min_eq_right hj

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

/-- The missing stage comparison: a counted OLD date cannot follow a retained
DOWN of the current word. The last input is an internal call-date consequence,
proved from the actual run in the root below. -/
private theorem common_old_dates_subset (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hprior : ∀ a : Fin K.length, actualOldAt (K.get a) i M →
      ∀ b : Fin K.length, b.val < a.val →
        ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get b) i M)
    (j : ℕ) :
    oldDownServiceFinset K (commonPrefixLength s K source rewards C_star C_h control0 i j) i M ⊆
      oldDownServiceFinset K
        (min j (ReferenceFirstReplacementCollectionStoppedOldDownQuota.literalOldDownStopIndex
          s K i M + 1)) i M := by
  intro a ha
  simp only [oldDownServiceFinset, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  refine ⟨?_, ha.2⟩
  have haj : a.val < j := lt_of_lt_of_le ha.1 (Nat.min_le_left _ _)
  refine lt_min haj ?_
  let f := ReferenceFirstReplacementCollectionStoppedOldDownQuota.literalOldDownStopIndex s K i M
  by_contra hnot
  have hfa : f < a.val := by omega
  have hfK : f < K.length := hfa.trans a.isLt
  have hstop : ReferenceFirstReplacementCollectionStoppedOldDownQuota.literalOldDownStopAt
      s (K.get ⟨f, hfK⟩) i M :=
    of_decide_eq_true (List.findIdx_getElem (w := hfK))
  have hfmem : K.get ⟨f, hfK⟩ ∈ K.take a.val := by
    apply List.mem_iff_getElem.mpr
    refine ⟨f, by simp only [List.length_take]; omega, ?_⟩
    simp only [List.getElem_take, List.get_eq_getElem]
  rcases hstop with hdown | hfail | hflag
  · exact hprior a ha.2.1 ⟨f, hfK⟩ hfa hdown
  · exact ha.2.2.2.2 _ hfmem hfail
  · exact no_commonStop_before_counted s K source rewards C_star C_h control0 i j a ha.1
      _ hfmem (Or.inr (Or.inr (Or.inl hflag)))

/-- Adding the retained decoder flag can only move the source-aware first stop
backward. No equivalence with a global failure event is used. -/
theorem commonStopIndex_le_sourceStopIndex (s : ℕ)
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    commonStopIndex s K source rewards C_star C_h control0 i ≤
      ReferenceFirstReplacementCollectionLocalStopSourceTransport.commonSourceStopIndex
        K i U source rewards C_star C_h control0 := by
  let f := ReferenceFirstReplacementCollectionLocalStopSourceTransport.commonSourceStopIndex
    K i U source rewards C_star C_h control0
  by_cases hf : f < K.length
  · have hs : ReferenceFirstReplacementCollectionLocalStopSourceTransport.commonSourceStopAt
        K i U source rewards C_star C_h control0 (K.get ⟨f, hf⟩) :=
      of_decide_eq_true (List.findIdx_getElem (w := hf))
    have hc : commonStopAt s source rewards C_star C_h control0 i (K.get ⟨f, hf⟩) := by
      rcases hs with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
    by_contra hnot
    have hlt : f < commonStopIndex s K source rewards C_star C_h control0 i := by omega
    have hno := List.not_of_lt_findIdx (xs := K)
      (p := fun r => decide (commonStopAt s source rewards C_star C_h control0 i r)) hlt
    exact (of_decide_eq_false hno) hc
  · have hfLen : f = K.length := Nat.le_antisymm List.findIdx_le_length (by omega)
    change commonStopIndex s K source rewards C_star C_h control0 i ≤ f
    rw [hfLen]
    exact List.findIdx_le_length

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

/-- A literal stage identity preserves the complete entries, including stamps. -/
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

/-- Before a retained acceptance, ordinary CHOICE chronology prevents the
current reply from already being formed, including at the accepting date. -/
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

/-- The actual first replacement has one inclusive common mask. Both stage
bounds are derived inside this theorem from the accepted source roots; no
formation, chronology, decoder-success, or service-coverage premise is added. -/
theorem complete_first_replacement_collection_stopped_composite_quota
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    ∀ control0 : ContinuousLearningRows.TimeControl p,
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
            let M := fun i => payload.downRecord i
            cut.input.time.val = s + c ∧
            (∀ a : Fin K.length,
              (K.get a).input.time.val + 1 = cut.input.time.val + 1 + a.val) ∧
            Function.Injective (fun a : Fin K.length => (K.get a).input.time) ∧
            ∀ i : Fin (p.m - 1),
              (∀ a : Fin K.length, actualOldAt (K.get a) i (M i) →
                (K.get a).input.rows = source.1.2 ∧
                (K.get a).input.selected = J ∧ (K.get a).input.rewards = rewards ∧
                ∀ d : Fin K.length, d.val < a.val →
                  ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get d) i (M i)) ∧
              (∀ j : ℕ, j ≤ K.length →
                oldDownServiceFinset K
                  (commonPrefixLength s K source rewards C_star C_h control0 i j) i (M i) ⊆
                oldDownServiceFinset K
                  (min j (ReferenceFirstReplacementCollectionStoppedOldDownQuota.literalOldDownStopIndex
                    s K i (M i) + 1)) i (M i)) ∧
              (∀ (j : ℕ) (a : Fin K.length),
                a ∈ countedOldDownServiceIndices K
                    (commonPrefixLength s K source rewards C_star C_h control0 i j) i (M i) →
                  ∃ call : ReferenceFollowerDownDecoderReplay.Call p,
                    ReferenceFollowerDownDecoderReplay.actualDownCall i (K.get a) = some call ∧
                    call.1 = (K.get a).input.time ∧
                    call.2.sample = ReferenceDownPhysicalHashRule.originalDownSample (K.get a).input ∧
                    ⟨(K.get a).input.time,
                      ReferenceDownPhysicalHashRule.originalDownSample (K.get a).input⟩ ∈
                      ReferenceFollowerDownDecoderReplay.actualDownPositives i [K.get a] ∧
                    ⟨(K.get a).input.time,
                      ReferenceDownPhysicalHashRule.originalDownSample (K.get a).input⟩ ∈
                      ReferenceFollowerDownDecoderReplay.actualDownPositives i
                        (K.take (commonPrefixLength s K source rewards C_star C_h control0 i j))) ∧
              (∃ (base : ReferencePrelaunchFollower.State p rate.eta)
                  (baseMemory : ActiveFollowerLifecycle.LocalMemory p),
                (Z 0).followers i = .ordinary base baseMemory ∧
                (base.lastDown = some (M i) → ∀ j : ℕ, j ≤ K.length →
                  commonOldCount s K source rewards C_star C_h control0 i (M i) j = 0) ∧
                ∀ j : ℕ, j ≤ K.length →
                  commonOldCount s K source rewards C_star C_h control0 i (M i) j ≤
                    ReferenceFirstReplacementCollectionStoppedOldDownQuota.stoppedOldDownCount
                      s K j i (M i) ∧
                  ReferenceFirstReplacementCollectionStoppedOldDownQuota.stoppedOldDownCount
                      s K j i (M i) ≤ 2 * AffineBatchDecoder.quota p) ∧
              ((∃ (b : ℕ) (anchor : ReferencePrelaunchFollower.State p rate.eta)
                  (memory : ActiveFollowerLifecycle.LocalMemory p)
                  (U : OrdinaryMessageCodec.UpRecord
                    (ReferencePrelaunchFollower.codecParams p rate.eta)),
                ((b = 0 ∧ (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                    .ordinary anchor memory) ∨
                  ∃ q : Fin K.length, b = q.val + 1 ∧
                    ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i) ∧
                    (∀ a : Fin K.length, a.val < q.val →
                      ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get a) i (M i)) ∧
                    (K.get q).output.next.followers i = .ordinary anchor memory) ∧
                b ≤ K.length ∧ anchor.status = .unoccupied ∧
                anchor.lastDown = some (M i) ∧
                U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
                U.val.sigma = (M i).val.sigma ∧ 0 < U.val.sigma ∧
                (∀ a : Fin K.length, replyFormedAt (K.get a) i (M i) ↔ b ≤ a.val) ∧
                ∀ j : ℕ, j ≤ K.length →
                  formedPositiveEntries
                    (K.take (commonPrefixLength s K source rewards C_star C_h control0 i j)) i (M i) =
                    ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                      ((K.take (commonPrefixLength s K source rewards C_star C_h control0 i j)).drop b) i ∧
                  commonUpCount s K source rewards C_star C_h control0 i (M i) j ≤
                    ReferenceFirstReplacementCollectionLocalStopSourceTransport.commonSourceStoppedUpCount
                      K b i U source rewards C_star C_h control0 j ∧
                  ReferenceFirstReplacementCollectionLocalStopSourceTransport.commonSourceStoppedUpCount
                      K b i U source rewards C_star C_h control0 j ≤
                    AffineBatchDecoder.quota p - ((Z b).upDecoderBank i).pending.length +
                      AffineBatchDecoder.quota p ∧
                  AffineBatchDecoder.quota p - ((Z b).upDecoderBank i).pending.length +
                    AffineBatchDecoder.quota p ≤ 2 * AffineBatchDecoder.quota p) ∨
                (∀ j : ℕ, j ≤ K.length → formedPositiveEntries (K.take j) i (M i) = [])) ∧
              ∀ j : ℕ, j ≤ K.length →
                commonOldCount s K source rewards C_star C_h control0 i (M i) j ≤
                  2 * AffineBatchDecoder.quota p ∧
                commonUpCount s K source rewards C_star C_h control0 i (M i) j ≤
                  2 * AffineBatchDecoder.quota p ∧
                compositeCount s K source rewards C_star C_h control0 i (M i) j ≤
                  4 * AffineBatchDecoder.quota p
          | _ => True
      | _ => True := by
  classical
  intro control0
  have hO :=
    ReferenceFirstReplacementCollectionStoppedOldDownQuota.complete_first_replacement_collection_stopped_old_down_quota
      rate source rewards C_star C_h control0
  have hS :=
    ReferenceFirstReplacementCollectionLocalStopSourceTransport.complete_first_replacement_collection_local_stop_source_transport
      rate source rewards C_star C_h
  have hDates := complete_first_replacement_collection_old_down_call_dates
    rate source rewards C_star C_h
  have hRoot :=
    ReferenceFirstReplacementCollectionPureUpAcceptanceRoot.complete_first_replacement_collection_pure_up_acceptance
      rate source rewards C_star C_h
  dsimp only at hO hS hDates hRoot ⊢
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
    rw [hb] at hO hS hDates hRoot
    dsimp only at hO hS hDates hRoot ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      rw [hbirth] at hO hS hDates hRoot
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hO hS hDates hRoot ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      rcases hRoot with ⟨_, _, hRoot⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        rw [hc] at hO hS hDates hRoot
        dsimp only at hO hS hDates hRoot ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          rw [hcut] at hO hS hDates hRoot
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hO hS hDates hRoot ⊢
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := fun i => payload.downRecord i
          rcases hDates with ⟨hcuttime, hcalendar, hinjective, _hE0, _hZ0,
            _hZE, hstates, _hRuns, hCalls⟩
          rcases hRoot with ⟨_hcalendar, hZ, hrootFollowers, _hboundary⟩
          rcases hS with ⟨hsourceFollowers, _hdiagnostics, _hsourceBoundary⟩
          obtain ⟨_initial, _active, _hlaunch, _hseed, holdFollowers⟩ := hO
          have hchain : ReferenceActivePhysicalHorizon.Connected (Z 0) K (Z K.length) := by
            simpa only [List.take_length] using linked_prefix_connected K Z hZ.2.2 K.length le_rfl
          refine ⟨hcuttime, hcalendar, hinjective, ?_⟩
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
              _holdiff, hactual⟩ := hstates a i
            obtain ⟨_htime, hrows, hJ, hrwd, _hstart, _hsigma, _hvalid, _hop,
              _hparse, _hacc, _hlabels, hprior, _hrest⟩ := hactual ha
            exact ⟨hrows, hJ, hrwd, hprior⟩
          have hsubset := fun j => common_old_dates_subset s K source rewards C_star C_h
            control0 i (M i) (fun a ha => (hactual a ha).2.2.2) j
          obtain ⟨base0, baseMemory0, _span0, hbase0, _hrun0, _hend0,
            hretained0, hqueries⟩ := holdFollowers i
          have holdCompare : ∀ j : ℕ, j ≤ K.length →
              commonOldCount s K source rewards C_star C_h control0 i (M i) j ≤
                ReferenceFirstReplacementCollectionStoppedOldDownQuota.stoppedOldDownCount s K j i (M i) ∧
              ReferenceFirstReplacementCollectionStoppedOldDownQuota.stoppedOldDownCount s K j i (M i) ≤
                2 * AffineBatchDecoder.quota p := by
            intro j hj
            constructor
            · unfold commonOldCount ReferenceFirstReplacementCollectionStoppedOldDownQuota.stoppedOldDownCount
              rw [oldCount_eq_card, oldCount_eq_card]
              exact Finset.card_le_card (hsubset j)
            · have hq := hqueries j hj
              exact hq.2.2.trans hq.1
          have hbaseResult : ∃ (base : ReferencePrelaunchFollower.State p rate.eta)
              (baseMemory : ActiveFollowerLifecycle.LocalMemory p),
              (Z 0).followers i = .ordinary base baseMemory ∧
              (base.lastDown = some (M i) → ∀ j : ℕ, j ≤ K.length →
                commonOldCount s K source rewards C_star C_h control0 i (M i) j = 0) ∧
              ∀ j : ℕ, j ≤ K.length →
                commonOldCount s K source rewards C_star C_h control0 i (M i) j ≤
                  ReferenceFirstReplacementCollectionStoppedOldDownQuota.stoppedOldDownCount s K j i (M i) ∧
                ReferenceFirstReplacementCollectionStoppedOldDownQuota.stoppedOldDownCount s K j i (M i) ≤
                  2 * AffineBatchDecoder.quota p := by
            refine ⟨base0, baseMemory0, hbase0, ?_, holdCompare⟩
            intro hb0 j hj
            exact hretained0 hb0 _ ((Nat.min_le_left _ _).trans hj)
          have hUpResult : ((∃ (b : ℕ) (anchor : ReferencePrelaunchFollower.State p rate.eta)
                  (memory : ActiveFollowerLifecycle.LocalMemory p)
                  (U : OrdinaryMessageCodec.UpRecord
                    (ReferencePrelaunchFollower.codecParams p rate.eta)),
                ((b = 0 ∧ (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
                    .ordinary anchor memory) ∨
                  ∃ q : Fin K.length, b = q.val + 1 ∧
                    ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i) ∧
                    (∀ a : Fin K.length, a.val < q.val →
                      ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get a) i (M i)) ∧
                    (K.get q).output.next.followers i = .ordinary anchor memory) ∧
                b ≤ K.length ∧ anchor.status = .unoccupied ∧
                anchor.lastDown = some (M i) ∧
                U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
                U.val.sigma = (M i).val.sigma ∧ 0 < U.val.sigma ∧
                (∀ a : Fin K.length, replyFormedAt (K.get a) i (M i) ↔ b ≤ a.val) ∧
                ∀ j : ℕ, j ≤ K.length →
                  formedPositiveEntries
                    (K.take (commonPrefixLength s K source rewards C_star C_h control0 i j)) i (M i) =
                    ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
                      ((K.take (commonPrefixLength s K source rewards C_star C_h control0 i j)).drop b) i ∧
                  commonUpCount s K source rewards C_star C_h control0 i (M i) j ≤
                    ReferenceFirstReplacementCollectionLocalStopSourceTransport.commonSourceStoppedUpCount
                      K b i U source rewards C_star C_h control0 j ∧
                  ReferenceFirstReplacementCollectionLocalStopSourceTransport.commonSourceStoppedUpCount
                      K b i U source rewards C_star C_h control0 j ≤
                    AffineBatchDecoder.quota p - ((Z b).upDecoderBank i).pending.length +
                      AffineBatchDecoder.quota p ∧
                  AffineBatchDecoder.quota p - ((Z b).upDecoderBank i).pending.length +
                    AffineBatchDecoder.quota p ≤ 2 * AffineBatchDecoder.quota p) ∨
                (∀ j : ℕ, j ≤ K.length → formedPositiveEntries (K.take j) i (M i) = [])) := by
            rcases hsourceFollowers i with hformed | habsent
            · rcases hformed with ⟨b, anchor, memory, U, horigin, hbK, hstatus, _hdomain,
                hlast, hfields, hsigma, hpositive, _hsmall, hneed, _hlocalCount,
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
              left
              refine ⟨b, anchor, memory, U, ?_, hbK, hstatus, hlast, hfields,
                hsigma, hpositive, hstage, ?_⟩
              · rcases horigin with ⟨hb0, hc0, _⟩ | hdelay
                · exact Or.inl ⟨hb0, hc0⟩
                · exact Or.inr hdelay
              · intro j hj
                have hentries := formed_entries_eq_drop K b i (M i) hstage
                  (commonPrefixLength s K source rewards C_star C_h control0 i j)
                refine ⟨hentries, ?_, ((hsourceCount control0).2.2.2 j hj).2, hneed⟩
                unfold commonUpCount
                rw [hentries]
                apply retained_prefix_length_mono
                have horder := commonStopIndex_le_sourceStopIndex s K source rewards C_star C_h
                  control0 i U
                dsimp only [commonPrefixLength]
                omega
            · exact Or.inr habsent.2.2.2
          refine ⟨hactual, fun j _ => hsubset j, ?_, hbaseResult, hUpResult, ?_⟩
          · intro j a ha
            exact hCalls i (commonPrefixLength s K source rewards C_star C_h control0 i j) a ha
          · intro j hj
            have ho := (holdCompare j hj).1.trans (holdCompare j hj).2
            have hu : commonUpCount s K source rewards C_star C_h control0 i (M i) j ≤
                2 * AffineBatchDecoder.quota p := by
              rcases hUpResult with ⟨b, anchor, memory, U, _horigin, _hbK,
                  _hstatus, _hlast, _hfields, _hsigma, _hpositive, _hstage, hcounts⟩ | habsent
              · have hq := hcounts j hj
                exact hq.2.1.trans (hq.2.2.1.trans hq.2.2.2)
              · unfold commonUpCount
                have hm : commonPrefixLength s K source rewards C_star C_h control0 i j ≤ K.length :=
                  (Nat.min_le_left _ _).trans hj
                rw [habsent _ hm]
                simp
            refine ⟨ho, hu, ?_⟩
            change commonOldCount s K source rewards C_star C_h control0 i (M i) j +
              commonUpCount s K source rewards C_star C_h control0 i (M i) j ≤
                4 * AffineBatchDecoder.quota p
            omega

end Bandits.Support.ReferenceFirstReplacementCollectionStoppedCompositeQuota

end
