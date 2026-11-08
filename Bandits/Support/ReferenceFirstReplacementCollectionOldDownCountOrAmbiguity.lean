/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionOldDownCallDates
public import Bandits.Support.ReferenceFirstCollectionStoppedOldDownQuota

import Lean.Elab.Tactic.Omega

/-!
# Actual first-replacement OLD DOWN threshold and completed-batch readout

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-55,180-239`,
`sources/zip4/manuscript/06_interruptions.tex:246-299,477-481`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

This module derives the earliest literal OLD-positive threshold inside the
original first-replacement cutoff branch, retaining current physical failure.
The nonfailure branch produces both actual completion coordinates and resets,
fixed-word selected calls including zeros, and the second batch's solver readout.
Already-retained initial words have zero OLD count. Successful acceptance retains
the original queue seed and every checked recovery prefix. This module does not
establish a stopped quota or manuscript theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceFirstReplacementCollectionOldDownCallDates
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The OLD-positive count on the exact source list used by the call-date
producer. A failure at the queried coordinate is still eligible; only an
earlier physical failure removes that coordinate. -/
def oldDownCount
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) : ℕ :=
  (ReferenceFirstReplacementCollectionOldDownCallDates.countedOldDownServiceIndices
    K j i M).length

/-- A single actual coordinate's OLD-positive contribution. -/
def oldDownServiceAt
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (a : Fin K.length) : Prop :=
  ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt (K.get a) i M ∧
    ReferenceSelectedAffinePairLaw.selectedChannel p
      ((K.get a).input.row.2 (K.get a).input.time).1 = some (0, i) ∧
    0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get a) i).val.val ∧
    ∀ r ∈ K.take a.val,
      ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r

/-- The finite coordinate set underlying the executable list count. -/
noncomputable def oldDownServiceFinset
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) : Finset (Fin K.length) := by
  classical
  exact Finset.univ.filter fun a => a.val < j ∧ oldDownServiceAt K i M a

private theorem oldDownCount_eq_card_filter
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    oldDownCount K j i M = (oldDownServiceFinset K j i M).card := by
  classical
  have hnodup' :
      (ReferenceFirstReplacementCollectionOldDownCallDates.countedOldDownServiceIndices
        K j i M).Nodup := by
    unfold ReferenceFirstReplacementCollectionOldDownCallDates.countedOldDownServiceIndices
    exact (List.nodup_finRange K.length).filter _
  calc
    oldDownCount K j i M =
        ((ReferenceFirstReplacementCollectionOldDownCallDates.countedOldDownServiceIndices
          K j i M).toFinset).card := by
      unfold oldDownCount
      symm
      exact List.toFinset_card_of_nodup hnodup'
    _ = (oldDownServiceFinset K j i M).card := by
      simp [ReferenceFirstReplacementCollectionOldDownCallDates.countedOldDownServiceIndices,
        ReferenceFirstReplacementCollectionOldDownCallDates.countedOldDownServiceAt,
        oldDownServiceFinset, oldDownServiceAt, List.toFinset_filter,
        List.toFinset_finRange]

/-- Increasing the requested physical prefix by one adds at most its new
coordinate to the actual OLD-positive count. -/
theorem oldDownCount_succ_le
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hj : j < K.length) :
    oldDownCount K (j + 1) i M ≤ oldDownCount K j i M + 1 := by
  classical
  rw [oldDownCount_eq_card_filter, oldDownCount_eq_card_filter]
  let x : Fin K.length := ⟨j, hj⟩
  have hsub : oldDownServiceFinset K (j + 1) i M ⊆
      insert x (oldDownServiceFinset K j i M) := by
    intro a ha
    rcases Finset.mem_filter.mp ha with ⟨_, ha⟩
    by_cases heq : a.val = j
    · rw [Finset.mem_insert]
      exact Or.inl (Fin.ext heq)
    · rw [Finset.mem_insert]
      right
      have hmem : a ∈ oldDownServiceFinset K j i M := by
        simp only [oldDownServiceFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by omega, ha.2⟩
      exact hmem
  have hnot : x ∉ oldDownServiceFinset K j i M := by
    simp only [oldDownServiceFinset, Finset.mem_filter, Finset.mem_univ, true_and, x]
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hcard
  exact hcard

/-- At a local singleton prefix, the literal OLD-positive count increases
exactly when that coordinate satisfies the full OLD service predicate. -/
theorem oldDownCount_succ_eq_add_one_of_service
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hj : j < K.length)
    (hservice : oldDownServiceAt K i M ⟨j, hj⟩) :
    oldDownCount K (j + 1) i M = oldDownCount K j i M + 1 := by
  classical
  let x : Fin K.length := ⟨j, hj⟩
  have hset : oldDownServiceFinset K (j + 1) i M =
      insert x (oldDownServiceFinset K j i M) := by
    ext a
    simp only [oldDownServiceFinset, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨ha, hserviceA⟩
      by_cases heq : a.val = j
      · exact Or.inl (Fin.ext heq)
      · exact Or.inr ⟨by omega, hserviceA⟩
    · rintro (heq | ⟨ha, hserviceA⟩)
      · subst a
        exact ⟨by simp [x], hservice⟩
      · exact ⟨by omega, hserviceA⟩
  have hnot : x ∉ oldDownServiceFinset K j i M := by
    simp only [oldDownServiceFinset, Finset.mem_filter,
      Finset.mem_univ, true_and, x]
    omega
  calc
    oldDownCount K (j + 1) i M =
        (oldDownServiceFinset K (j + 1) i M).card :=
      oldDownCount_eq_card_filter K (j + 1) i M
    _ = (insert x (oldDownServiceFinset K j i M)).card := by rw [hset]
    _ = (oldDownServiceFinset K j i M).card + 1 :=
      Finset.card_insert_of_notMem hnot
    _ = oldDownCount K j i M + 1 := by
      rw [oldDownCount_eq_card_filter]

/-- The OLD-positive count is monotone in the requested prefix length. -/
theorem oldDownCount_mono
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j k : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hjk : j ≤ k) : oldDownCount K j i M ≤ oldDownCount K k i M := by
  classical
  rw [oldDownCount_eq_card_filter, oldDownCount_eq_card_filter]
  apply Finset.card_le_card
  intro a ha
  simp only [oldDownServiceFinset, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ⟨by omega, ha.2⟩

/-- Any count that reaches a positive integer threshold has a first coordinate
whose inclusive prefix count is exactly that threshold. -/
theorem exists_first_oldDownCount_threshold
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (threshold : ℕ) (hthreshold : 0 < threshold) (hj : j ≤ K.length)
    (hreaches : threshold ≤ oldDownCount K j i M) :
    ∃ a : Fin K.length, a.val < j ∧
      oldDownCount K (a.val + 1) i M = threshold ∧
      ∀ b : ℕ, b ≤ a.val → oldDownCount K b i M < threshold := by
  induction j with
  | zero =>
      have hzero : oldDownCount K 0 i M = 0 := by
        rw [oldDownCount_eq_card_filter]
        simp [oldDownServiceFinset]
      omega
  | succ j ih =>
      have hjK : j < K.length := by omega
      by_cases hsmall : oldDownCount K j i M < threshold
      · have hsucc := oldDownCount_succ_le K j i M hjK
        have heq : oldDownCount K (j + 1) i M = threshold := by omega
        refine ⟨⟨j, hjK⟩, by simp, ?_, ?_⟩
        · simpa only [Fin.val_mk] using heq
        · intro b hb
          have hmono := oldDownCount_mono K b j i M hb
          exact lt_of_le_of_lt hmono hsmall
      · have hreachJ : threshold ≤ oldDownCount K j i M := by omega
        have hjle : j ≤ K.length := by omega
        obtain ⟨a, haJ, hthresholdAt, hbefore⟩ := ih hjle hreachJ
        exact ⟨a, by omega, hthresholdAt, hbefore⟩

/-- If the requested prefix has not yet reached the threshold, retain that
case; otherwise expose the earliest actual coordinate where it is reached. -/
theorem oldDownCount_small_or_first_threshold
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (threshold : ℕ) (hthreshold : 0 < threshold) (hj : j ≤ K.length) :
    oldDownCount K j i M < threshold ∨
      ∃ a : Fin K.length, a.val < j ∧
        oldDownCount K (a.val + 1) i M = threshold ∧
        ∀ b : ℕ, b ≤ a.val → oldDownCount K b i M < threshold := by
  by_cases hsmall : oldDownCount K j i M < threshold
  · exact Or.inl hsmall
  · right
    have hreach : threshold ≤ oldDownCount K j i M := by omega
    exact exists_first_oldDownCount_threshold K j i M threshold hthreshold hj hreach

private theorem oldDownCount_succ_of_not_service
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (j : ℕ) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hj : j < K.length) (hno : ¬ oldDownServiceAt K i M ⟨j, hj⟩) :
    oldDownCount K (j + 1) i M = oldDownCount K j i M := by
  classical
  rw [oldDownCount_eq_card_filter, oldDownCount_eq_card_filter]
  congr 1
  ext a
  simp only [oldDownServiceFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ha, hs⟩
    have hne : a.val ≠ j := by
      intro he
      have hfin : a = ⟨j, hj⟩ := Fin.ext he
      exact hno (hfin ▸ hs)
    exact ⟨by omega, hs⟩
  · rintro ⟨ha, hs⟩
    exact ⟨by omega, hs⟩

/-- Reaching a new threshold requires service at that actual coordinate.
In particular, its failure exclusion concerns the strict past only. -/
theorem oldDownServiceAt_of_first_threshold
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (a : Fin K.length) (threshold : ℕ)
    (hbefore : oldDownCount K a.val i M < threshold)
    (hat : oldDownCount K (a.val + 1) i M = threshold) :
    oldDownServiceAt K i M a := by
  classical
  by_contra hn
  have he := oldDownCount_succ_of_not_service K a.val i M a.isLt hn
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

private theorem actualDownPositives_append
    (i : Fin (p.m - 1))
    (left right : List (ReferenceCompletePhysicalHistory.RoundRecord p rate)) :
    ReferenceFollowerDownDecoderReplay.actualDownPositives i (left ++ right) =
      ReferenceFollowerDownDecoderReplay.actualDownPositives i left ++
        ReferenceFollowerDownDecoderReplay.actualDownPositives i right := by
  simp only [ReferenceFollowerDownDecoderReplay.actualDownPositives,
    ReferenceFollowerDownDecoderReplay.actualDownCalls, List.filterMap_append,
    ReferenceFollowerDownDecoderReplay.positiveCallEntries, List.flatMap_append]

private theorem actualDownPositives_singleton_length
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate) (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory)
    (hu : state.status = .unoccupied) :
    (ReferenceFollowerDownDecoderReplay.actualDownPositives i [r]).length =
      if ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
        0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val
      then 1 else 0 := by
  classical
  have hr : ReferenceFollowerDownDecoderReplay.preparedChoiceRow r i = r.input.row :=
    (ReferenceFollowerFixedReply.actualChoice_alignment r i).1
  have ht := ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime r i
  have hcall := ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary r i state memory hc
  have helig := ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p i
    r.input.row r.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i)
    rate state
  simp only [ReferenceFollowerDownDecoderReplay.actualDownPositives,
    ReferenceFollowerDownDecoderReplay.actualDownCalls, List.filterMap_cons,
    List.filterMap_nil, hcall, ReferenceFollowerDownDecoderReplay.positiveCallEntries,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [ht, hr]
  by_cases hs : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
      0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i).val.val
  · have he : AffineBatchDecoder.eligible
        ((ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate state))
              r.input.time) := helig.mpr ⟨hs.1, hu, hs.2⟩
    simp only [AffineBatchDecoder.positiveAt, ite_eq_left he, ite_eq_left hs,
      List.length_singleton]
  · have he : ¬ AffineBatchDecoder.eligible
        ((ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation r i) rate state))
              r.input.time) := by
      intro h
      have hh := helig.mp h
      exact hs ⟨hh.1, hh.2.2⟩
    simp only [AffineBatchDecoder.positiveAt, ite_eq_right he, ite_eq_right hs,
      List.length_nil]

/-- On a physically ordinary OLD prefix with no earlier physical failure,
the literal service count is exactly the length of its actual positive calls.
This local identity does not assume a decoder trace or a completed batch. -/
theorem oldDownCount_eq_actualDownPositives_length
    (K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (j : ℕ) (hj : j ≤ K.length)
    (hold : ∀ a : Fin K.length, a.val < j → actualOldAt (K.get a) i M)
    (hfree : ∀ a : Fin K.length, a.val < j →
      ∀ r ∈ K.take a.val,
        ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r) :
    oldDownCount K j i M =
      (ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take j)).length := by
  classical
  induction j with
  | zero =>
    rw [oldDownCount_eq_card_filter]
    simp [oldDownServiceFinset, ReferenceFollowerDownDecoderReplay.actualDownPositives,
      ReferenceFollowerDownDecoderReplay.actualDownCalls,
      ReferenceFollowerDownDecoderReplay.positiveCallEntries]
  | succ j ih =>
    have hjK : j < K.length := by omega
    let a : Fin K.length := ⟨j, hjK⟩
    have hOld := hold a (by simp [a])
    obtain ⟨state, memory, hc, hu, _⟩ := hOld
    have hlen := actualDownPositives_singleton_length (K.get a) i state memory hc hu
    have hprev := ih (by omega)
      (fun b hb => hold b (by omega)) (fun b hb => hfree b (by omega))
    rw [List.take_succ_eq_append_getElem hjK, actualDownPositives_append, List.length_append]
    change oldDownCount K (j + 1) i M =
      (ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take j)).length +
        (ReferenceFollowerDownDecoderReplay.actualDownPositives i [K.get a]).length
    rw [← hprev, hlen]
    by_cases hs : ActiveFollowerDownAcceptance.downSelected p i
        (K.get a).input.row (K.get a).input.time ∧
        0 < (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get a) i).val.val
    · rw [ite_eq_left hs]
      exact oldDownCount_succ_eq_add_one_of_service K j i M hjK
        ⟨hold a (by simp [a]), (selectedChannel_down_iff _ _).2 hs.1,
          hs.2, hfree a (by simp [a])⟩
    · rw [ite_eq_right hs, Nat.add_zero]
      apply oldDownCount_succ_of_not_service K j i M hjK
      rintro ⟨_, hchannel, hpositive, _⟩
      exact hs ⟨(selectedChannel_down_iff _ _).1 hchannel, hpositive⟩

private theorem connected_drop
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate)}
    (h : ReferenceActivePhysicalHorizon.Connected initial records final) (n : ℕ) :
    ∃ middle, ReferenceActivePhysicalHorizon.Connected middle (records.drop n) final := by
  induction n generalizing initial records with
  | zero => exact ⟨initial, h⟩
  | succ n ih =>
    cases records with
    | nil => exact ⟨final, rfl⟩
    | cons r records => exact ih h.2

/-- An OLD ordinary choice forces every earlier ordinary choice in its
connected physical prefix to be OLD. This retains stale positive starts. -/
theorem actualOldAt_before_of_connected
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {K : List (ReferenceCompletePhysicalHistory.RoundRecord p rate)}
    (chain : ReferenceActivePhysicalHorizon.Connected initial K final)
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (a b : Fin K.length) (hba : b.val ≤ a.val)
    (current earlier : ReferencePrelaunchFollower.State p rate.eta)
    (currentMemory earlierMemory : ActiveFollowerLifecycle.LocalMemory p)
    (ha : (ReferenceFollowerFixedReply.actualChoice (K.get a) i).configuration =
      .ordinary current currentMemory)
    (hb : (ReferenceFollowerFixedReply.actualChoice (K.get b) i).configuration =
      .ordinary earlier earlierMemory)
    (hu : earlier.status = .unoccupied)
    (hstale : ReferencePrelaunchFollower.acceptedStart current < M.val.sigma) :
    actualOldAt (K.get b) i M := by
  have hm := (ReferenceFollowerReplyChronology.connected_choice_chronology chain i
    b.val a.val b.isLt a.isLt hba earlier current earlierMemory currentMemory hb ha).1
  refine ⟨earlier, earlierMemory, hb, hu, ?_⟩
  intro he
  have hsigma : ReferencePrelaunchFollower.acceptedStart earlier = M.val.sigma := by
    simp only [ReferencePrelaunchFollower.acceptedStart, he]
  omega

/-- Before the first quota, every literal call, including ineligible and
zero-feedback calls, preserves the completed history and appends its positives. -/
theorem foldDownCalls_before_quota
    (calls : List (ReferenceFollowerDownDecoderReplay.Call p))
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hsmall : bank.pending.length +
      (ReferenceFollowerDownDecoderReplay.positiveCallEntries calls).length <
        AffineBatchDecoder.quota p) :
    ReferenceFollowerDownDecoderReplay.foldDownCalls calls bank =
      ⟨bank.pending ++ ReferenceFollowerDownDecoderReplay.positiveCallEntries calls,
        bank.completed⟩ := by
  induction calls generalizing bank with
  | nil => simp [ReferenceFollowerDownDecoderReplay.foldDownCalls,
      ReferenceFollowerDownDecoderReplay.positiveCallEntries]
  | cons call calls ih =>
    let added := AffineBatchDecoder.positiveAt p
      (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1
    have htotal : bank.pending.length + (added ++
        ReferenceFollowerDownDecoderReplay.positiveCallEntries calls).length <
          AffineBatchDecoder.quota p := hsmall
    have hhead : (bank.pending ++ added).length < AffineBatchDecoder.quota p := by
      simp only [List.length_append] at htotal ⊢
      omega
    have hstep : ReferenceFollowerDownDecoderReplay.replayDownCall bank call =
        ⟨bank.pending ++ added, bank.completed⟩ :=
      ite_eq_left hhead
    change ReferenceFollowerDownDecoderReplay.foldDownCalls calls
      (ReferenceFollowerDownDecoderReplay.replayDownCall bank call) = _
    rw [hstep]
    have htail : (bank.pending ++ added).length +
        (ReferenceFollowerDownDecoderReplay.positiveCallEntries calls).length <
          AffineBatchDecoder.quota p := by
      simpa only [List.length_append, Nat.add_assoc] using htotal
    simpa only [ReferenceFollowerDownDecoderReplay.positiveCallEntries,
      List.flatMap_cons, List.append_assoc] using ih ⟨bank.pending ++ added, bank.completed⟩ htail

private theorem connected_endpointState_at
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate)}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (n : ℕ) (hn : n < records.length) :
    ReferenceCollectionSegmentExtraction.endpointState initial (records.take n) =
      records[n].input.state := by
  induction records generalizing initial n with
  | nil => simp only [List.length_nil] at hn; omega
  | cons record rest ih =>
    cases n with
    | zero => exact chain.1.symm
    | succ n =>
      exact ih chain.2 n (by simp only [List.length_cons] at hn; omega)

/-- The public two-batch window applied to literal stamped calls, retaining
both the arbitrary pending equations and the whole completed history. -/
theorem foldDownCalls_two_batch_readout
    (calls : List (ReferenceFollowerDownDecoderReplay.Call p))
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hpending : bank.pending.length < AffineBatchDecoder.quota p)
    (hpair : calls.Pairwise (fun x y => x.1.val < y.1.val))
    (holder : ∀ e ∈ bank.pending, ∀ call ∈ calls, e.time.val < call.1.val)
    (hcount : (ReferenceFollowerDownDecoderReplay.positiveCallEntries calls).length =
      AffineBatchDecoder.quota p - bank.pending.length + AffineBatchDecoder.quota p) :
    let positives := ReferenceFollowerDownDecoderReplay.positiveCallEntries calls
    let first := bank.pending ++ positives.take (AffineBatchDecoder.quota p - bank.pending.length)
    let pure := positives.drop (AffineBatchDecoder.quota p - bank.pending.length)
    ReferenceFollowerDownDecoderReplay.foldDownCalls calls bank =
      ⟨[], bank.completed ++ [first, pure]⟩ ∧
    first.length = AffineBatchDecoder.quota p ∧
    pure.length = AffineBatchDecoder.quota p ∧
    pure.Pairwise (fun x y => x.time.val < y.time.val) ∧
    (∀ e ∈ bank.pending, e ∉ pure) := by
  have hnonempty : calls ≠ [] := by
    intro hn
    have hq := AffineBatchDecoder.quota_pos p
    simp only [hn, ReferenceFollowerDownDecoderReplay.positiveCallEntries,
      List.flatMap_nil, List.length_nil] at hcount
    omega
  obtain ⟨fallback, _⟩ := List.exists_mem_of_ne_nil calls hnonempty
  let trace := ReferenceFollowerDownIntervalWindow.administrativeIntervalTrace calls fallback
  have hcurrent : ∀ call ∈ calls,
      trace call.1 = ActiveFollowerDownAcceptance.currentInputExtension p call.2 call.1 := by
    intro call hcall
    exact ReferenceFollowerDownIntervalWindow.administrativeIntervalTrace_on_call hpair hcall
  have hpositive := ReferenceFollowerDownIntervalWindow.positiveCallEntries_eq_positives
    trace hcurrent
  have hfold := ReferenceFollowerDownIntervalWindow.foldDownCalls_eq_run trace hcurrent bank
  have hchron : (calls.map Prod.fst).Pairwise (fun x y => x.val < y.val) :=
    List.pairwise_map.mpr hpair
  have hstamp : ∀ e ∈ bank.pending, ∀ t ∈ calls.map Prod.fst, e.time.val < t.val := by
    intro e he t ht
    obtain ⟨call, hcall, rfl⟩ := List.mem_map.mp ht
    exact holder e he call hcall
  obtain ⟨first, hrun, hfirst, hfirstLen, hpureLen, hpurePair, hdisjoint, _⟩ :=
    WaitedWordWindow.run_two_batch_window p trace (calls.map Prod.fst) bank hpending
      (by rw [← hpositive]; exact hcount) hchron hstamp
  dsimp only
  dsimp only [WaitedWordWindow.secondPositiveWindow] at hrun hpureLen hpurePair hdisjoint
  rw [← hpositive] at hrun hfirst hpureLen hpurePair hdisjoint
  rw [hfirst] at hrun hfirstLen
  exact ⟨hfold.trans hrun, hfirstLen, hpureLen, hpurePair, hdisjoint⟩

/-- The generic physical interval cut yields an actual retained completion,
not merely a quota-sized list. Its count test stays inside the conclusion. -/
theorem run_interval_actual_second_completion
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start left right : ℕ) (hlr : left ≤ right) (span : start + right ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (seed : ReferenceFollowerDecoderChronology.downBatchSeed initial start)
    (i : Fin (p.m - 1)) (endpoint : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hendpoint : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start right span active).finalState.followers i = .ordinary endpoint memory) :
    ∃ (base : ReferencePrelaunchFollower.State p rate.eta)
      (baseMemory : ActiveFollowerLifecycle.LocalMemory p),
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start left
      (by omega) active).finalState.followers i = .ordinary base baseMemory ∧
    (let I := (ReferenceActivePhysicalHorizon.run initial rows selected rewards start right
        span active).records.drop left
     let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i I
     let first := base.downBatch.pending ++
       P.take (AffineBatchDecoder.quota p - base.downBatch.pending.length)
     let pure := P.drop (AffineBatchDecoder.quota p - base.downBatch.pending.length)
     P.length = AffineBatchDecoder.quota p - base.downBatch.pending.length +
       AffineBatchDecoder.quota p →
     ∃ (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
       (record : ReferenceCompletePhysicalHistory.RoundRecord p rate)
       (logged : ReferencePrelaunchFollower.State p rate.eta)
       (diag : ReferenceDownReception.ReferenceDownCutOutput p rate),
       entry ∈ pure ∧ (∀ e ∈ pure, e.time.val ≤ entry.time.val) ∧
       entry.time = record.input.time ∧ record ∈ I ∧
       (record.output.followers i).downInput = some logged ∧
       (record.output.followers i).down = some diag ∧
       diag.rawComparison.isSome = true ∧
       ReferenceFirstLiveDownCompletionReadout.completedDownBatch record i = some pure ∧
       diag.raw = AffineBatchDecoder.batchOutput pure ∧
       (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
         (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged).1 =
           ⟨[], base.downBatch.completed ++ [first, pure]⟩) := by
  obtain ⟨base, baseMemory, hbase, hcut⟩ :=
    ReferenceFollowerDownWindowCompletedCut.run_interval_down_completed_window_cut
      p rate initial rows selected rewards start left right hlr span active seed i
      endpoint memory hendpoint
  refine ⟨base, baseMemory, hbase, ?_⟩
  dsimp only at hcut ⊢
  intro hcount
  obtain ⟨index, call, entry, record, choice, choiceMemory, logged, postRecord,
      next, nextMemory, hindex, hsplit, hentry, hmax, hentryTime, hrecord, hcall, hcallTime,
      hchoice, _, _, _, _, _, _, _, _, hlogging, _, _, _, hinput, hdiag,
      _, _, _, hcomp, hraw, hbound, trace, hcurrent, before, beforeMemory,
      _, _, _, _, _, happend, hlen, hdecode⟩ := hcut hcount
  let diag := ReferenceDownReception.referenceDownCut p
    record.output.preparation.coordinator.downView i
    (ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i)
    (ReferenceFollowerDownDecoderReplay.preparedChoiceTime record i)
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged
  have hr : ReferenceFollowerDownDecoderReplay.preparedChoiceRow record i = record.input.row :=
    (ReferenceFollowerFixedReply.actualChoice_alignment record i).1
  have ht := ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime record i
  have hfields : record.output.followers i = record.output.preparation.observeFollower i := by
    rw [record.output_eq]
    rfl
  have hi : (record.output.followers i).downInput = some logged := by
    rw [hfields]
    exact hinput
  have hd : (record.output.followers i).down = some diag := by
    rw [hfields]
    exact hdiag
  have hc : diag.rawComparison.isSome = true := Option.isSome_iff_ne_none.mpr hcomp
  have hframe := ActiveFollowerLogging.checkedLogging_success_frame _ _ _ _ _ _ _ hlogging
  have hcallEq := Option.some.inj (hcall.symm.trans
    (ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary record i choice choiceMemory hchoice))
  have hcallMem : call ∈ ReferenceFollowerDownDecoderReplay.actualDownCalls i
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start right
        span active).records.drop left) := by
    rw [hsplit]
    simp
  have hhere := hcurrent call hcallMem
  rw [hcallEq] at hhere
  dsimp only [Prod.fst, Prod.snd] at hhere
  rw [hr, ht] at hhere
  have hlogInput : ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row
      record.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
      rate choice = ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row
      record.input.time (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i)
      rate logged := by
    simp only [ActiveFollowerDownAcceptance.currentRoundInput, hframe.2.2.2.2.1]
  have hpositive : AffineBatchDecoder.positiveAt p trace record.input.time =
      AffineBatchDecoder.positiveAt p (ActiveFollowerDownAcceptance.currentInputExtension p
        (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged))
          record.input.time := by
    unfold AffineBatchDecoder.positiveAt AffineBatchDecoder.entry
    rw [hhere, hlogInput]
  rw [hcallTime, hpositive] at happend
  have happended : ReferenceFirstLiveDownCompletionReadout.appendedDownBatch record i logged =
      (ReferenceFollowerDownDecoderReplay.actualDownPositives i
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start right
          span active).records.drop left)).drop
            (AffineBatchDecoder.quota p - base.downBatch.pending.length) := happend
  have hcomplete := (ReferenceFirstLiveDownCompletionReadout.completedDownBatch_eq_some_iff
    record i _).2 ⟨logged, diag, hi, hd, hc, by
      rw [happended]
      simp only [List.length_drop, hcount]
      omega, happended⟩
  refine ⟨entry, record, logged, diag, hentry, hmax, hentryTime.trans hcallTime,
    hrecord, hi, hd, hc, hcomplete, hraw, ?_⟩
  simpa only [hr, ht] using hdecode

/-- Original positive-call entries satisfy a fixed actually sent word when
every selected record has a passed retained receiver call for that word. -/
theorem actualDownPositives_satisfy_sent_word
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hfields : ∀ r ∈ records,
      ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time →
      ∃ logged diag,
        (r.output.followers i).downInput = some logged ∧
        (r.output.followers i).down = some diag ∧ diag.rawComparison.isSome = true ∧
        ReferenceActiveAffinePositiveTest.downSent r.input = some word) :
    AffineBatchDecoder.satisfies
      (AffineBatchDecoder.samples (ReferenceFollowerDownDecoderReplay.actualDownPositives i records))
      word := by
  apply (AffineBatchDecoder.satisfies_samples_iff _ _).2
  intro e he
  obtain ⟨call, hcallMem, he⟩ := List.mem_flatMap.mp he
  obtain ⟨r, hr, hcall⟩ := List.mem_filterMap.mp hcallMem
  have hel : AffineBatchDecoder.eligible call.2 := by
    by_contra hn
    simp only [AffineBatchDecoder.positiveAt, ActiveFollowerDownAcceptance.currentInputExtension,
      hn, ite_false, List.not_mem_nil] at he
  have heq : e = AffineBatchDecoder.entry p
      (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1 := by
    simpa only [AffineBatchDecoder.positiveAt, ActiveFollowerDownAcceptance.currentInputExtension,
      hel, ite_true, List.mem_singleton] using he
  have hsample := ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_sample_original_of_eligible
    r i call hcall hel
  cases hc : ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration r i with
  | dagger => simp only [ReferenceFollowerDownDecoderReplay.actualDownCall, hc] at hcall; cases hcall
  | ordinary choice memory =>
    have hcallEq := Option.some.inj (hcall.symm.trans
      (ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary r i choice memory hc))
    have hrAlign : ReferenceFollowerDownDecoderReplay.preparedChoiceRow r i = r.input.row :=
      (ReferenceFollowerFixedReply.actualChoice_alignment r i).1
    have ht := ReferenceFollowerDownDecoderReplay.preparedChoiceTime_eq_recordTime r i
    have hel' := hel
    rw [hcallEq] at hel'
    have hsource := (ReferenceFollowerDownDecoderReplay.actualDownCall_eligible_iff r i choice).1 hel'
    rw [hrAlign, ht] at hsource
    obtain ⟨logged, diag, hi, hd, hcomp, hsent⟩ := hfields r hr hsource.1
    rw [heq]
    change AffineBatchDecoder.equation call.2.sample word
    rw [hsample]
    exact ReferenceFirstLiveDownCompletionReadout.retained_positive_equation
      r i logged diag hi hd hcomp word hsent hsource.2.2

/-- A known solution converts raw absence into genuine solver multiplicity.
The fixed solution itself is retained among the two distinct witnesses. -/
theorem batchOutput_eq_sent_or_multiple
    (batch : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hsat : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) word) :
    AffineBatchDecoder.batchOutput batch = some word ∨
      (AffineBatchDecoder.batchOutput batch = none ∧
        ReferenceFirstLiveDownCompletionReadout.multipleSolutions batch ∧
        ∃ other, word ≠ other ∧
          AffineBatchDecoder.satisfies (AffineBatchDecoder.samples batch) other) := by
  cases hout : AffineBatchDecoder.batchOutput batch with
  | some u =>
    have hu := (AffineBatchDecoder.solve_eq_some_iff _ u).1 hout
    have he := hu.2 word hsat
    exact Or.inl (congrArg some he.symm)
  | none =>
    have halt := (AffineBatchDecoder.solve_eq_none_iff_empty_or_ambiguous _).1 hout
    rcases halt with hempty | htwo
    · exact (hempty word hsat).elim
    · have hm := (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff batch).2 htwo
      obtain ⟨u, v, hu, hv, huv⟩ :=
        (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff batch).1 hm
      refine Or.inr ⟨rfl, hm, ?_⟩
      by_cases he : word = u
      · exact ⟨v, by rw [he]; exact huv, hv⟩
      · exact ⟨u, he, hu⟩

/-- Actual-source threshold and endpoint banks. A current physical failure is
split before any favorable sender claim. On the other branch the actual OLD
count is identified with the retained positive list and its two completed
banks, without a supplied trace, readiness or completion premise. -/
theorem complete_first_replacement_collection_old_down_threshold_banks
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
            ∃ initial : ReferenceActivePhysicalStep.State p rate,
              ∃ active : ReferenceActivePhysicalHorizon.allActiveAtStart initial s,
              ReferenceCorrectedInitializationLaunch.correctedLaunch
                rate source rewards C_star C_h = some initial ∧
              ReferenceFollowerDecoderChronology.downBatchSeed initial s ∧
              ∀ i : Fin (p.m - 1),
                ∃ (base : ReferencePrelaunchFollower.State p rate.eta)
                  (baseMemory : ActiveFollowerLifecycle.LocalMemory p)
                  (span0 : s + c ≤ p.T),
                (Z 0).followers i = .ordinary base baseMemory ∧
                (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s c span0 active
                  ).finalState.followers i = .ordinary base baseMemory ∧
                ReferenceFollowerDecoderChronology.downBatchEndpoint base (s + c) ∧
                (base.lastDown = some (M i) → ∀ j : ℕ, j ≤ K.length →
                  oldDownCount K j i (M i) = 0) ∧
                ∀ j : ℕ, j ≤ K.length →
                  let Q := AffineBatchDecoder.quota p
                  let need := (Q - base.downBatch.pending.length) + Q
                  let M := M i
                  need ≤ 2 * Q ∧
                  (oldDownCount K j i M < need ∨
                    ∃ a : Fin K.length, a.val < j ∧
                      oldDownCount K (a.val + 1) i M = need ∧
                      (∀ b : ℕ, b ≤ a.val → oldDownCount K b i M < need) ∧
                      oldDownServiceAt K i M a ∧
                      (ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt
                        (K.get a) ∨
                        ((∀ r ∈ K.take (a.val + 1),
                          ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r) ∧
                        (∀ b : Fin K.length, b.val ≤ a.val → actualOldAt (K.get b) i M) ∧
                        (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                          (K.take (a.val + 1))).length = need ∧
                        (∀ b : Fin K.length, b.val ≤ a.val →
                          ActiveFollowerDownAcceptance.downSelected p i
                            (K.get b).input.row (K.get b).input.time →
                          ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
                            (memory : ActiveFollowerLifecycle.LocalMemory p)
                            (diag : ReferenceDownReception.ReferenceDownCutOutput p rate),
                            (ReferenceFollowerFixedReply.actualChoice (K.get b) i).configuration =
                              .ordinary state memory ∧
                            ((K.get b).output.followers i).downInput = some state ∧
                            ((K.get b).output.followers i).down = some diag ∧
                            diag.rawComparison.isSome = true ∧
                            let input := ActiveFollowerDownAcceptance.currentRoundInput p i
                              (K.get b).input.row (K.get b).input.time
                              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get b) i)
                              rate state
                            ReferenceFollowerDownDecoderReplay.actualDownCall i (K.get b) =
                              some ((K.get b).input.time, input) ∧
                            input.selected = true ∧ input.receiverEnabled = true ∧
                            input.sample = ReferenceDownPhysicalHashRule.originalDownSample (K.get b).input ∧
                            ReferenceActiveAffinePositiveTest.downSent (K.get b).input =
                              some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                            ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
                              (K.get b).input.time state
                              (ReferenceDownReception.ordinaryParse p rate
                                (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)))) ∧
                        (∃ d : Fin K.length, d.val < a.val ∧
                          (K.get d).input.time.val < (K.get a).input.time.val ∧
                          oldDownCount K (d.val + 1) i M = Q - base.downBatch.pending.length ∧
                          (∀ k : ℕ, k ≤ d.val →
                            oldDownCount K k i M < Q - base.downBatch.pending.length) ∧
                          ∃ (firstState : ReferencePrelaunchFollower.State p rate.eta)
                            (firstDiag : ReferenceDownReception.ReferenceDownCutOutput p rate)
                            (reset : ReferencePrelaunchFollower.State p rate.eta)
                            (resetMemory : ActiveFollowerLifecycle.LocalMemory p),
                            let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i
                              (K.take (a.val + 1))
                            let first := base.downBatch.pending ++
                              P.take (Q - base.downBatch.pending.length)
                            ReferenceFollowerDownDecoderReplay.actualDownPositives i
                              (K.take (d.val + 1)) = P.take (Q - base.downBatch.pending.length) ∧
                            firstState.downBatch =
                              ⟨base.downBatch.pending ++ ReferenceFollowerDownDecoderReplay.actualDownPositives i
                                (K.take d.val), base.downBatch.completed⟩ ∧
                            ((K.get d).output.followers i).downInput = some firstState ∧
                            ((K.get d).output.followers i).down = some firstDiag ∧
                            firstDiag.rawComparison.isSome = true ∧
                            ReferenceFirstLiveDownCompletionReadout.completedDownBatch
                              (K.get d) i = some first ∧
                            firstDiag.raw = AffineBatchDecoder.batchOutput first ∧
                            (ActiveFollowerDownAcceptance.currentDecodeStep p i
                              (K.get d).input.row (K.get d).input.time
                              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get d) i)
                              rate firstState).1 = ⟨[], base.downBatch.completed ++ [first]⟩ ∧
                            (Z (d.val + 1)).followers i = .ordinary reset resetMemory ∧
                            reset.downBatch = ⟨[], base.downBatch.completed ++ [first]⟩) ∧
                        ∃ (endpoint : ReferencePrelaunchFollower.State p rate.eta)
                          (memory : ActiveFollowerLifecycle.LocalMemory p)
                          (span : s + (c + (a.val + 1)) ≤ p.T),
                          (Z (a.val + 1)).followers i = .ordinary endpoint memory ∧
                          (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                            (c + (a.val + 1)) span active).records.drop c = K.take (a.val + 1) ∧
                          (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                            (c + (a.val + 1)) span active).finalState = Z (a.val + 1) ∧
                          let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i
                            (K.take (a.val + 1))
                          let first := base.downBatch.pending ++
                            P.take (Q - base.downBatch.pending.length)
                          let pure := P.drop (Q - base.downBatch.pending.length)
                          endpoint.downBatch = ⟨[], base.downBatch.completed ++ [first, pure]⟩ ∧
                          first.length = Q ∧ pure.length = Q ∧
                          pure.Pairwise (fun x y => x.time.val < y.time.val) ∧
                          (∀ e ∈ base.downBatch.pending, e ∉ pure) ∧
                          (∀ e ∈ P, s + c ≤ e.time.val ∧
                            e.time.val < s + c + (a.val + 1)) ∧
                          ∃ (logged : ReferencePrelaunchFollower.State p rate.eta)
                            (diag : ReferenceDownReception.ReferenceDownCutOutput p rate),
                            ((K.get a).output.followers i).downInput = some logged ∧
                            ((K.get a).output.followers i).down = some diag ∧
                            diag.rawComparison.isSome = true ∧
                            ReferenceFirstLiveDownCompletionReadout.completedDownBatch
                              (K.get a) i = some pure ∧
                            diag.raw = AffineBatchDecoder.batchOutput pure ∧
                            (ActiveFollowerDownAcceptance.currentDecodeStep p i
                              (K.get a).input.row (K.get a).input.time
                              (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get a) i)
                              rate logged).1 = ⟨[], base.downBatch.completed ++ [first, pure]⟩ ∧
                            AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure)
                              (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                            (AffineBatchDecoder.batchOutput pure =
                                some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∨
                              (AffineBatchDecoder.batchOutput pure = none ∧
                                ReferenceFirstLiveDownCompletionReadout.multipleSolutions pure ∧
                                ∃ other,
                                  CoordinatorLocalArmChoice.storedDownFlatWord payload i ≠ other ∧
                                  AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure) other)) ∧
                            (AffineBatchDecoder.batchOutput pure =
                                some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) →
                              ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get a) i M ∧
                              ∃ (accepted : OrdinaryMessageCodec.acceptDown
                                  (ReferencePrelaunchFollower.codecParams p rate.eta)
                                  (ReferencePrelaunchFollower.acceptedStart logged)
                                  ((K.get a).input.time.val + 1) M)
                                (recovered : ActiveFollowerDownAcceptance.ReplayRegisters)
                                (post : ReferencePrelaunchFollower.State p rate.eta)
                                (memory : ActiveFollowerLifecycle.LocalMemory p),
                                let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M
                                  (K.get a).input.time (ActiveFollowerDownAcceptance.acceptedDownStartLE
                                    p rate M (K.get a).input.time logged accepted) (K.get a).input.row
                                scan.endpoint = cut.input.time.val + 1 ∧
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
                                diag.raw = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                                diag.outcome = .accepted logged post
                                  (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) M scan
                                  recovered.registers recovered.lastService ∧
                                (K.get a).output.followers i =
                                  ⟨.ordinary post memory, none, some logged, some diag⟩ ∧
                                (K.get a).output.next.followers i = .ordinary post memory ∧
                                (Z (a.val + 1)).followers i = .ordinary post memory))))
          | _ => True
      | _ => True := by
  classical
  have hSource := complete_first_replacement_collection_old_down_call_dates
    rate source rewards C_star C_h
  simp only []
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
    have hbSource := hb
    dsimp only [R, w, v] at hbSource
    simp only [hbSource] at hSource
    simp only
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hSource ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hSource ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        have hcSource := hc
        dsimp only [R, w, v, tail, c] at hcSource
        simp only [hcSource] at hSource
        simp only
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hSource ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only [ReferenceActivePhysicalStep.collectionInput] at hSource ⊢
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          rcases hSource with ⟨hcutTime, hcalendar, _, _, _, _, hAll, hBank, hPositiveDates⟩
          obtain ⟨initial, active, hlaunch, hseed, hBank⟩ := hBank
          refine ⟨initial, active, hlaunch, hseed, ?_⟩
          intro i
          obtain ⟨span0, state0, memory0, base0, baseMemory0, hstate0, _, hfinal0,
            _, hbase0, hbaseEndpoint, _, _, _, hn, _, _, _, _, _⟩ := hBank i 0 (by omega)
          have hbase : (Z 0).followers i = .ordinary base0 baseMemory0 := by
            have hf : (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                c (by omega) active).finalState = Z 0 := hfinal0
            exact (congrArg (fun z => z.followers i) hf).symm.trans hbase0
          refine ⟨base0, baseMemory0, by omega, hbase, hbase0, hbaseEndpoint, ?_, ?_⟩
          · intro hretained j _
            change base0.lastDown = some (payload.downRecord i) at hretained
            obtain ⟨span, _, _, _, _, _, hdrop, _, _⟩ :=
              hBank i K.length le_rfl
            have hconnected := ReferenceActivePhysicalHorizon.run_connected
              initial source.1.2 J rewards s (c + K.length) span active
            obtain ⟨middle, hchain⟩ := connected_drop hconnected c
            rw [hdrop, List.take_length] at hchain
            have hmiddle : cut.input.state = middle := hchain.1
            have hbaseInput : middle.followers i = .ordinary base0 baseMemory0 := by
              rw [← hmiddle]
              exact hbase
            rw [oldDownCount_eq_card_filter]
            apply Finset.card_eq_zero.mpr
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro a ha
            have hold := (Finset.mem_filter.mp ha).2.2.1
            obtain ⟨state, stateMemory, _, _, _, hchoice, _, _, _, _, _, _, _, _, _, _, _,
              _, _, _, _, _, _, hsender⟩ := hAll a i
            have hstale : ReferencePrelaunchFollower.acceptedStart state <
                (payload.downRecord i).val.sigma := (hsender hold).2.2.2.2.1
            obtain ⟨before, beforeMemory, hinput, hreply, _⟩ :=
              ReferenceFollowerReplyChronology.record_input_to_choice (K.get a) i
                state stateMemory hchoice
            have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input
              hchain a.val a.isLt
            obtain ⟨first, firstMemory, hfirst, hmono, _⟩ :=
              ReferenceFollowerReplyChronology.connected_ordinary_chronology
                hprefix i before beforeMemory hinput
            have heq := hbaseInput.symm.trans hfirst
            cases heq
            have hstart := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply
            have hbaseStart : ReferencePrelaunchFollower.acceptedStart base0 =
                (payload.downRecord i).val.sigma := by
              simp only [ReferencePrelaunchFollower.acceptedStart, hretained]
            omega
          intro j hj
          let Q := AffineBatchDecoder.quota p
          let need := (Q - base0.downBatch.pending.length) + Q
          let M := payload.downRecord i
          have hneed : 0 < need := by
            have hq := AffineBatchDecoder.quota_pos p
            dsimp [need, Q]
            omega
          refine ⟨by
            change (Q - base0.downBatch.pending.length) + Q ≤ 2 * Q
            omega, ?_⟩
          rcases oldDownCount_small_or_first_threshold K j i M need hneed hj with
            hsmall | ⟨a, haj, hat, hbefore⟩
          · exact Or.inl hsmall
          · right
            have hservice := oldDownServiceAt_of_first_threshold K i M a need
              (hbefore a.val le_rfl) hat
            refine ⟨a, haj, hat, hbefore, hservice, ?_⟩
            by_cases hfail : ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt
                (K.get a)
            · exact Or.inl hfail
            · right
              have hfree : ∀ r ∈ K.take (a.val + 1),
                  ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r := by
                intro r hr
                rw [List.take_succ_eq_append_getElem a.isLt] at hr
                rcases List.mem_append.mp hr with hpast | hnow
                · exact hservice.2.2.2 r hpast
                · have he : r = K.get a := by
                    simpa only [List.mem_singleton, List.get_eq_getElem] using hnow
                  exact he ▸ hfail
              obtain ⟨span, endpoint, memory, base1, baseMemory1, hendpoint, hdrop, hfinal,
                _, hbase1, _, _, hfold, _, hn1, holder, hcallsPair, hcallsCalendar,
                hpositivePair, hpositiveTime⟩ := hBank i (a.val + 1) (Nat.succ_le_of_lt a.isLt)
              have heBase := hbase0.symm.trans hbase1
              cases heBase
              obtain ⟨current, currentMemory, logged, post, diag,
                hcurrent, _, _, _, _, _, _, _, _, hinputCurrent, hdiagCurrent, hdiagEqCurrent, _, _, _, _,
                hselectedCurrent, _, hOldCurrent⟩ := hAll a i
              have hstale := (hOldCurrent hservice.1).2.2.2.2.1
              have hconnected := ReferenceActivePhysicalHorizon.run_connected
                initial source.1.2 J rewards s (c + (a.val + 1)) span active
              obtain ⟨middle, hchain⟩ := connected_drop hconnected c
              rw [hdrop] at hchain
              have hchain' : ReferenceActivePhysicalHorizon.Connected middle
                  (K.take (a.val + 1)) (Z (a.val + 1)) := by
                have hf : (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards s
                    (c + (a.val + 1)) span active).finalState = Z (a.val + 1) := hfinal
                exact hf ▸ hchain
              have hallOld : ∀ b : Fin K.length, b.val ≤ a.val → actualOldAt (K.get b) i M := by
                intro b hba
                obtain ⟨earlier, earlierMemory, _, _, _, hchoice, hunoccupied, _⟩ := hAll b i
                have hbTake : b.val < (K.take (a.val + 1)).length := by
                  simp only [List.length_take]
                  omega
                have haTake : a.val < (K.take (a.val + 1)).length := by
                  simp only [List.length_take]
                  omega
                simpa only [List.get_eq_getElem, List.getElem_take] using
                  actualOldAt_before_of_connected hchain' i M
                  ⟨a.val, haTake⟩ ⟨b.val, hbTake⟩ hba current earlier currentMemory earlierMemory
                  (by simpa only [List.get_eq_getElem, List.getElem_take] using hcurrent)
                  (by simpa only [List.get_eq_getElem, List.getElem_take] using hchoice)
                  hunoccupied hstale
              have hfixed : ∀ b : Fin K.length, b.val ≤ a.val →
                  ActiveFollowerDownAcceptance.downSelected p i
                    (K.get b).input.row (K.get b).input.time →
                  ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
                    (memory : ActiveFollowerLifecycle.LocalMemory p)
                    (diag : ReferenceDownReception.ReferenceDownCutOutput p rate),
                    (ReferenceFollowerFixedReply.actualChoice (K.get b) i).configuration =
                      .ordinary state memory ∧
                    ((K.get b).output.followers i).downInput = some state ∧
                    ((K.get b).output.followers i).down = some diag ∧
                    diag.rawComparison.isSome = true ∧
                    let input := ActiveFollowerDownAcceptance.currentRoundInput p i
                      (K.get b).input.row (K.get b).input.time
                      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get b) i) rate state
                    ReferenceFollowerDownDecoderReplay.actualDownCall i (K.get b) =
                      some ((K.get b).input.time, input) ∧
                    input.selected = true ∧ input.receiverEnabled = true ∧
                    input.sample = ReferenceDownPhysicalHashRule.originalDownSample (K.get b).input ∧
                    ReferenceActiveAffinePositiveTest.downSent (K.get b).input =
                      some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                    ReferenceDownReception.ordinaryLocalAcceptanceTest p rate (K.get b).input.time state
                      (ReferenceDownReception.ordinaryParse p rate
                        (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i))) := by
                intro b hba hdown
                obtain ⟨state, stateMemory, logged, post, diag, hchoice, hunoccupied,
                  _, _, _, _, _, _, _, hinput, hdiag, hdiagEq, _, _, _, _, hselected,
                  _, hOldSender⟩ := hAll b i
                obtain ⟨_, _, _, _, _, _, _, hop, _, haccept, _, _, hdownSender⟩ :=
                  hOldSender (hallOld b hba)
                obtain ⟨hlogged, hcall, hselectedInput, henabled, _, hsample, _⟩ := hselected hdown
                have hfreeB : ∀ r ∈ K.take (b.val + 1),
                    ¬ ReferenceFirstReplacementCollectionStoppedPureUpQuota.physicalFailureAt r := by
                  intro r hr
                  exact hfree r (List.take_subset_take_left K (by omega) hr)
                obtain ⟨_, _, hsender⟩ := hdownSender hdown
                obtain ⟨selected, _, _, _, _, hsent, _, _, _, _⟩ := hsender hfreeB
                have hdiagState : diag = ReferenceDownReception.referenceDownCut p
                    (K.get b).output.preparation.coordinator.downView i
                    (K.get b).input.row (K.get b).input.time
                    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get b) i)
                    rate state := by
                  rw [hlogged] at hdiagEq
                  exact hdiagEq
                have hcomp : diag.rawComparison.isSome = true := by
                  rw [hdiagState]
                  simp only [ReferenceDownReception.referenceDownCut, dite_eq_left hdown,
                    dite_eq_left hunoccupied, dite_eq_left hop.1, dite_eq_left hop.2.1,
                    dite_eq_left hop.2.2]
                  split <;> rfl
                rw [hlogged] at hinput hcall hselectedInput henabled hsample
                exact ⟨state, stateMemory, diag, hchoice, hinput, hdiag, hcomp,
                  hcall, hselectedInput, henabled, hsample, hsent, haccept⟩
              have hcount : (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                  (K.take (a.val + 1))).length = need := by
                rw [← oldDownCount_eq_actualDownPositives_length K i M (a.val + 1) (by omega)
                  (fun b hb => hallOld b (by omega))]
                · exact hat
                · intro b hb r hr
                  exact hservice.2.2.2 r
                    (List.take_subset_take_left K (by omega) hr)
              have hbeforeCalls : ∀ e ∈ base0.downBatch.pending,
                  ∀ call ∈ ReferenceFollowerDownDecoderReplay.actualDownCalls i
                    (K.take (a.val + 1)), e.time.val < call.1.val := by
                intro e he call hcall
                have htimeMem : call.1.val ∈
                    ((ReferenceFollowerDownDecoderReplay.actualDownCalls i
                      (K.take (a.val + 1))).map Prod.fst).map Fin.val :=
                  List.mem_map.mpr ⟨call.1, List.mem_map.mpr ⟨call, hcall, rfl⟩, rfl⟩
                rw [hcallsCalendar] at htimeMem
                obtain ⟨offset, _, htime⟩ := List.mem_range'.mp htimeMem
                have htime' : call.1.val = s + c + offset := by
                  simpa only [Nat.mul_one, Nat.one_mul] using htime
                have heOld : e.time.val < s + c := holder e he
                omega
              have htwo := foldDownCalls_two_batch_readout
                (ReferenceFollowerDownDecoderReplay.actualDownCalls i (K.take (a.val + 1)))
                base0.downBatch hn1 hcallsPair hbeforeCalls hcount
              dsimp only at htwo
              rw [← hfold] at htwo
              have hordinary : (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards
                  s (c + (a.val + 1)) span active).finalState.followers i =
                    .ordinary endpoint memory :=
                (congrArg (fun z => z.followers i) hfinal).trans hendpoint
              obtain ⟨base2, baseMemory2, hbase2, hcompletion⟩ :=
                run_interval_actual_second_completion initial source.1.2 J rewards s c
                  (c + (a.val + 1)) (by omega) span active hseed i endpoint memory hordinary
              have heBase2 := hbase0.symm.trans hbase2
              cases heBase2
              dsimp only at hcompletion
              rw [hdrop] at hcompletion
              obtain ⟨entry, record, actualLogged, actualDiag, hentry, hmax, hentryTime,
                hrecord, hinput, hdiag, hcompared, hcompleted, hrawBatch, hdecodeBank⟩ :=
                  hcompletion hcount
              let P := ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take (a.val + 1))
              let gap := AffineBatchDecoder.quota p - base0.downBatch.pending.length
              let pure := P.drop gap
              have hgap : 0 < gap := by dsimp [gap]; omega
              obtain ⟨d, hd, hdat, hdbefore⟩ := exists_first_oldDownCount_threshold K
                (a.val + 1) i M gap hgap (by omega) (by
                  rw [hat]; dsimp [need, gap, Q]; omega)
              have hda : d.val < a.val := by
                have hq := AffineBatchDecoder.quota_pos p
                by_contra hnot
                have he : d = a := Fin.ext (by omega)
                rw [he, hat] at hdat
                dsimp [gap, need, Q] at hdat
                omega
              have hcountBefore : (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                  (K.take d.val)).length < gap := by
                rw [← oldDownCount_eq_actualDownPositives_length K i M d.val (by omega)
                  (fun b hb => hallOld b (by omega))
                  (fun b hb r hr => hservice.2.2.2 r
                    (List.take_subset_take_left K (by omega) hr))]
                exact hdbefore d.val le_rfl
              have hcountFirst : (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                  (K.take (d.val + 1))).length = gap := by
                rw [← oldDownCount_eq_actualDownPositives_length K i M (d.val + 1) (by omega)
                  (fun b hb => hallOld b (by omega))
                  (fun b hb r hr => hservice.2.2.2 r
                    (List.take_subset_take_left K (by omega) hr))]
                exact hdat
              have hprefixP : ReferenceFollowerDownDecoderReplay.actualDownPositives i
                  (K.take (d.val + 1)) = P.take gap := by
                have hr : K.take (d.val + 1) <+: K.take (a.val + 1) :=
                  List.take_prefix_take_left (by omega)
                have hc := hr.filterMap (ReferenceFollowerDownDecoderReplay.actualDownCall i)
                have hp := hc.flatMap (fun call => AffineBatchDecoder.positiveAt p
                  (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1)
                have he : ReferenceFollowerDownDecoderReplay.actualDownPositives i
                    (K.take (d.val + 1)) =
                    P.take (ReferenceFollowerDownDecoderReplay.actualDownPositives i
                      (K.take (d.val + 1))).length := List.prefix_iff_eq_take.mp hp
                rw [hcountFirst] at he
                exact he
              obtain ⟨spanD, before, beforeMemory, baseD, baseMemoryD, hbeforeZ, _, hbeforeFinal,
                _, hbaseD, _, _, hfoldBefore, _⟩ := hBank i d.val (Nat.le_of_lt d.isLt)
              have heBaseD := hbase0.symm.trans hbaseD
              cases heBaseD
              have hbeforeBank : before.downBatch =
                  ⟨base0.downBatch.pending ++ ReferenceFollowerDownDecoderReplay.actualDownPositives i
                    (K.take d.val), base0.downBatch.completed⟩ :=
                hfoldBefore.trans (foldDownCalls_before_quota
                (ReferenceFollowerDownDecoderReplay.actualDownCalls i (K.take d.val))
                base0.downBatch (by change base0.downBatch.pending.length +
                  (ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take d.val)).length <
                    AffineBatchDecoder.quota p; dsimp [gap] at hcountBefore; omega))
              have hdservice := oldDownServiceAt_of_first_threshold K i M d gap
                (hdbefore d.val le_rfl) hdat
              obtain ⟨firstState, firstMemory, firstDiag, hchoiceFirst, hinputFirst, hdiagFirst,
                hcompFirst, hcallFirst, _⟩ := hfixed d (by omega)
                  ((selectedChannel_down_iff _ _).1 hdservice.2.1)
              have hmiddle : cut.input.state = middle := hchain'.1
              have hdTake : d.val < (K.take (a.val + 1)).length := by
                simp only [List.length_take]; omega
              have hinputD : (K.get d).input.state = Z d.val := by
                have he := connected_endpointState_at hchain' d.val hdTake
                simpa only [← hmiddle, List.take_take, Nat.min_eq_left (by omega : d.val ≤ a.val + 1),
                  List.get_eq_getElem, List.getElem_take] using he.symm
              have hbeforeOrdinary : (ReferenceActivePhysicalHorizon.run initial source.1.2 J rewards
                  s (c + d.val) spanD active).finalState.followers i =
                    .ordinary before beforeMemory :=
                (congrArg (fun z => z.followers i) hbeforeFinal).trans hbeforeZ
              have hoccupied := ReferenceFollowerDecoderChronology.run_occupied_pending_empty
                initial source.1.2 J rewards s (c + d.val) spanD active hseed i
                  before beforeMemory hbeforeOrdinary
              have hstateBank := (ReferenceFollowerDecoderChronology.run_interruption_downBatch_frame
                (K.get d) i before firstState beforeMemory firstMemory
                (hinputD ▸ hbeforeZ) hchoiceFirst hoccupied).1
              have hrecordSplit : K.take (d.val + 1) = K.take d.val ++ [K.get d] :=
                List.take_succ_eq_append_getElem d.isLt
              have hpositiveSplit : ReferenceFollowerDownDecoderReplay.actualDownPositives i
                  (K.take (d.val + 1)) =
                    ReferenceFollowerDownDecoderReplay.actualDownPositives i (K.take d.val) ++
                    AffineBatchDecoder.positiveAt p
                      (ActiveFollowerDownAcceptance.currentInputExtension p
                        (ActiveFollowerDownAcceptance.currentRoundInput p i (K.get d).input.row
                          (K.get d).input.time
                          (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get d) i)
                          rate firstState)) (K.get d).input.time := by
                rw [hrecordSplit, actualDownPositives_append]
                simp only [ReferenceFollowerDownDecoderReplay.actualDownPositives,
                  ReferenceFollowerDownDecoderReplay.actualDownCalls, List.filterMap_cons,
                  hcallFirst, List.filterMap_nil, ReferenceFollowerDownDecoderReplay.positiveCallEntries,
                  List.flatMap_cons, List.flatMap_nil, List.append_nil]
              have happended : ReferenceFirstLiveDownCompletionReadout.appendedDownBatch
                  (K.get d) i firstState = base0.downBatch.pending ++ P.take gap := by
                unfold ReferenceFirstLiveDownCompletionReadout.appendedDownBatch
                rw [hstateBank, hbeforeBank]
                dsimp only
                rw [List.append_assoc, ← hpositiveSplit, hprefixP]
              have hfirstCompleted :=
                (ReferenceFirstLiveDownCompletionReadout.completedDownBatch_eq_some_iff
                  (K.get d) i (base0.downBatch.pending ++ P.take gap)).2
                    ⟨firstState, firstDiag, hinputFirst, hdiagFirst, hcompFirst,
                      by rw [happended]; exact htwo.2.1.ge, happended⟩
              obtain ⟨_, loggedF, diagF, hinputF, hdiagF, _, _, hdecodeFirst, hrawFirst⟩ :=
                ReferenceFirstLiveDownCompletionReadout.completedDownBatch_spec
                  (K.get d) i _ hfirstCompleted
              have heLogged : loggedF = firstState := Option.some.inj (hinputF.symm.trans hinputFirst)
              subst loggedF
              have heDiag : diagF = firstDiag := Option.some.inj (hdiagF.symm.trans hdiagFirst)
              subst diagF
              rw [hstateBank, hbeforeBank] at hdecodeFirst
              obtain ⟨spanF, reset, resetMemory, baseF, baseMemoryF, hresetZ, _, _, _,
                hbaseF, _, _, hfoldFirst, _⟩ := hBank i (d.val + 1) (Nat.succ_le_of_lt d.isLt)
              have heBaseF := hbase0.symm.trans hbaseF
              cases heBaseF
              have hfoldAt : ReferenceFollowerDownDecoderReplay.foldDownCalls
                  (ReferenceFollowerDownDecoderReplay.actualDownCalls i (K.take (d.val + 1)))
                  base0.downBatch = (ActiveFollowerDownAcceptance.currentDecodeStep p i
                    (K.get d).input.row (K.get d).input.time
                    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get d) i)
                    rate firstState).1 := by
                rw [hrecordSplit]
                simp only [ReferenceFollowerDownDecoderReplay.actualDownCalls, List.filterMap_append,
                  List.filterMap_cons, hcallFirst, List.filterMap_nil,
                  ReferenceFollowerDownDecoderReplay.foldDownCalls, List.foldl_append,
                  List.foldl_cons, List.foldl_nil]
                change ReferenceFollowerDownDecoderReplay.replayDownCall
                  (ReferenceFollowerDownDecoderReplay.foldDownCalls
                    (ReferenceFollowerDownDecoderReplay.actualDownCalls i (K.take d.val))
                    base0.downBatch) _ = _
                rw [← hfoldBefore, ← hstateBank]
                rfl
              have hresetBank := hfoldFirst.trans (hfoldAt.trans hdecodeFirst)
              have hPpair : P.Pairwise (fun x y => x.time.val < y.time.val) := hpositivePair
              have hcurrentCounted : a ∈ countedOldDownServiceIndices K (a.val + 1) i M :=
                (mem_countedOldDownServiceIndices K (a.val + 1) i M a).2
                  ⟨by omega, hservice⟩
              obtain ⟨_, _, _, _, _, heP⟩ := hPositiveDates i (a.val + 1) a hcurrentCounted
              let currentEntry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p) :=
                ⟨(K.get a).input.time, ReferenceDownPhysicalHashRule.originalDownSample (K.get a).input⟩
              have heP' : currentEntry ∈ P := heP
              have hentryP : entry ∈ P := List.mem_of_mem_drop hentry
              have hcalA : (K.get a).input.time.val + 1 = cut.input.time.val + 1 + a.val :=
                hcalendar a
              have ht0 : cut.input.time.val = s + c := hcutTime
              have hentryUpper : entry.time.val < s + c + (a.val + 1) :=
                (hpositiveTime entry hentryP).2
              have hcurrentPure : currentEntry ∈ pure := by
                have hsplitP : P.take gap ++ pure = P := List.take_append_drop gap P
                have hpSplit : (P.take gap ++ pure).Pairwise
                    (fun x y => x.time.val < y.time.val) := by
                  simpa only [hsplitP] using hPpair
                have heSplit : currentEntry ∈ P.take gap ++ pure := by
                  simpa only [hsplitP] using heP'
                rcases List.mem_append.mp heSplit with hfirst | hpure
                · have hlt := (List.pairwise_append.mp hpSplit).2.2 currentEntry hfirst entry hentry
                  have hcurrentTime : currentEntry.time.val = (K.get a).input.time.val := rfl
                  omega
                · exact hpure
              have hmaxCurrent : currentEntry.time.val ≤ entry.time.val := hmax currentEntry hcurrentPure
              have hdate : record.input.time.val = (K.get a).input.time.val := by
                have heTime := congrArg Fin.val hentryTime
                have hcurrentTime : currentEntry.time.val = (K.get a).input.time.val := rfl
                omega
              obtain ⟨b, hb, hget⟩ := List.mem_take_iff_getElem.mp hrecord
              have hbK : b < K.length := (Nat.lt_min.mp hb).2
              have hget' : K.get ⟨b, hbK⟩ = record := hget
              have hsame : (⟨b, hbK⟩ : Fin K.length) = a :=
                coordinate_eq_of_calendar K (cut.input.time.val + 1)
                  (fun x => hcalendar x) ⟨b, hbK⟩ a (by rw [hget']; exact hdate)
              have hrecordEq : record = K.get a := by rw [← hsame]; exact hget'.symm
              rw [hrecordEq] at hinput hdiag hcompleted hdecodeBank
              have hsolutionP : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples P)
                  (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
                apply actualDownPositives_satisfy_sent_word
                intro r hr hdown
                obtain ⟨b, hb, hget⟩ := List.mem_take_iff_getElem.mp hr
                have hbK : b < K.length := (Nat.lt_min.mp hb).2
                have hget' : K.get ⟨b, hbK⟩ = r := hget
                obtain ⟨state, stateMemory, diag, _, hi, hd, hc, _, _, _, _, hsent, _⟩ :=
                  hfixed ⟨b, hbK⟩ (Nat.le_of_lt_succ (Nat.lt_min.mp hb).1)
                    (by rw [hget']; exact hdown)
                rw [hget'] at hi hd hsent
                exact ⟨state, diag, hi, hd, hc, hsent⟩
              have hsolutionPure : AffineBatchDecoder.satisfies (AffineBatchDecoder.samples pure)
                  (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
                apply (AffineBatchDecoder.satisfies_samples_iff _ _).2
                intro e he
                exact (AffineBatchDecoder.satisfies_samples_iff _ _).1 hsolutionP e
                  (List.mem_of_mem_drop he)
              have hsolver := batchOutput_eq_sent_or_multiple pure
                (CoordinatorLocalArmChoice.storedDownFlatWord payload i) hsolutionPure
              refine ⟨hfree, hallOld, hcount, hfixed,
                ⟨d, hda, by
                  change (K.get d).input.time.val < (K.get a).input.time.val
                  have hdTime : (K.get d).input.time.val + 1 = cut.input.time.val + 1 + d.val :=
                    hcalendar d
                  omega, hdat, hdbefore, firstState, firstDiag, reset, resetMemory,
                  hprefixP, hstateBank.trans hbeforeBank, hinputFirst, hdiagFirst,
                  hcompFirst, hfirstCompleted, hrawFirst,
                  hdecodeFirst, hresetZ, hresetBank⟩,
                endpoint, memory, span, hendpoint, hdrop,
                hfinal, htwo.1, htwo.2.1, htwo.2.2.1, htwo.2.2.2.1,
                htwo.2.2.2.2, hpositiveTime, actualLogged, actualDiag, hinput, hdiag,
                hcompared, hcompleted, hrawBatch, hdecodeBank, hsolutionPure, hsolver, ?_⟩
              intro hword
              have hdownAt := (selectedChannel_down_iff (K.get a) i).1 hservice.2.1
              have hloggedCurrent := (hselectedCurrent hdownAt).1
              rw [hloggedCurrent] at hinputCurrent
              have hloggedEq : actualLogged = current :=
                Option.some.inj (hinput.symm.trans hinputCurrent)
              have hrawFields := ReferenceFirstLiveDownCompletionReadout.retained_call_fields
                (K.get a) i actualLogged actualDiag hinput hdiag hcompared
              have hdecoded : (ActiveFollowerDownAcceptance.currentDecodeStep p i
                  (K.get a).input.row (K.get a).input.time
                  (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get a) i)
                  rate current).2 =
                  some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
                rw [← hloggedEq]
                exact hrawFields.2.2.2.2.2.1.symm.trans (hrawBatch.trans hword)
              obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdownSender⟩ :=
                hOldCurrent hservice.1
              obtain ⟨_, _, hthrough⟩ := hdownSender hdownAt
              obtain ⟨_, _, _, _, _, _, _, _, _, hrecovery⟩ := hthrough hfree
              obtain ⟨accepted, recovered, post, hscan, hrecover, hregisters, hprefixes,
                hlast, hstatus, hbuffer, hbank, hraw, houtcome, houtput, hnext,
                hretained, b, hb, _, hZ⟩ := hrecovery hdecoded
              have hdiagIdentity := Option.some.inj (hdiag.symm.trans hdiagCurrent)
              rw [hloggedCurrent] at hdiagEqCurrent
              have hdiagActual := hdiagIdentity.trans hdiagEqCurrent
              have hdecodeCurrent : (ActiveFollowerDownAcceptance.currentDecodeStep p i
                  (K.get a).input.row (K.get a).input.time
                  (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get a) i)
                  rate current).1 = ⟨[], base0.downBatch.completed ++
                    [base0.downBatch.pending ++ P.take gap, pure]⟩ := by
                rw [← hloggedEq]
                exact hdecodeBank
              have hbankActual : post.downBatch = ⟨[], base0.downBatch.completed ++
                  [base0.downBatch.pending ++ P.take gap, pure]⟩ := hbank.trans hdecodeCurrent
              rw [← hdiagActual] at hraw houtcome houtput
              have hrawActual := hraw.trans hdecoded
              have houtcomeActual : actualDiag.outcome = .accepted current post
                  (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) M
                  (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M (K.get a).input.time
                    (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M (K.get a).input.time
                      current accepted) (K.get a).input.row) recovered.registers
                  recovered.lastService := by
                calc
                  actualDiag.outcome = .accepted current post
                      (ActiveFollowerDownAcceptance.currentDecodeStep p i
                        (K.get a).input.row (K.get a).input.time
                        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation (K.get a) i)
                        rate current).2 M
                      (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M (K.get a).input.time
                        (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M (K.get a).input.time
                          current accepted) (K.get a).input.row) recovered.registers
                      recovered.lastService := houtcome
                  _ = _ := by rw [hdecoded]; rfl
              refine ⟨hretained, ?_⟩
              cases hloggedEq
              exact ⟨accepted, recovered, post, currentMemory, hscan, hrecover, hregisters,
                hprefixes, hlast, hstatus, hbuffer, hbankActual, hrawActual, houtcomeActual, houtput,
                hnext, hb ▸ hZ⟩

end Bandits.Support.ReferenceFirstReplacementCollectionOldDownCountOrAmbiguity

end
