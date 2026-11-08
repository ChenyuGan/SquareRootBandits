/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionStreamEmptyDispatch
public import Bandits.Support.ReferenceGeneratedInheritedDownFirstCompletion

import Lean.Elab.Tactic.Omega

/-!
# Local unaccepted DOWN facts in the actual first-collection stream

These are internal consequences on the canonical first-collection run.  The
pending-set result keeps the focal follower's ordinary input and old-word test
as local branch inputs.  The retained-diagnostic result identifies the actual
stored first-collection DOWN record.  Neither result asserts that every
selected DOWN has a retained diagnostic, a solver outcome, or a second-bank
completion.

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-480`,
`sources/zip4/manuscript/05_binary_transport.tex:27-53,100-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,139-157`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferencePrelaunchFollower (acceptedStart)

namespace Bandits.Support.ReferenceFirstCollectionUnacceptedDownAwaitedPrefix

variable {p : ConstructorDimensions.Parameters}

private theorem lastDown_none_of_acceptedStart_zero
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hstart : acceptedStart state = 0) : state.lastDown = none := by
  cases hlast : state.lastDown with
  | none => rfl
  | some message =>
      have hpositive : 1 ≤ message.val.sigma := message.property.1
      simp only [acceptedStart, hlast] at hstart
      omega

private theorem accepted_up_before_zero_start_impossible
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (i : Fin (p.m - 1)) (currentIndex : ℕ)
    (current : ReferencePrelaunchFollower.State p rate.eta)
    (currentMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hcurrentIndex : currentIndex < (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan).records.length)
    (hcurrent : (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan).records[currentIndex].input.state.followers i =
        .ordinary current currentMemory)
    (hnone : current.lastDown = none)
    (k : Fin (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan).records.length)
    (hk : k.val < currentIndex)
    (message : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (haccepted : ReferenceCollectionPhaseHistory.AcceptedUp
      ((ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records[k.val].input) i message) :
    False := by
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
  have hcurrentStart : acceptedStart current = 0 := by
    simp [acceptedStart, hnone]
  have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input
    execution.connected currentIndex hcurrentIndex
  obtain ⟨first, firstMemory, hfirst, hfirstLe, _, _⟩ :=
    ReferenceFollowerReplyChronology.connected_ordinary_chronology hprefix i current
      currentMemory hcurrent
  have hfirstStart : acceptedStart first = 0 := by omega
  have hfirstNone := lastDown_none_of_acceptedStart_zero rate first hfirstStart
  have hprior := ReferenceAcceptedUpFollowerHistory.run_acceptedUp_prior_down
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan hmode i first firstMemory hfirst hfirstNone k message haccepted
  rcases hprior with
    ⟨j, hjk, prior, _, happlied, _, _, _, _, _, _, _, _, _, _, _, _, _, hpositive⟩
  have htakeLength : (execution.records.take currentIndex).length = currentIndex := by
    rw [List.length_take]
    exact Nat.min_eq_left (Nat.le_of_lt hcurrentIndex)
  have hjTake : j.val < (execution.records.take currentIndex).length := by
    rw [htakeLength]
    exact lt_trans hjk hk
  obtain ⟨next, nextMemory, hnextPrefix, hnextLe⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology hprefix i current
      currentMemory hcurrent j.val hjTake
  have hrecordEq : (execution.records.take currentIndex)[j.val] = execution.records[j.val] :=
    List.getElem_take (xs := execution.records) (j := currentIndex) (i := j.val) (h := hjTake)
  have hnext : execution.records[j.val].output.next.followers i =
      .ordinary next nextMemory := by
    rw [← hrecordEq]
    exact hnextPrefix
  obtain ⟨_, _, _, hchoiceLt, hnextStart⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict
      execution.records[j.val] i prior.val.sigma happlied next nextMemory hnext
  have hpriorPositive : 0 < prior.val.sigma := by omega
  omega

/-- The actual stream's incoming coordinator ledger still contains a focal
follower whose current ordinary state has no accepted DOWN.  The stream is
produced from the full source telescope; the two local state facts remain
visible only after that existential output. -/
theorem actual_collection_unaccepted_down_pending
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
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
      let out := d.stream
      let B := out.window
      ∀ (n : Fin out.ell) (hn : 0 < n.val)
        (i : Fin (p.m - 1)) (before : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        (B[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.state.followers i =
          .ordinary before memory →
        before.lastDown = none →
        i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending ∧
        ∀ k : Fin n.val,
          ReferenceCollectionPhaseHistory.acceptedLabel
            (B[k.val]'(Nat.lt_of_lt_of_le (Nat.lt_trans k.isLt n.isLt)
              out.withinWindow)).input ≠ some i := by
  classical
  have hdispatch :=
    ReferenceFirstCollectionStreamEmptyDispatch.actual_initialized_first_collection_stream_empty_dispatch
      rate source rewards C_star C_h count hcross hspan hshort
  obtain ⟨d⟩ := hdispatch
  refine ⟨d, ?_⟩
  dsimp only
  intro n hn i before memory hfi hnone
  let out := d.stream
  let E := ReferenceFirstCollectionReadyStream.actualEpoch
    (rate := rate) source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let nWindow : Fin out.window.length :=
    ⟨n.val, Nat.lt_of_lt_of_le n.isLt out.withinWindow⟩
  have hindexCurrent : w + n.val < E.records.length := by
    have hlookup := (List.getElem?_eq_some_iff.mp (out.alignment nWindow).1).1
    simpa [E, w, nWindow] using hlookup
  have hcurrentEq : E.records[w + n.val] =
      out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow) := by
    have hlookup := (List.getElem?_eq_some_iff.mp (out.alignment nWindow).1).2
    simpa [E, w, nWindow] using hlookup
  have hcurrent : E.records[w + n.val].input.state.followers i =
      .ordinary before memory := by
    rw [hcurrentEq]
    exact hfi
  have hnoEvent : ∀ k : Fin out.ell, k.val < n.val →
      ReferenceCollectionPhaseHistory.acceptedLabel
        (out.window[k.val]'(Nat.lt_of_lt_of_le k.isLt out.withinWindow)).input ≠ some i := by
    intro k hk hevent
    have hkWindow : k.val < out.window.length := Nat.lt_of_lt_of_le k.isLt out.withinWindow
    let nk : Fin out.window.length := ⟨k.val, hkWindow⟩
    have halign := out.alignment nk
    have hlookupEpoch := (List.getElem?_eq_some_iff.mp halign.1).2
    have hrecord : E.records[w + k.val] = out.window[k.val]'hkWindow := by
      simpa [E, w, nk] using hlookupEpoch
    have hsourceAccepted : ReferenceCollectionPhaseHistory.acceptedLabel
        (E.records[w + k.val].input) = some i := by
      simpa [hrecord] using hevent
    obtain ⟨message, haccepted⟩ :=
      ReferenceCollectionPhaseHistory.acceptedLabel_witness hsourceAccepted
    have hindex : w + k.val < E.records.length := by
      exact (List.getElem?_eq_some_iff.mp halign.1).1
    let j : Fin E.records.length := ⟨w + k.val, hindex⟩
    have haccepted' : ReferenceCollectionPhaseHistory.AcceptedUp
        (E.records[j.val].input) i message := by
      simpa [j] using haccepted
    exact accepted_up_before_zero_start_impossible rate source rewards C_star C_h count
      hcross hspan i (w + n.val) before memory hindexCurrent hcurrent hnone j
      (by simp [j]; omega) message haccepted'
  have hbase : i ∈ (out.ledgers ⟨0, by have := out.positiveLength; omega⟩).pending := by
    rw [out.ledgers_are_outputs]
    simpa using out.cutoffPendingUniv ▸ Finset.mem_univ i
  have hledger : ∀ k, (hk : k < n.val) →
      i ∈ (out.ledgers ⟨k, Nat.lt_trans hk n.isLt⟩).pending := by
    intro k hk
    induction k with
    | zero => simpa using hbase
    | succ k ih =>
        have hk' : k < n.val := by omega
        have hprev := ih hk'
        have hstreamIndex : k + 1 < out.ell := Nat.lt_trans hk n.isLt
        let nk : Fin out.ell := ⟨k + 1, hstreamIndex⟩
        obtain ⟨_, r, incoming, cell, _, hr, hservice, hprevious⟩ :=
          out.cell_at nk (Nat.succ_pos k)
        have hIncoming : incoming = out.ledgers ⟨k, Nat.lt_trans hk' n.isLt⟩ := by
          simpa [nk] using hprevious
        have hnotAccepted :
            ReferenceCollectionPhaseHistory.acceptedLabel r.input ≠ some i := by
          have hkWindow : k + 1 < out.window.length :=
            Nat.lt_of_lt_of_le hstreamIndex out.withinWindow
          have hrEq : r = out.window[k + 1]'hkWindow := by
            have hrow : out.window[k + 1]? = some r := by simpa [nk] using hr
            exact (List.getElem?_eq_some_iff.mp hrow).2.symm
          intro hevent
          exact hnoEvent nk (by omega) (by simpa [hrEq] using hevent)
        have hrec := ReferenceFirstCollectionReadyStream.cell_pending_recurrence cell
        rw [← hservice, hrec, hIncoming]
        cases hevent : ReferenceCollectionPhaseHistory.acceptedLabel r.input with
        | none => simpa [ReferenceCollectionPhaseHistory.eraseEvent, hevent] using hprev
        | some j =>
            have hji : j ≠ i := by
              intro hji
              subst j
              exact hnotAccepted hevent
            simpa [ReferenceCollectionPhaseHistory.eraseEvent, hevent] using
              (And.intro (Ne.symm hji) hprev)
  have hlast : n.val - 1 < n.val := by omega
  refine ⟨?_, ?_⟩
  · simpa using hledger (n.val - 1) hlast
  · intro k
    let kk : Fin out.ell := ⟨k.val, Nat.lt_trans k.isLt n.isLt⟩
    exact hnoEvent kk k.isLt

/-- Any retained DOWN diagnostic in the canonical first-collection window is
the original installed word, with its original start and empty queue field. -/
theorem actual_collection_retained_down_has_stored_word
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
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∃ P0 : ReferenceActivePhysicalStep.Payload rate,
      ∀ (k : Fin B.length) (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
        (_hrecord : E.records[w + k.val]? = some record)
        (i : Fin (p.m - 1))
        (message : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
        ReferenceAcceptedUpFollowerHistory.RetainedDown record i message →
        message = P0.downRecord i ∧ message.val.sigma = s + 1 ∧ message.val.q = 0 := by
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  let w := W.length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  let u := s + w + 1
  have horigin := ReferenceFirstCollectionDownPayloadOrigin.actual_first_collection_down_payload_origin
    rate source rewards C_star C_h count hcross hspan hshort
  dsimp only [s, I, E, W, w, B, u] at horigin
  rcases horigin.origin with
    ⟨cutoffRecord, P0, birth, registers, owned, base, hcutIndex, hcutUnique,
      hcutLive, hcutChosen, hP0Registers, hP0sigma, hP0queues, hfirstCutoff,
      hbirthMem, hbirthInst, hbirthTime, hinstd, hwindowRecord, hselection,
      hretainedWindow, hretainedEarlier⟩
  refine ⟨P0, ?_⟩
  intro k record hrecord i message hretained
  exact hretainedWindow k record hrecord i message hretained

end Bandits.Support.ReferenceFirstCollectionUnacceptedDownAwaitedPrefix

end
