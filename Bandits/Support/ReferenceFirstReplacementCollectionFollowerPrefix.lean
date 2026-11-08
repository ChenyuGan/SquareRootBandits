/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCutoffDownRecovery

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# Follower recovery ingredients after a replacement cutoff

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-70,193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This file records two source-level ingredients for the subsequent collection
follower-prefix construction. Actual records in the complete suffix are
adjacent, and a later accepted copy of the installed DOWN record still scans
only to its first cutoff coordinate. The latter is independent of later row
bits; checked recovery uses the calendar-credit API at that earlier endpoint.
These ingredients do not establish survival or the follower invariant over
the collection tail, and they do not close a manuscript regret statement.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementCollectionFollowerPrefix

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower ActiveFollowerDownAcceptance

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- An indexed member of a take-while collection window is the original
complete-suffix record at its physical offset. -/
theorem collectionWindow_get
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (cutIndex j : ℕ) (hj : j <
      ((records.drop (cutIndex + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length) :
    records[cutIndex + 1 + j]? = some
      (((records.drop (cutIndex + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).get
          ⟨j, hj⟩) := by
  let window := (records.drop (cutIndex + 1)).takeWhile
    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
  have hprefix : window <+: records.drop (cutIndex + 1) :=
    List.takeWhile_prefix _
  have hj' : j < records.length - (cutIndex + 1) := by
    have := Nat.lt_of_lt_of_le hj hprefix.length_le
    simpa only [window, List.length_drop] using this
  have hindex : cutIndex + 1 + j < records.length := by omega
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨hindex, ?_⟩
  simpa only [window, List.get_eq_getElem, List.getElem_drop, Nat.add_assoc] using
    (hprefix.getElem hj).symm

/-- A real selected coordinator view can expose only this payload's stored
DOWN word (or no word) to a follower. The pending set and the coordinator's
actual choice remain those of the retained selection. -/
theorem actualSelection_expectedDownWord_none_or_payload
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hselection : record.output.preparation.coordinator.selection = some selected)
    (hpayload : selected.view.payload = payload)
    (i : Fin (p.m - 1)) :
    ReferenceDownReception.expectedDownFlatWord
        record.output.preparation.coordinator.downView i record.input.row record.input.time = none ∨
      ReferenceDownReception.expectedDownFlatWord
        record.output.preparation.coordinator.downView i record.input.row record.input.time =
          some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
  have hview : record.output.preparation.coordinator.downView = some selected.view := by
    change Option.map (fun s : ReferenceActivePhysicalStep.Selection record.input => s.view)
        record.output.preparation.coordinator.selection = some selected.view
    rw [hselection]
    rfl
  rw [hview]
  unfold ReferenceDownReception.expectedDownFlatWord
  by_cases hchoice :
      CoordinatorLocalArmChoice.coordinatorArmChoice selected.view.payload
          selected.view.pendingAtChoice selected.view.cutoff record.input.time
          selected.view.complementWeights record.input.row ≠ none ∧
        ReferenceDownReception.selectedDownSenderBranch selected.view i
          record.input.row record.input.time
  · right
    simp [hchoice, hpayload]
    rfl
  · left
    simp [hchoice]

/-- Adjacent records in the corrected physical suffix use the previous
record's actual successor state. The source-record reconstruction and the
accepted horizon's successor equation provide the link; no success chain is
assumed. -/
private theorem connected_adjacent
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (k : ℕ) (hk : k + 1 < records.length) :
    (records.get ⟨k + 1, hk⟩).input.state =
      (records.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).output.next := by
  induction records generalizing initial final k with
  | nil => simp at hk
  | cons head tail ih =>
      cases k with
      | zero =>
          cases tail with
          | nil => simp at hk
          | cons next rest =>
              change next.input.state = head.output.next
              exact hconnected.2.1
      | succ k =>
          have hk' : k + 1 < tail.length := by simp at hk ⊢; omega
          simpa using ih hconnected.2 k hk'

theorem completeSuffix_adjacent
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ)
    (hk : k + 1 <
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length) :
    let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    (records.get ⟨k + 1, hk⟩).input.state =
        (records.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).output.next ∧
      (records.get ⟨k + 1, hk⟩).input.time.val =
        (records.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).input.time.val + 1 := by
  dsimp only
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none => simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch] at hk
  | some active =>
      have hconnected := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate source rewards C_star C_h active hlaunch
      have hstate := connected_adjacent hconnected k hk
      obtain ⟨hc0, hspan0, hr0⟩ :=
        ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h
          source ⟨k, (Nat.lt_succ_self k).trans hk⟩
      obtain ⟨hc1, hspan1, hr1⟩ :=
        ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h
          source ⟨k + 1, hk⟩
      have hhc : hc0 = hc1 := Subsingleton.elim _ _
      rw [← hhc] at hr1
      have htime :
          (records.get ⟨k + 1, hk⟩).input.time.val =
            (records.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).input.time.val + 1 := by
        rw [hr0, hr1]
        rfl
      exact ⟨hstate, htime⟩

/-- If the source row's first replacement cutoff is `u`, every accepted scan
of that same DOWN record at a later physical round ending no earlier than
`u` has endpoint `u`. Bits after `u` do not enter this equality. -/
theorem acceptedScan_endpoint_of_firstCutoff
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (sigma : Fin p.T) (t : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (u : ℕ)
    (hdownStart : ActiveFollowerDownAcceptance.downStart p rate M = sigma)
    (hstart : (ActiveFollowerDownAcceptance.downStart p rate M).val ≤ t.val)
    (hfirst : FollowerCutoffScan.firstCutoff p rate.eta.val sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) = u)
    (hendpoint : u ≤ t.val + 2) :
    (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t hstart row).endpoint =
      u := by
  unfold ActiveFollowerDownAcceptance.acceptedCutoffScan
    FollowerCutoffScan.completeRowCutoffScan
  have hendpoint' : u ≤ t.val + 2 := hendpoint
  have hfirst' : FollowerCutoffScan.firstCutoff p rate.eta.val
      (ActiveFollowerDownAcceptance.downStart p rate M)
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) = u := by
    rw [hdownStart]
    exact hfirst
  rw [FollowerCutoffScan.followerCutoffScan_endpoint_eq_min_firstCutoff]
  rw [hfirst']
  exact Nat.min_eq_left hendpoint'

/-- The admitted DOWN record stores a one-based start, while the scan uses its
zero-based coordinate. The first-cutoff bound therefore places the stored
start strictly before that endpoint. -/
theorem downRecord_start_before_firstCutoff
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (sigma : Fin p.T) (row : CompletePublicTable.CompleteRow p) (u : ℕ)
    (hdownStart : ActiveFollowerDownAcceptance.downStart p rate M = sigma)
    (hfirst : FollowerCutoffScan.firstCutoff p rate.eta.val sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) = u) :
    M.val.sigma ≤ u - 1 := by
  have hbounds := FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
    rate.eta.property rate.sourceCap sigma
    (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row)
  have hstored : M.val.sigma = sigma.val + 1 := by
    have h := ActiveFollowerDownAcceptance.downStart_val_add_one p rate M
    rw [hdownStart] at h
    omega
  rw [hfirst] at hbounds
  omega

/-- Calendar credit can recover a later accepted DOWN record at its original
first-cutoff endpoint, with every checked replay prefix. The `Fin` coordinate
is arithmetic only; it is not a fabricated physical record. -/
theorem checkedRecovery_at_firstCutoff
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (u : ℕ)
    (hvalid : ActiveFollowerLifecycle.localBufferValid state)
    (hstart : M.val.sigma ≤ u - 1)
    (hcredit : M.val.q ≤ (M.val.sigma - 1) * D p)
    (hu : 3 ≤ u) (huT : u ≤ p.T) :
    ∃ final, ActiveFollowerDownAcceptance.checkedRecovery p rate M state u = .ok final ∧
      final.registers.1 + final.registers.2 ≤ (u - 1) * D p ∧
      final.lastService ≤ D p ∧
      ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) final ∧
      final.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
        (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M state u) ∧
      (∀ k, ∃ middle,
        ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
          ⟨(0, M.val.q), 0⟩
          ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M state u).take k) =
            .ok middle ∧
        ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
        middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
          ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M state u).take k)) := by
  let t : Fin p.T := ⟨u - 2, by omega⟩
  have ht1 : t.val + 1 = u - 1 := by dsimp [t]; omega
  have ht2 : t.val + 2 = u := by dsimp [t]; omega
  obtain ⟨final, hchecked, hmass, hservice, hdomain, hregisters, hprefix⟩ :=
    ReferenceFirstReplacementLiveFollowerPrefix.checked_recovery_of_calendar_credit
      (p := p) (rate := rate) M state t hvalid (by rw [ht1]; exact hstart) hcredit
  refine ⟨final, ?_, ?_, hservice, hdomain, ?_, ?_⟩
  · simpa only [ht2] using hchecked
  · simpa only [ht1] using hmass
  · simpa only [ht2] using hregisters
  · intro k
    obtain ⟨middle, hrun, hdom, hregs⟩ := hprefix k
    exact ⟨middle, by simpa only [ht2] using hrun, hdom,
      by simpa only [ht2] using hregs⟩

/-- Source first-cutoff geometry supplies the start-to-endpoint span required
by the calendar-credit recovery theorem. The sole remaining numerical
premises are the actual local-buffer validity, installed queue credit, and the
lower endpoint bound used to form the arithmetic `Fin` coordinate. -/
theorem checkedRecovery_at_sourceFirstCutoff
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (state : ReferencePrelaunchFollower.State p rate.eta) (sigma : Fin p.T)
    (row : CompletePublicTable.CompleteRow p) (u : ℕ)
    (hdownStart : ActiveFollowerDownAcceptance.downStart p rate M = sigma)
    (hfirst : FollowerCutoffScan.firstCutoff p rate.eta.val sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) = u)
    (hvalid : ActiveFollowerLifecycle.localBufferValid state)
    (hcredit : M.val.q ≤ (M.val.sigma - 1) * D p)
    (hu : 3 ≤ u) (huT : u ≤ p.T) :
    ∃ final, ActiveFollowerDownAcceptance.checkedRecovery p rate M state u = .ok final ∧
      final.registers.1 + final.registers.2 ≤ (u - 1) * D p ∧
      final.lastService ≤ D p ∧
      ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) final ∧
      final.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
        (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M state u) ∧
      (∀ k, ∃ middle,
        ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
          ⟨(0, M.val.q), 0⟩
          ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M state u).take k) =
            .ok middle ∧
        ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
        middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
          ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M state u).take k)) := by
  have hstart := downRecord_start_before_firstCutoff M sigma row u hdownStart hfirst
  exact checkedRecovery_at_firstCutoff M state u hvalid hstart hcredit hu huT

end Bandits.Support.ReferenceFirstReplacementCollectionFollowerPrefix

end
