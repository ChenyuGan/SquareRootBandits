/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteSuffixFollowerPreservation

import Lean.Elab.Tactic.Omega

/-!
# Complete source payload fields and selected follower choices

Sources: `sources/zip4/manuscript/05_binary_transport.tex:60-124`,
`sources/zip4/manuscript/06_interruptions.tex:41-62,246-299,327-348`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:54-64,100-108`, and
`sources/zip4/manuscript/07_public_setup.tex:157-163`.

For every record in the original complete-source suffix, stored payload fields
agree with the carried follower state. On an actual selected branch, the real
follower preparations are ordinary and their occupied last DOWN records agree
with the selected payload. The source launch and both adjacent run prefixes are
derived inside the proofs.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceAssignmentPayloadPersistence
open Bandits.Support.ReferenceActiveDataOwnership
open Bandits.Support.ReferenceFollowerFixedReply

namespace Bandits.Support.ReferenceCompletePayloadChoiceChronology

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem complete_record_field_history
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin R.length),
      let r := R[k.val]'k.isLt
      (∀ P : ReferenceActivePhysicalStep.Payload rate,
        ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some P →
          ReferenceActiveDataOwnership.carriedOccupiedFields P r.input.state) ∧
      (∀ P : ReferenceActivePhysicalStep.Payload rate,
        ReferenceAssignmentPayloadPersistence.storedPayload r.output.next.coordinator = some P →
          ReferenceActiveDataOwnership.carriedOccupiedFields P r.output.next) ∧
      (∀ v : ReferenceActivePhysicalStep.Selection r.input,
        r.output.preparation.coordinator.selection = some v →
          ReferenceActiveDataOwnership.carriedOccupiedFields v.view.payload r.input.state ∧
          (∀ i, ReferenceActiveDataOwnership.occupiedFields v.view.payload i
            (ReferenceFollowerFixedReply.actualChoice r i).configuration) ∧
          ReferenceActiveDataOwnership.carriedOccupiedFields v.view.payload r.output.next) := by
  classical
  dsimp only
  intro k
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let r := R[k.val]'k.isLt
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hk := k.isLt
      simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch] at hk
  | some active =>
      have hc : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      obtain ⟨seedActive, hseedLaunch, hsourceFields⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
          rate source rewards C_star C_h hc
      have hseedActiveEq : seedActive = active :=
        Option.some.inj (hseedLaunch.symm.trans hlaunch)
      subst seedActive
      have hseed : ∀ i s memory, active.followers i = .ordinary s memory →
          s.status = .unoccupied := by
        intro i s memory hstate
        rcases hsourceFields i with ⟨hconfiguration, _, _, _, _, _, hunoccupied, _⟩
        have hs : (ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
            (ActualReferenceInitializationBlock.refFollower i)) = s := by
          exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
            (hconfiguration.symm.trans hstate)).1
        simpa [hs] using hunoccupied
      obtain ⟨coordinatorActive, hcoordinatorLaunch, hfirst, _, _, _, _⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
          rate source rewards C_star C_h hc
      have hcoordinatorActiveEq : coordinatorActive = active :=
        Option.some.inj (hcoordinatorLaunch.symm.trans hlaunch)
      have hfirst : active.coordinator = .first := by
        rw [← hcoordinatorActiveEq]
        exact hfirst
      let start := ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h
      let count := p.T - start
      have hspan : start + count ≤ p.T := by
        have hstart : start ≤ p.T := by
          dsimp [start]
          exact ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate source rewards C_star C_h
        dsimp [count]
        omega
      have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active start := by
        dsimp [start]
        exact ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate source rewards C_star C_h active hlaunch
      let execution := ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
      have hrecords : R = execution.records := by
        exact ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate source rewards C_star C_h active hlaunch
      have hlength : R.length = count := by
        rw [hrecords]
        exact ReferenceActivePhysicalHorizon.run_record_count active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
      have hkcount : k.val < count := by
        rw [← hlength]
        exact k.isLt
      have hkPlus : k.val + 1 ≤ count := by omega
      have hprefixSpan : start + k.val ≤ p.T := by omega
      have hsuccessorSpan : start + (k.val + 1) ≤ p.T := by omega
      let previous := ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k.val
        hprefixSpan hmode
      let prefixRun := ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (k.val + 1)
        hsuccessorSpan hmode
      have hsplit : k.val + 1 + (count - (k.val + 1)) = count := by omega
      obtain ⟨suffix, hrunPrefix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
        active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start (k.val + 1) (count - (k.val + 1)) (by simpa [hsplit] using hspan) hmode
      have hfullPrefix : execution.records = prefixRun.records ++ suffix := by
        simpa [execution, prefixRun, hsplit] using hrunPrefix
      have hpreviousLength : previous.records.length = k.val := by
        exact ReferenceActivePhysicalHorizon.run_record_count active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k.val
          hprefixSpan hmode
      have hprefixLength : prefixRun.records.length = k.val + 1 := by
        exact ReferenceActivePhysicalHorizon.run_record_count active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (k.val + 1)
          hsuccessorSpan hmode
      have hprefixIndex : k.val < prefixRun.records.length := by omega
      let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k.val
        hsuccessorSpan hmode
      have hget : r = execution.records[k.val]'(hrecords ▸ k.isLt) := by
        change R[k.val]'k.isLt = execution.records[k.val]'(hrecords ▸ k.isLt)
        exact getElem_congr_coll hrecords
      have hprefixRecords : prefixRun.records = previous.records ++ [actual] := by
        change (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (k.val + 1)
          hsuccessorSpan hmode).records = _
        exact ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
          active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start k.val hsuccessorSpan hmode
      have hprefixGet : prefixRun.records[k.val]'hprefixIndex = actual := by
        calc
          prefixRun.records[k.val]'hprefixIndex =
              (previous.records ++ [actual])[k.val]'(hprefixRecords ▸ hprefixIndex) :=
            getElem_congr_coll hprefixRecords
          _ = actual := by simp [hpreviousLength]
      have hrecord : r = actual := by
        calc
          r = execution.records[k.val]'(hrecords ▸ k.isLt) := hget
          _ = (prefixRun.records ++ suffix)[k.val]'(hfullPrefix ▸ (hrecords ▸ k.isLt)) :=
            getElem_congr_coll hfullPrefix
          _ = prefixRun.records[k.val]'hprefixIndex := List.getElem_append_left hprefixIndex
          _ = actual := hprefixGet
      have hinputState : r.input.state =
          (ReferenceActivePhysicalHorizon.run active source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k.val
            hprefixSpan hmode).finalState := by
        rw [hrecord]
        rfl
      have houtputState : r.output.next =
          (ReferenceActivePhysicalHorizon.run active source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (k.val + 1)
            hsuccessorSpan hmode).finalState := by
        rw [hrecord]
        exact (ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
          active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start k.val hsuccessorSpan hmode).symm
      have hactualMember : actual ∈ (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (k.val + 1)
          hsuccessorSpan hmode).records := by
        rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
          active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards start k.val hsuccessorSpan hmode]
        exact List.mem_append.mpr (Or.inr (by simp [actual]))
      have hmember : r ∈ (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (k.val + 1)
          hsuccessorSpan hmode).records := hrecord ▸ hactualMember
      have hhistoryIn := ReferenceOccupiedFieldHistory.run_prefix_occupied_field_history
        active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start count hspan hmode hfirst hseed k.val (by omega)
      have hhistoryOut := ReferenceOccupiedFieldHistory.run_prefix_occupied_field_history
        active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start count hspan hmode hfirst hseed (k.val + 1) (by omega)
      refine ⟨?_, ?_, ?_⟩
      · intro P hstored
        rw [hinputState] at hstored ⊢
        exact hhistoryIn.1 P hstored
      · intro P hstored
        rw [houtputState] at hstored ⊢
        exact hhistoryOut.1 P hstored
      · intro v hv
        have hselected := hhistoryOut.2 r hmember v hv
        have hchoices : ∀ i, ReferenceActiveDataOwnership.occupiedFields v.view.payload i
            (ReferenceFollowerFixedReply.actualChoice r i).configuration := by
          intro i
          simpa [ReferenceFollowerFixedReply.actualChoice] using hselected.2.1 i
        exact ⟨hselected.1, hchoices, hselected.2.2⟩

/-- Every stored payload at an actual complete-source record has the literal
carried occupied fields on both its incoming and output states. -/
theorem complete_stored_payload_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin R.length),
      let r := R[k.val]'k.isLt
      (∀ P : ReferenceActivePhysicalStep.Payload rate,
        ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some P →
          ReferenceActiveDataOwnership.carriedOccupiedFields P r.input.state) ∧
      (∀ P : ReferenceActivePhysicalStep.Payload rate,
        ReferenceAssignmentPayloadPersistence.storedPayload r.output.next.coordinator = some P →
          ReferenceActiveDataOwnership.carriedOccupiedFields P r.output.next) := by
  classical
  dsimp only
  intro k
  have h := complete_record_field_history (rate := rate) rewards C_star C_h source k
  exact ⟨h.1, h.2.1⟩

/-- On an actual selected branch, all followers have the real ordinary
choice-time states and memories, and every occupied choice carries the
selected payload's DOWN record. The same proof retains the selected payload's
incoming and output field agreement. -/
theorem complete_selected_payload_choice_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin R.length),
      let r := R[k.val]'k.isLt
      ∀ (v : ReferenceActivePhysicalStep.Selection r.input),
        r.output.preparation.coordinator.selection = some v →
        ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
          (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
          (∀ i, (ReferenceFollowerFixedReply.actualChoice r i).configuration =
            .ordinary (states i) (memories i)) ∧
          (∀ i, (states i).status ≠ .unoccupied →
            (states i).lastDown = some (v.view.payload.downRecord i)) ∧
          ReferenceActiveDataOwnership.carriedOccupiedFields v.view.payload r.input.state ∧
          ReferenceActiveDataOwnership.carriedOccupiedFields v.view.payload r.output.next := by
  classical
  dsimp only
  intro k v hv
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let r := R[k.val]'k.isLt
  have hrecordHistory :=
    complete_record_field_history (rate := rate) rewards C_star C_h source k
  have hselected := hrecordHistory.2.2 v hv
  have hchoices := ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
    (rate := rate) rewards C_star C_h source k
  have hconfig : ∀ i, ∃ s memory,
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary s memory := by
    intro i
    rcases hchoices i with ⟨_, memory, choice, _, _, _, hactual, _, _⟩
    refine ⟨choice, memory, ?_⟩
    simpa [r, R] using hactual
  let states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta :=
    fun i => Classical.choose (hconfig i)
  let memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p :=
    fun i => Classical.choose (Classical.choose_spec (hconfig i))
  have hactualConfig : ∀ i,
      (ReferenceFollowerFixedReply.actualChoice r i).configuration =
        .ordinary (states i) (memories i) := by
    intro i
    exact Classical.choose_spec (Classical.choose_spec (hconfig i))
  refine ⟨states, memories, hactualConfig, ?_, hselected.1, hselected.2.2⟩
  intro i hoccupied
  have hfields := hselected.2.1 i
  rw [hactualConfig i] at hfields
  simpa [ReferenceActiveDataOwnership.occupiedFields] using hfields hoccupied

end Bandits.Support.ReferenceCompletePayloadChoiceChronology

end
