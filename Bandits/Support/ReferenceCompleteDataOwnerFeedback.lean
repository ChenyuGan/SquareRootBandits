/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompletePayloadChoiceChronology

import Lean.Elab.Tactic.Omega

/-!
# Complete-source DATA owner feedback

Sources: `sources/zip4/manuscript/05_binary_transport.tex:60-124`,
`sources/zip4/manuscript/06_interruptions.tex:110-163,246-299`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:20-64`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-177`.

At an actual selected record of the complete original-source suffix, the
choice fields and actual ordinary follower preparations are produced from that
record. On the literal live DATA, action, ownership, and recording-mask
branches, the physical owner has the original grid reward and typed
observation. The same branch yields each actual follower's whole-reward source
arrival floor, including zero. This is pointwise source geometry; it asserts
no recording law or queue survival claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFollowerFixedReply
open Bandits.Support.ReferenceActiveDataOwnership
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceCorrectedInitializationLaunch
open Bandits.Support.PublicDiscreteDraws

namespace Bandits.Support.ReferenceCompleteDataOwnerFeedback

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem complete_record_rewards
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).input.rewards = rewards := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hindex : k.val <
          ([] : List (ReferenceActivePhysicalHorizon.RoundRecord
            (p := p) (rate := rate))).length := by
        simpa [R, ReferenceCompletePhysicalHistory.completeSuffixRecords, hlaunch]
          using k.isLt
      simp at hindex
  | some active =>
      let start := ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h
      have hspan : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        dsimp only [start]
        omega
      let hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source rewards C_star C_h active hlaunch
      let run := ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
        (p.T - start) hspan hmode
      have hrecords : R = run.records := by
        dsimp only [R, run, start, hmode]
        exact ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate source rewards C_star C_h active hlaunch
      have hrecordMem : R[k.val]'k.isLt ∈ run.records := by
        rw [← hrecords]
        exact List.getElem_mem k.isLt
      obtain ⟨_, _, hrecordRewards⟩ := ReferenceActivePhysicalHorizon.run_record_inputs
        active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards start (p.T - start) hspan hmode R[k.val] hrecordMem
      exact hrecordRewards

/-- Source-root geometry at an actual selected complete-suffix record.

The actual ordinary states, memories, and occupied DOWN-field agreement are
produced first from `complete_selected_payload_choice_fields`. The live/DATA
and owner/action/ownership/mask propositions remain the literal pointwise
branches of the source protocol. No preparation, payload-field, or reward-table
identity is supplied by the caller.
-/
theorem complete_selected_source_data_owner_geometry
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
          r.output.preparation = ReferenceActivePhysicalStep.prepare r.input ∧
          (∀ i, (ReferenceFollowerFixedReply.actualChoice r i).configuration =
            .ordinary (states i) (memories i)) ∧
          (∀ i, ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
            .ordinary (states i) (memories i)) ∧
          (∀ i, (states i).status ≠ .unoccupied →
            (states i).lastDown = some (v.view.payload.downRecord i)) ∧
          ∀ (_hlive : CoordinatorLocalArmChoice.assignmentIsLive
              v.view.payload v.view.cutoff r.input.time)
            (_hdata : slotDraw (r.input.row.2 r.input.time).1 = dataSlot),
            (∀ (owner : Fin p.m) (j : Fin p.K)
              (_haction : (ReferenceActivePhysicalStep.prepare r.input).arms.actions owner = j)
              (_howns : SnapshotRecordingKernel.owns p
                (.live v.view.payload.assignment
                  (ReferenceActiveDataOwnership.choiceSnapshot v states)) owner j)
              (_hmask : CanonicalRecordingSlice.recordingMask (K_pos p) owner j
                (r.input.row.2 r.input.time).1),
              FiniteBanditModel.collisionFreeFor
                  (ReferenceActivePhysicalStep.prepare r.input).arms.actions owner ∧
                (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback owner =
                  rewards r.input.time j ∧
                ((ReferenceActivePhysicalStep.prepare r.input).feedback.observations owner).val.val =
                  ((rewards r.input.time j).val : ℝ) / (D p : ℝ)) ∧
            ∀ (i : Fin (p.m - 1))
              (_haction : (ReferenceActivePhysicalStep.prepare r.input).arms.actions
                (followerPlayer p.two_le_m i) = v.view.payload.assignment.assigned i)
              (_hmask : CanonicalRecordingSlice.recordingMask (K_pos p)
                (followerPlayer p.two_le_m i)
                (v.view.payload.assignment.assigned i)
                (r.input.row.2 r.input.time).1),
              ActiveFollowerQueueOperation.sourceArrivalFloor rate.eta
                  (v.view.payload.downRecord i)
                  ((ReferenceActivePhysicalStep.prepare r.input).feedback.observations
                    (followerPlayer p.two_le_m i)) =
                Nat.floor ((D p : ℝ) * rate.eta.val *
                  (((rewards r.input.time
                    (v.view.payload.assignment.assigned i)).val : ℝ) / (D p : ℝ)) /
                  OrdinaryMessageCodec.dyadicRate (v.view.payload.downRecord i).val.h) := by
  classical
  dsimp only
  intro k
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let r := R[k.val]'k.isLt
  intro v hv
  obtain ⟨states, memories, hactualOrdinary, hfields, _, _⟩ :=
    ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
      (rate := rate) rewards C_star C_h source k v hv
  have hprepare : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have hordinary : ∀ i,
      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
    intro i
    calc
      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
          (r.output.preparation.followers.followers i).configuration := by rw [hprepare]
      _ = .ordinary (states i) (memories i) := by
        simpa only [ReferenceFollowerFixedReply.actualChoice] using hactualOrdinary i
  have hselected : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection = some v := by
    calc
      (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection =
          r.output.preparation.coordinator.selection := by rw [hprepare]
      _ = some v := hv
  have hrecordRewards := complete_record_rewards rewards C_star C_h source k
  refine ⟨states, memories, hprepare, hactualOrdinary, hordinary, hfields, ?_⟩
  intro hlive hdata
  constructor
  · intro owner j haction howns hmask
    have hcollision := ReferenceActiveDataOwnership.actual_data_owner_collisionFree
      r.input v hselected states memories hordinary hfields hlive hdata owner j
      haction howns hmask
    have hfeedback := ReferenceActiveDataOwnership.actual_data_owner_feedback
      r.input v hselected states memories hordinary hfields hlive hdata owner j
      haction howns hmask
    have hreward : r.input.rewards r.input.time j = rewards r.input.time j :=
      congrArg (fun table : ActualInitializationPhysicalStep.GridRewardTable p =>
        table r.input.time j) hrecordRewards
    have hrewardReal :
        ((r.input.rewards r.input.time j).val : ℝ) =
          ((rewards r.input.time j).val : ℝ) :=
      congrArg (fun value : Fin (D p + 1) => (value.val : ℝ)) hreward
    have hnormalized := congrArg (fun value : ℝ => value / (D p : ℝ)) hrewardReal
    have hgrid : (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback owner =
        rewards r.input.time j := hfeedback.1.trans hreward
    have htyped :
        ((ReferenceActivePhysicalStep.prepare r.input).feedback.observations owner).val.val =
          ((rewards r.input.time j).val : ℝ) / (D p : ℝ) := by
      exact hfeedback.2.trans hnormalized
    exact ⟨hcollision, hgrid, htyped⟩
  · intro i hiaction himask
    have hfloor := ReferenceActiveDataOwnership.actual_follower_sourceArrivalFloor
      r.input v hselected states memories hordinary hfields hlive hdata i hiaction himask
    have hreward : r.input.rewards r.input.time
        (v.view.payload.assignment.assigned i) =
          rewards r.input.time (v.view.payload.assignment.assigned i) :=
      congrArg (fun table : ActualInitializationPhysicalStep.GridRewardTable p =>
        table r.input.time (v.view.payload.assignment.assigned i)) hrecordRewards
    have hrewardReal :
        ((r.input.rewards r.input.time
          (v.view.payload.assignment.assigned i)).val : ℝ) =
          ((rewards r.input.time (v.view.payload.assignment.assigned i)).val : ℝ) :=
      congrArg (fun value : Fin (D p + 1) => (value.val : ℝ)) hreward
    have hnormalized := congrArg (fun value : ℝ => value / (D p : ℝ)) hrewardReal
    have hfloorRhs := congrArg Nat.floor (by
      rw [hnormalized] :
        (D p : ℝ) * rate.eta.val *
            (((r.input.rewards r.input.time
              (v.view.payload.assignment.assigned i)).val : ℝ) / (D p : ℝ)) /
            OrdinaryMessageCodec.dyadicRate (v.view.payload.downRecord i).val.h =
          (D p : ℝ) * rate.eta.val *
            (((rewards r.input.time (v.view.payload.assignment.assigned i)).val : ℝ) /
              (D p : ℝ)) /
            OrdinaryMessageCodec.dyadicRate (v.view.payload.downRecord i).val.h)
    exact hfloor.trans hfloorRhs

end Bandits.Support.ReferenceCompleteDataOwnerFeedback

end
