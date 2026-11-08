/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteDataOwnerFeedback

import Lean.Elab.Tactic.Omega

/-!
# Complete-source occupied follower DATA arrival and service

Sources: `sources/zip4/manuscript/05_binary_transport.tex:60-124,354-429`,
`sources/zip4/manuscript/06_interruptions.tex:110-163,246-299`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-177`.

At one actual selected live complete-suffix record, the complete-source DATA
geometry and occupied-service producer identify the literal follower arrival,
recording event, checked service, release/finish, and physical queue update.
The result is pointwise and makes no probability or whole-run claim.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteOccupiedFollowerDataArrival

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceFollowerFixedReply
open Bandits.Support.ReferenceActiveDataOwnership
open Bandits.Support.ReferenceFollowerOccupiedRecorderEvent
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveRoundActions
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.SnapshotRecordingKernel

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

local instance recorderPropDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- On the original complete-source telescope, an occupied selected follower
has the actual source-floor arrival, checked service, record/release tail, and
queue transition at this same physical round. The recording event is the
occupied canonical arm event with the selected payload anchor in both weight
inputs. -/
theorem complete_selected_occupied_follower_arrival_service
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin R.length),
      let r := R[k.val]'k.isLt
      ∀ (v : ReferenceActivePhysicalStep.Selection r.input),
        r.output.preparation.coordinator.selection = some v →
        CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
          r.input.time →
        ∃ (states : Fin (p.m - 1) →
            ReferencePrelaunchFollower.State p rate.eta)
          (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
          r.output.preparation = ReferenceActivePhysicalStep.prepare r.input ∧
          (∀ i, (ReferenceFollowerFixedReply.actualChoice r i).configuration =
            .ordinary (states i) (memories i)) ∧
          (∀ i, ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
            .ordinary (states i) (memories i)) ∧
          (∀ i, (states i).status ≠ .unoccupied →
            (states i).lastDown = some (v.view.payload.downRecord i)) ∧
          ∀ i, (states i).status ≠ .unoccupied →
            let prep := ReferenceActivePhysicalStep.prepare r.input
            let t := r.input.time
            let row := r.input.row
            let s := states i
            let mem := memories i
            let M := v.view.payload.downRecord i
            let a := v.view.payload.assignment.assigned i
            let y := prep.feedback.observations (followerPlayer p.two_le_m i)
            let f := prep.followers.followers i
            let cap := 4 * rate.n
            let G := ActiveFollowerQueueOperation.recorderGate rate.eta i row t M
            let F := Nat.floor ((D p : ℝ) * rate.eta.val *
              (((rewards t a).val : ℝ) / (D p : ℝ)) /
                OrdinaryMessageCodec.dyadicRate M.val.h)
            let delta := if G then F else 0
            let gamma := min cap (s.backlog + delta)
            ∃ (serviced : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta
                rate.n f.follower f.row f.activation f.time y s)
              (next : ReferencePrelaunchFollower.State p rate.eta)
              (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
              ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
                rate.n rate.n_scale f.follower f.row f.activation f.time y s =
                  .success serviced ∧
              serviced.arrival = delta ∧
              serviced.service = gamma ∧
              serviced.output = ActiveFollowerQueueOperation.serviceUpdate rate.n s delta ∧
              (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
                f.follower f.row f.activation f.time f.active f.arm y s).result =
                  .ok serviced.output ∧
              (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
                f.follower f.row f.activation f.time f.active f.arm y s).downInput = none ∧
              (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
                f.follower f.row f.activation f.time f.active f.arm y s).down = none ∧
              DeclaredFollowerLocalRound.releaseAndFinish rate f.follower f.row f.time
                y s mem serviced.output = .ok (next, nextMemory) ∧
              (r.output.followers i).configuration = .ordinary next nextMemory ∧
              (r.output.followers i).failure = none ∧
              r.output.next.followers i = .ordinary next nextMemory ∧
              next.S = s.S + gamma ∧
              next.delta = gamma ∧
              next.backlog = s.backlog + delta - gamma ∧
              (next.S, next.backlog) =
                QueueReplay.transition cap (s.S, s.backlog) (true, delta) ∧
              next.lastDown = s.lastDown ∧
              next.buffer = s.buffer ∧
              (next.status = .released ↔
                s.status = .released ∨
                  (s.status = .pending ∧
                    ActiveFollowerLifecycle.releaseCondition rate.eta i
                      (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) y M)) ∧
              (next.status = .pending ↔
                s.status = .pending ∧
                  ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
                    (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) y M) ∧
              (G ↔ SnapshotRecordingKernel.recordingMap p
                (.live v.view.payload.assignment
                  (ReferenceActiveDataOwnership.choiceSnapshot v states))
                true rate.eta.val rate.eta.property v.view.payload.eta_le_source_cap
                v.view.payload.anchor v.view.payload.anchor
                v.view.payload.anchor_pos v.view.payload.anchor_pos
                (fun _ => le_rfl) (fun j => by
                  rw [two_mul]
                  exact le_add_of_nonneg_right
                    (le_of_lt (v.view.payload.anchor_pos j)))
                ((row.2 t).1) = some a) := by
  classical
  dsimp only
  intro k
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let r := R[k.val]'k.isLt
  intro v hv hlive
  obtain ⟨states, memories, hprepare, hactualOrdinary, hpreparedOrdinary,
    hfields, hgeometry⟩ :=
    ReferenceCompleteDataOwnerFeedback.complete_selected_source_data_owner_geometry
      (rate := rate) rewards C_star C_h source k v hv
  refine ⟨states, memories, hprepare, hactualOrdinary, hpreparedOrdinary, hfields, ?_⟩
  intro i hoccupied
  let prep := ReferenceActivePhysicalStep.prepare r.input
  let t := r.input.time
  let row := r.input.row
  let s := states i
  let mem := memories i
  let M := v.view.payload.downRecord i
  let a := v.view.payload.assignment.assigned i
  let y := prep.feedback.observations (followerPlayer p.two_le_m i)
  let f := prep.followers.followers i
  let cap := 4 * rate.n
  let G := ActiveFollowerQueueOperation.recorderGate rate.eta i row t M
  let F := Nat.floor ((D p : ℝ) * rate.eta.val *
    (((rewards t a).val : ℝ) / (D p : ℝ)) /
      OrdinaryMessageCodec.dyadicRate M.val.h)
  let delta := if G then F else 0
  let gamma := min cap (s.backlog + delta)
  have hactualChoice :
      (ReferenceFollowerFixedReply.actualChoice r i).configuration =
        .ordinary s mem := hactualOrdinary i
  obtain ⟨Mdown, hdown, htime, hdomains, b, j, birthPayload, beta,
    hbj, hjk, hbirth, hbase, hretained, hmessage, hchoiceMass, hdeltaBound,
    hmass, hfollower, hrow, htimeField, hactivation, serviced, next,
    nextMemory, hchecked, harrival, hservice, hserviceOutput, harrivalBound,
    hserviceBound, hrecordResult, hrecordDownInput, hrecordDown,
    hreleaseFinish, hstepConfiguration, hstepFailure, hstepDownInput,
    hstepDown, hscore, hdeltaNext, hbacklogNext, hqueueTransition,
    hconservation, hmassNext, hnextDomain, hnextDown, hbufferNext,
    hbatchNext, hinitializationFailure, hreleased, hpending, hnextOccupied,
    hproposalRead, houtputConfiguration, houtputFailure, houtputDownInput,
    houtputDown, hnextOutput⟩ :=
    ReferenceCompleteOccupiedServiceForward.complete_ordinary_occupied_service_forward
      (rate := rate) rewards C_star C_h source k i s mem hactualChoice hoccupied
  have hdownAgreement : Mdown = M := by
    apply Option.some.inj
    exact hdown.symm.trans (hfields i hoccupied)
  have hoccupiedStatus : s.status.occupied := by
    cases hstatus : s.status with
    | unoccupied => exact False.elim (hoccupied hstatus)
    | pending => exact Or.inl rfl
    | released => exact Or.inr rfl
  have hserviceArrivalGate :=
    ReferenceFollowerOccupiedRecorderEvent.serviceSuccess_arrival_eq_gate serviced M
      hoccupiedStatus (hfields i hoccupied)
  have harrivalGate : serviced.arrival =
      if G then ActiveFollowerQueueOperation.sourceArrivalFloor rate.eta M y else 0 := by
    simpa only [G, prep, t, row, y, f, hfollower, hrow, htimeField] using
      hserviceArrivalGate
  have harrivalDelta : serviced.arrival = delta := by
    by_cases hG : G
    · have hgateFields :
          PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.dataSlot ∧
            PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K (row.2 t).1 =
              followerPlayer p.two_le_m i ∧
            CanonicalRecordingSlice.recordingMask (K_pos p)
              (followerPlayer p.two_le_m i) (PrelaunchBufferRecovery.downArm rate.eta M)
              (row.2 t).1 ∧
            (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
              (row.2 t).1).val ≤ ActiveFollowerQueueOperation.thinningProbability rate.eta M := by
          change _ ∧ _ ∧ _ ∧ _ at hG
          exact hG
      rcases hgateFields with ⟨hdata, hsource, hmaskDown, hthin⟩
      have hdownArm : PrelaunchBufferRecovery.downArm rate.eta M = a :=
        ReferenceActiveDataOwnership.downRecord_arm v.view.payload i
      have hmask : CanonicalRecordingSlice.recordingMask (K_pos p)
          (followerPlayer p.two_le_m i) a (row.2 t).1 := by
        simpa only [hdownArm] using hmaskDown
      have hlocalOrdinary :
          (DeclaredFollowerLocalRound.prepare rate i row (r.input.state.activations i)
            t (r.input.active i) (r.input.state.followers i)).configuration =
              .ordinary s mem := by
        exact hpreparedOrdinary i
      have hlocalArm := ReferenceActiveDataOwnership.ordinary_data_arm
        v.view.payload i row (r.input.state.activations i) t (r.input.active i)
        (r.input.state.followers i) s mem hlocalOrdinary (hfields i) hdata
      have haction :
          (ReferenceActivePhysicalStep.prepare r.input).arms.actions
            (followerPlayer p.two_le_m i) = a := by
        rw [ReferenceActivePhysicalStep.PreparedRound.action_follower]
        have hnotUnoccupied : s.status ≠ .unoccupied := hoccupied
        rw [ite_eq_right hnotUnoccupied] at hlocalArm
        simpa only [a] using hlocalArm
      have hsourceFloor :
          ActiveFollowerQueueOperation.sourceArrivalFloor rate.eta M y = F := by
        exact (hgeometry hlive hdata).2 i haction hmask
      calc
        serviced.arrival =
            if G then ActiveFollowerQueueOperation.sourceArrivalFloor rate.eta M y else 0 :=
          harrivalGate
        _ = delta := by simp only [delta, hG, ite_eq_left hG, hsourceFloor, ite_true]
    · calc
        serviced.arrival = ActiveFollowerQueueOperation.rawArrival rate.eta i row t Mdown y :=
          harrival
        _ = ActiveFollowerQueueOperation.rawArrival rate.eta i row t M y := by
          rw [hdownAgreement]
        _ = 0 := by
          rw [ActiveFollowerQueueOperation.rawArrival_eq_sourceFormula]
          simp only [G, hG, ite_false]
        _ = delta := by simp only [delta, G, hG, ite_false]
  have hserviceGamma : serviced.service = gamma := by
    have h := hservice
    rw [← harrival, harrivalDelta] at h
    simpa only [gamma, cap] using h
  have hserviceOutputDelta : serviced.output =
      ActiveFollowerQueueOperation.serviceUpdate rate.n s delta := by
    have h := hserviceOutput
    rw [← harrival, harrivalDelta] at h
    exact h
  have hscoreGamma : next.S = s.S + gamma := by
    have h := hscore
    rw [← harrival, harrivalDelta] at h
    simpa only [gamma, cap] using h
  have hdeltaGamma : next.delta = gamma := by
    have h := hdeltaNext
    rw [← harrival, harrivalDelta] at h
    simpa only [gamma, cap] using h
  have hbacklogGamma : next.backlog = s.backlog + delta - gamma := by
    have h := hbacklogNext
    rw [← harrival, harrivalDelta] at h
    simpa only [gamma, cap] using h
  have hqueue : (next.S, next.backlog) =
      QueueReplay.transition cap (s.S, s.backlog) (true, delta) := by
    have h := hqueueTransition
    rw [← harrival, harrivalDelta] at h
    simpa only [ActiveFollowerQueueOperation.serviceCapacity, cap] using h
  have hrecordOutput :
      (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
        f.follower f.row f.activation f.time f.active f.arm y s).result =
          .ok serviced.output := by
    simpa only [prep, f, y] using hrecordResult
  have hrecordNoDownInput :
      (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
        f.follower f.row f.activation f.time f.active f.arm y s).downInput = none := by
    simpa only [prep, f, y] using hrecordDownInput
  have hrecordNoDown :
      (ReferenceActivePhysicalStep.recordFollower prep.coordinator.downView
        f.follower f.row f.activation f.time f.active f.arm y s).down = none := by
    simpa only [prep, f, y] using hrecordDown
  have houtputConfig : (r.output.followers i).configuration = .ordinary next nextMemory :=
    houtputConfiguration
  have houtputOK : (r.output.followers i).failure = none := houtputFailure
  have hnextConfig : r.output.next.followers i = .ordinary next nextMemory := hnextOutput
  have hgateMap : G ↔ SnapshotRecordingKernel.recordingMap p
      (.live v.view.payload.assignment
        (ReferenceActiveDataOwnership.choiceSnapshot v states))
      true rate.eta.val rate.eta.property v.view.payload.eta_le_source_cap
      v.view.payload.anchor v.view.payload.anchor
      v.view.payload.anchor_pos v.view.payload.anchor_pos
      (fun _ => le_rfl) (fun j => by
        rw [two_mul]
        exact le_add_of_nonneg_right (le_of_lt (v.view.payload.anchor_pos j)))
      ((row.2 t).1) = some a := by
    exact ReferenceFollowerOccupiedRecorderEvent.occupiedGate_eq_canonicalRecordingMap
      v.view.payload (ReferenceActiveDataOwnership.choiceSnapshot v states) i row t s
      rfl hoccupiedStatus
  have hreleasedSource : next.status = .released ↔
      s.status = .released ∨
        (s.status = .pending ∧ ActiveFollowerLifecycle.releaseCondition rate.eta i
          (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) y M) := by
    simpa only [s, M, prep, row, t, y, hdownAgreement] using hreleased
  have hpendingSource : next.status = .pending ↔
      s.status = .pending ∧ ¬ ActiveFollowerLifecycle.releaseCondition rate.eta i
        (ActiveFollowerLifecycle.publicRowOfCompleteRow row t) y M := by
    simpa only [s, M, prep, row, t, y, hdownAgreement] using hpending
  exact ⟨serviced, next, nextMemory, hchecked, harrivalDelta, hserviceGamma,
    hserviceOutputDelta, hrecordOutput, hrecordNoDownInput, hrecordNoDown,
    hreleaseFinish, houtputConfig, houtputOK, hnextConfig, hscoreGamma,
    hdeltaGamma, hbacklogGamma, hqueue, hnextDown, hbufferNext,
    hreleasedSource, hpendingSource, hgateMap⟩

end Bandits.Support.ReferenceCompleteOccupiedFollowerDataArrival

end
