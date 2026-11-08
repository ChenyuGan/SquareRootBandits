/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveStaleDownExclusion

/-!
# First-live retained raw DOWN diagnostic exclusion

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-108`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,246-295`, and
`sources/zip4/manuscript/05_binary_transport.tex:74-88`.

This internal result traces an actually retained ordinary DOWN parse and
local-acceptance diagnostic back to the ordinary unoccupied choice that
produced it. It then excludes the exact selected payload record's stale raw
local-acceptance event at a later first-live choice. Reference filtering,
recovery, and successful finishing are not premises. This is not a
source-facing theorem or manuscript-closure claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceFollowerFixedReply
open ReferencePrelaunchFollower
open ReferenceFirstLiveConfirmationHistory
open ReferenceFirstLivePendingErasureHistory

namespace Bandits.Support.ReferenceFirstLiveRawDownExclusion

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem referenceDownCut_parse_acceptance_start
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hparse : (ReferenceDownReception.referenceDownCut p view i row t observation rate state).ordinaryParse = some M)
    (haccept : (ReferenceDownReception.referenceDownCut p view i row t observation rate state).ordinaryAcceptance) :
    ReferencePrelaunchFollower.acceptedStart state < M.val.sigma := by
  classical
  unfold ReferenceDownReception.referenceDownCut at hparse haccept
  split at hparse <;> rename_i hselected
  · simp only [dite_eq_left hselected] at haccept
    split at hparse <;> rename_i hstatus
    · simp only [dite_eq_left hstatus] at haccept
      split at hparse <;> rename_i hregisters
      · simp only [dite_eq_left hregisters] at haccept
        split at hparse <;> rename_i hbatch
        · simp only [dite_eq_left hbatch] at haccept
          split at hparse <;> rename_i hbuffer
          · simp only [dite_eq_left hbuffer] at haccept
            dsimp only at hparse haccept
            split at hparse <;> rename_i hmatches
            · simp only [dite_eq_left hmatches] at haccept
              dsimp only at hparse haccept
              rw [hparse] at haccept
              have htest : OrdinaryMessageCodec.acceptDown
                  (ReferencePrelaunchFollower.codecParams p rate.eta)
                  (ReferencePrelaunchFollower.acceptedStart state) (t.val + 1) M := by
                simpa only [ReferenceDownReception.ordinaryLocalAcceptanceTest] using haccept
              exact htest.1
            · simp only [dite_eq_right hmatches] at haccept
              dsimp only at hparse haccept
              rw [hparse] at haccept
              have htest : OrdinaryMessageCodec.acceptDown
                  (ReferencePrelaunchFollower.codecParams p rate.eta)
                  (ReferencePrelaunchFollower.acceptedStart state) (t.val + 1) M := by
                simpa only [ReferenceDownReception.ordinaryLocalAcceptanceTest] using haccept
              exact htest.1
          · change none = some M at hparse
            cases hparse
        · change none = some M at hparse
          cases hparse
      · change none = some M at hparse
        cases hparse
    · change none = some M at hparse
      cases hparse
  · change none = some M at hparse
    cases hparse

private theorem finishFollower_ordinary_diagnostic_frame
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary state memory) :
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).down =
        (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation state).down := by
  classical
  cases hrecord : (ReferenceActivePhysicalStep.recordFollower view prepared.follower
      prepared.row prepared.activation prepared.time prepared.active prepared.arm
      observation state).result with
  | error reason =>
      simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord]
  | ok post =>
      cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
          prepared.row prepared.time observation state memory post with
      | error reason =>
          simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord, hfinish]
      | ok result =>
          simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord, hfinish]

/-- A retained raw parse with the ordinary local DOWN acceptance test passing
comes from the actual ordinary unoccupied choice. Its logged state and cut
are identified from the record's literal step, even if reference filtering,
recovery, or a later finish rejects the operation. -/
theorem retained_raw_down_parse_acceptance_actual_choice
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdown : (r.output.followers i).down = some cut)
    (hparse : cut.ordinaryParse = some M)
    (haccept : cut.ordinaryAcceptance) :
    ∃ state memory,
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory ∧
      state.status = .unoccupied ∧
      ReferencePrelaunchFollower.acceptedStart state < M.val.sigma := by
  have hdownStep := hdown
  rw [r.output_eq] at hdownStep
  let prepared := ReferenceActivePhysicalStep.prepare r.input
  let observation := prepared.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let localPrepared := prepared.followers.followers i
  have hdiagDown :
      (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView
        localPrepared observation).down = some cut := by
    change ((ReferenceActivePhysicalStep.prepare r.input).observeFollower i).down = some cut at hdownStep
    simpa only [ReferenceActivePhysicalStep.PreparedRound.observeFollower,
      prepared, localPrepared, observation] using hdownStep
  cases hconfiguration : localPrepared.configuration with
  | dagger =>
      simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration] at hdiagDown
      cases hdiagDown
  | ordinary state memory =>
      have hchoice :
          (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary state memory := by
        change (r.output.preparation.followers.followers i).configuration = _
        rw [r.output_eq]
        change ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration = _
        exact hconfiguration
      have hframe := finishFollower_ordinary_diagnostic_frame
        prepared.coordinator.downView localPrepared observation state memory hconfiguration
      have hrecordDown :
          (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
            localPrepared.follower localPrepared.row localPrepared.activation localPrepared.time
            localPrepared.active localPrepared.arm observation state).down = some cut :=
        hframe.symm.trans hdiagDown
      by_cases hunoccupied : state.status = .unoccupied
      · cases hlogging : ActiveFollowerLogging.checkedLogging localPrepared.follower
            localPrepared.row localPrepared.activation localPrepared.time
            (localPrepared.arm, observation) state with
        | error reason =>
            simp only [ReferenceActivePhysicalStep.recordFollower, hunoccupied, hlogging]
              at hrecordDown
            cases hrecordDown
        | ok logged =>
            have hcutEq :
                ReferenceDownReception.referenceDownCut p prepared.coordinator.downView
                  localPrepared.follower localPrepared.row localPrepared.time observation rate logged = cut := by
              apply Option.some.inj
              simpa [ReferenceActivePhysicalStep.recordFollower, hunoccupied, hlogging]
                using hrecordDown
            have hparse' :
                (ReferenceDownReception.referenceDownCut p prepared.coordinator.downView
                  localPrepared.follower localPrepared.row localPrepared.time observation rate logged).ordinaryParse =
                    some M := by
              rw [hcutEq]
              exact hparse
            have haccept' :
                (ReferenceDownReception.referenceDownCut p prepared.coordinator.downView
                  localPrepared.follower localPrepared.row localPrepared.time observation rate logged).ordinaryAcceptance := by
              rw [hcutEq]
              exact haccept
            have hstrict := referenceDownCut_parse_acceptance_start
              prepared.coordinator.downView localPrepared.follower localPrepared.row
              localPrepared.time observation logged M hparse' haccept'
            have hloggingFrame := ActiveFollowerLogging.checkedLogging_success_frame
              localPrepared.follower localPrepared.row localPrepared.activation localPrepared.time
              (localPrepared.arm, observation) state logged hlogging
            have hstart : ReferencePrelaunchFollower.acceptedStart logged =
                ReferencePrelaunchFollower.acceptedStart state := by
              simp only [ReferencePrelaunchFollower.acceptedStart, hloggingFrame.1]
            rw [hstart] at hstrict
            exact ⟨state, memory, hchoice, hunoccupied, hstrict⟩
      · simp only [ReferenceActivePhysicalStep.recordFollower, hunoccupied] at hrecordDown
        cases hrecordDown

/-- The exact selected payload record's raw parse/local-acceptance diagnostic
cannot be stale at a later-or-same actual first-live round. The bound is
consumed from the original full physical run; no filtered `AcceptedDown`
outcome or successful current finish is required. -/
theorem run_firstLive_missing_pending_raw_down_diagnostic_excluded
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hseed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial) :
    let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ (a : Fin W.length) (v : ReferenceFirstLivePendingErasureHistory.Selection W[a.val].input),
      (ReferenceActivePhysicalStep.prepare W[a.val].input).coordinator.selection = some v →
      ∀ (i : Fin (p.m - 1)), i ∉ v.view.pendingAtChoice →
      ∀ (t : Fin R.records.length), a.val ≤ t.val →
      ∀ (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
        (R.records[t.val].output.followers i).down = some cut →
        cut.ordinaryParse = some (v.view.payload.downRecord i) →
        ¬ cut.ordinaryAcceptance := by
  intro R W a v hselected i hi t hat cut hdown hparse haccept
  obtain ⟨state, memory, hchoice, _hunoccupied, hstrict⟩ :=
    retained_raw_down_parse_acceptance_actual_choice R.records[t.val] i cut
      (v.view.payload.downRecord i) hdown hparse haccept
  have hbound := ReferenceFirstLiveStaleDownExclusion.run_firstLive_missing_pending_stale_down_start_bound
    initial rows J rewards start count hspan hmode hfirst hseed a v hselected i hi t hat
    state memory hchoice
  exact Nat.not_lt_of_ge hbound hstrict

end Bandits.Support.ReferenceFirstLiveRawDownExclusion

end
