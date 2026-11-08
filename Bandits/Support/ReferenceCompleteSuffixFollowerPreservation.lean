/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteFollowerPreparation
public import Bandits.Support.ReferenceCompleteAcceptedCurrentDownForward

import Lean.Elab.Tactic.Omega
import Bandits.Support.ReferenceFirstLaunchNumericalCell

/-!
# Ordinary follower preservation on the complete physical suffix

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:35-108,141-157`,
`sources/zip4/manuscript/05_binary_transport.tex:352-431`, and
`sources/zip4/manuscript/06_interruptions.tex:35-100,355-426`.

Starting from the actual corrected launch, every connected record in the
original complete-source suffix has an ordinary follower input.  PREPARE and
the three actual local-operation tails produce the corresponding ordinary
choice and output, including the checked local domains.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerDownAcceptance

namespace Bandits.Support.ReferenceCompleteSuffixFollowerPreservation

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem connected_first_input
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (h : 0 < records.length) : records[0].input.state = initial := by
  cases records with
  | nil => simp at h
  | cons record rest => exact hconnected.1

private theorem connected_successor_input
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (n : ℕ) (h : n + 1 < records.length) :
    records[n + 1].input.state = records[n].output.next := by
  induction records generalizing initial n with
  | nil => simp at h
  | cons record rest ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hconnected
      cases n with
      | zero =>
          cases rest with
          | nil => simp at h
          | cons next tail =>
              simpa only [List.getElem_cons_succ, List.getElem_cons_zero,
                ReferenceActivePhysicalHorizon.Connected] using hconnected.2.1
      | succ n =>
          have h' : n + 1 < rest.length := by simp at h; omega
          simpa only [List.getElem_cons_succ] using ih hconnected.2 n h'

private theorem complete_suffix_follower_forward
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val] i).configuration = .ordinary choice memory) :
    ∃ next nextMemory,
      ActiveFollowerLifecycle.localStateDomainValid next ∧
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].output.followers i).configuration =
          .ordinary next nextMemory ∧
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].output.followers i).failure = none ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].output.next.followers i =
          .ordinary next nextMemory := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let r := R[k.val]
  let t := r.input.time
  let row := r.input.row
  let own := r.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let view := r.output.preparation.coordinator.downView
  let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i row t own rate choice
  let expected := ReferenceDownReception.expectedDownFlatWord view i row t
  let parsed := ReferenceDownReception.ordinaryParse p rate decoded.2
  cases hstatus : choice.status with
  | unoccupied =>
      by_cases hpositive : ActiveFollowerDownAcceptance.downSelected p i row t ∧
          decoded.2 = expected ∧
          ReferenceDownReception.ordinaryLocalAcceptanceTest p rate t choice parsed
      · have haccepted :=
          ReferenceCompleteAcceptedCurrentDownForward.complete_ordinary_unoccupied_accepted_current_down_forward
            (rate := rate) rewards C_star C_h source k i choice memory hchoice hstatus hpositive
        rcases haccepted with
          ⟨selected, _hselection, _hview, _hbranch, _hraw, _hparsed, ha, _b, _beta,
            _hb, _hbirth, _hbase, _hcredit, final, htail⟩
        let P := selected.view.payload
        let M := P.downRecord i
        let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
          (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t choice ha) row
        let ell := scan.endpoint
        let installed : ReferencePrelaunchFollower.State p rate.eta := {
          choice with
          lastDown := some M
          S := final.registers.1
          delta := final.lastService
          backlog := final.registers.2
          downBatch := decoded.1
          buffer := []
          status := if ell = t.val + 2 then .pending else .unoccupied }
        let nextMemory : ActiveFollowerLifecycle.LocalMemory p := if ell = t.val + 2 then
          { lastProposalRead := some {
            timestamp := t
            bit := FollowerCutoffScan.completeRowProposalBit p rate.eta.val row t } }
          else memory
        let cut := ReferenceDownReception.referenceDownCut p view i row t own rate choice
        rcases htail with
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
            hnextDomain, _, _, _, _, _, _, houtput, hnext⟩
        have houtputConfig : (r.output.followers i).configuration = .ordinary installed nextMemory := by
          exact congrArg
            (fun x : ReferenceActivePhysicalStep.FollowerObservation p rate => x.configuration)
            houtput
        have houtputFailure : (r.output.followers i).failure = none := by
          exact congrArg
            (fun x : ReferenceActivePhysicalStep.FollowerObservation p rate => x.failure)
            houtput
        exact ⟨installed, nextMemory, hnextDomain, houtputConfig, houtputFailure, hnext⟩
      · have hnonaccepting :=
          ReferenceCompleteUnoccupiedNonacceptingForward.complete_ordinary_unoccupied_nonaccepting_forward
            (rate := rate) rewards C_star C_h source k i choice memory hchoice hstatus hpositive
        rcases hnonaccepting with ⟨logged, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        let cut := ReferenceDownReception.referenceDownCut p view i row t own rate logged
        let next := @ite _ (ActiveFollowerDownAcceptance.downSelected p i row t)
          (Classical.propDecidable _) {logged with downBatch := decoded.1} logged
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨hnextDomain, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨_, houter⟩
        rcases houter with ⟨houtput, hnext⟩
        have houtputConfig : (r.output.followers i).configuration = .ordinary next memory := by
          have h := congrArg
            (fun x : ReferenceActivePhysicalStep.FollowerObservation p rate => x.configuration)
            houtput
          exact h
        have houtputFailure : (r.output.followers i).failure = none := by
          have h := congrArg
            (fun x : ReferenceActivePhysicalStep.FollowerObservation p rate => x.failure)
            houtput
          exact h
        exact ⟨next, memory, hnextDomain, houtputConfig, houtputFailure, hnext⟩
  | pending | released =>
      have hoccupied : choice.status ≠ .unoccupied := by simp [hstatus]
      have hservice :=
        ReferenceCompleteOccupiedServiceForward.complete_ordinary_occupied_service_forward
          (rate := rate) rewards C_star C_h source k i choice memory hchoice hoccupied
      rcases hservice with ⟨_, hbefore⟩
      rcases hbefore with ⟨_, _, _, hmassData⟩
      rcases hmassData with ⟨b, j, payload, beta, hmassFacts⟩
      rcases hmassFacts with ⟨_, _, _, _, _, _, _, _, _, hpreparedFacts⟩
      rcases hpreparedFacts with ⟨_, _, _, _, hservices⟩
      obtain ⟨serviced, next, nextMemory, hbody⟩ := hservices
      rcases hbody with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnextDomain,
          _, _, _, _, _, _, _, _, houtputConfig, houtputFailure, _, _, hnext⟩
      exact ⟨next, nextMemory, hnextDomain, houtputConfig, houtputFailure, hnext⟩

/-- Every actual record on the complete suffix starts with the source's
ordinary follower state and advances through the real PREPARE choice and
checked ordinary follower output.  The quantifiers are rooted only in the
whole source, whole reward table, and shared constants. -/
theorem complete_suffix_follower_preservation
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin R.length) (i : Fin (p.m - 1)),
      ∃ inputState inputMemory choice next nextMemory,
        R[k.val].input.state.followers i = .ordinary inputState inputMemory ∧
        ActiveFollowerLifecycle.localStateDomainValid inputState ∧
        ActiveFollowerLifecycle.startRound rate.eta R[k.val].input.time
          inputState inputMemory = .ok (choice, inputMemory) ∧
        (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration =
          .ordinary choice inputMemory ∧
        ActiveFollowerLifecycle.localStateDomainValid choice ∧
        ActiveFollowerDownAcceptance.operationInputDomain p rate choice ∧
        ActiveFollowerLifecycle.localStateDomainValid next ∧
        (R[k.val].output.followers i).configuration = .ordinary next nextMemory ∧
        (R[k.val].output.followers i).failure = none ∧
        R[k.val].output.next.followers i = .ordinary next nextMemory := by
  classical
  dsimp only
  intro k i
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
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
      let initial := ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hlaunchInitial : active = initial := by
        exact Option.some.inj (hlaunch.symm.trans
          (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
            rate source rewards C_star C_h hc))
      have hconnected := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
        rate source rewards C_star C_h active hlaunch
      have hconnectedR : ReferenceActivePhysicalHorizon.Connected active R
          (ReferenceActivePhysicalHorizon.run active source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            (by
              have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
                rate source rewards C_star C_h
              omega)
            (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
              rate source rewards C_star C_h active hlaunch)).finalState := by
        simpa only [R] using hconnected
      have hall : ∀ (n : ℕ) (hn : n < R.length) (i : Fin (p.m - 1)),
          ∃ inputState inputMemory choice next nextMemory,
            R[n].input.state.followers i = .ordinary inputState inputMemory ∧
            ActiveFollowerLifecycle.localStateDomainValid inputState ∧
            ActiveFollowerLifecycle.startRound rate.eta R[n].input.time
              inputState inputMemory = .ok (choice, inputMemory) ∧
            (ReferenceFollowerFixedReply.actualChoice R[n] i).configuration =
              .ordinary choice inputMemory ∧
            ActiveFollowerLifecycle.localStateDomainValid choice ∧
            ActiveFollowerDownAcceptance.operationInputDomain p rate choice ∧
            ActiveFollowerLifecycle.localStateDomainValid next ∧
            (R[n].output.followers i).configuration = .ordinary next nextMemory ∧
            (R[n].output.followers i).failure = none ∧
            R[n].output.next.followers i = .ordinary next nextMemory := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
            intro hn i
            by_cases hz : n = 0
            · subst n
              have hfirst := connected_first_input hconnectedR (by omega)
              have hinput : R[0].input.state.followers i =
                  .ordinary (seed.followers i) (seed.memory i) := by
                calc
                  _ = (active).followers i := congrArg (fun s => s.followers i) hfirst
                  _ = (initial).followers i := congrArg (fun s => s.followers i) hlaunchInitial
                  _ = .ordinary (seed.followers i) (seed.memory i) := seed.configuration i
              obtain ⟨choice, hinputDomain, hstart, hchoice, hchoiceDomain, hoperationDomain⟩ :=
                ReferenceCompleteFollowerPreparation.complete_ordinary_input_prepare
                  (rate := rate) rewards C_star C_h source ⟨0, hn⟩ i
                  (seed.followers i) (seed.memory i) hinput
              obtain ⟨next, nextMemory, hnextDomain, houtputConfig, houtputFailure, hnext⟩ :=
                complete_suffix_follower_forward (rate := rate) rewards C_star C_h source
                  ⟨0, hn⟩ i choice (seed.memory i) hchoice
              exact ⟨seed.followers i, seed.memory i, choice, next, nextMemory,
                hinput, hinputDomain, hstart, hchoice, hchoiceDomain, hoperationDomain,
                hnextDomain, houtputConfig, houtputFailure, hnext⟩
            · have hpos : 0 < n := by omega
              let previous := n - 1
              have hprevious : previous < n := by dsimp [previous]; omega
              have hpreviousBound : previous < R.length := Nat.lt_trans hprevious hn
              obtain ⟨_, previousMemory, _, previousNext, previousNextMemory,
                hpreviousInput, _, _, _, _, _, hpreviousNextDomain,
                hpreviousOutputConfig, hpreviousOutputFailure, hpreviousNextEq⟩ :=
                ih previous hprevious hpreviousBound i
              have hnEq : n = previous + 1 := by dsimp [previous]; omega
              have hsuccessor := connected_successor_input hconnectedR previous (by
                rw [← hnEq]
                exact hn)
              have hpreviousNextInput :
                  R[previous + 1].input.state.followers i =
                    .ordinary previousNext previousNextMemory := by
                calc
                  _ = R[previous].output.next.followers i :=
                    congrArg (fun s => s.followers i) hsuccessor
                  _ = .ordinary previousNext previousNextMemory := hpreviousNextEq
              have hinput : R[n].input.state.followers i =
                  .ordinary previousNext previousNextMemory := by
                simpa only [hnEq] using hpreviousNextInput
              obtain ⟨choice, hinputDomain, hstart, hchoice, hchoiceDomain, hoperationDomain⟩ :=
                ReferenceCompleteFollowerPreparation.complete_ordinary_input_prepare
                  (rate := rate) rewards C_star C_h source ⟨n, hn⟩ i
                  previousNext previousNextMemory hinput
              obtain ⟨next, nextMemory, hnextDomain, houtputConfig, houtputFailure, hnext⟩ :=
                complete_suffix_follower_forward (rate := rate) rewards C_star C_h source
                  ⟨n, hn⟩ i choice previousNextMemory hchoice
              exact ⟨previousNext, previousNextMemory, choice, next, nextMemory,
                hinput, hinputDomain, hstart, hchoice, hchoiceDomain, hoperationDomain,
                hnextDomain, houtputConfig, houtputFailure, hnext⟩
      rcases hall k.val k.isLt i with
        ⟨inputState, inputMemory, choice, next, nextMemory,
          hinput, hinputDomain, hstart, hchoice, hchoiceDomain, hoperationDomain,
          hnextDomain, houtputConfig, houtputFailure, hnext⟩
      exact ⟨inputState, inputMemory, choice, next, nextMemory,
        hinput, hinputDomain, hstart, hchoice, hchoiceDomain, hoperationDomain,
        hnextDomain, houtputConfig, houtputFailure, hnext⟩

/-- The ordinary state and local domains at every actual complete-suffix
input. -/
theorem complete_suffix_follower_input
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin R.length) (i : Fin (p.m - 1)),
      ∃ state memory, R[k.val].input.state.followers i = .ordinary state memory ∧
        ActiveFollowerLifecycle.localStateDomainValid state := by
  intro R k i
  rcases complete_suffix_follower_preservation (rate := rate) rewards C_star C_h source k i with
    ⟨state, memory, _, _, _, hinput, hdomain, _, _, _, _, _, _, _, _⟩
  exact ⟨state, memory, hinput, hdomain⟩

/-- The actual PREPARE choice and checked operation domains at every actual
complete-suffix record. -/
theorem complete_suffix_follower_choice
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin R.length) (i : Fin (p.m - 1)),
      ∃ state memory choice,
        R[k.val].input.state.followers i = .ordinary state memory ∧
        ActiveFollowerLifecycle.localStateDomainValid state ∧
        ActiveFollowerLifecycle.startRound rate.eta R[k.val].input.time state memory =
          .ok (choice, memory) ∧
        (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration =
          .ordinary choice memory ∧
        ActiveFollowerLifecycle.localStateDomainValid choice ∧
        ActiveFollowerDownAcceptance.operationInputDomain p rate choice := by
  intro R k i
  rcases complete_suffix_follower_preservation (rate := rate) rewards C_star C_h source k i with
    ⟨state, memory, choice, _, _, hinput, hinputDomain, hstart, hchoice,
      hchoiceDomain, hoperationDomain, _, _, _, _⟩
  exact ⟨state, memory, choice, hinput, hinputDomain, hstart, hchoice,
    hchoiceDomain, hoperationDomain⟩

/-- The ordinary output and next state are the actual follower projections of
each complete-suffix record, with checked failure absent. -/
theorem complete_suffix_follower_output
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin R.length) (i : Fin (p.m - 1)),
      ∃ state memory choice next nextMemory,
        R[k.val].input.state.followers i = .ordinary state memory ∧
        (ReferenceFollowerFixedReply.actualChoice R[k.val] i).configuration =
          .ordinary choice memory ∧
        ActiveFollowerLifecycle.localStateDomainValid choice ∧
        ActiveFollowerLifecycle.localStateDomainValid next ∧
        (R[k.val].output.followers i).configuration = .ordinary next nextMemory ∧
        (R[k.val].output.followers i).failure = none ∧
        R[k.val].output.next.followers i = .ordinary next nextMemory := by
  dsimp only
  intro k i
  rcases complete_suffix_follower_preservation (rate := rate) rewards C_star C_h source k i with
    ⟨state, memory, choice, next, nextMemory, hinput, _, _, hchoice,
      hchoiceDomain, _, hnextDomain, houtputConfig, houtputFailure, hnext⟩
  exact ⟨state, memory, choice, next, nextMemory, hinput, hchoice, hchoiceDomain, hnextDomain,
    houtputConfig, houtputFailure, hnext⟩

end Bandits.Support.ReferenceCompleteSuffixFollowerPreservation

end
