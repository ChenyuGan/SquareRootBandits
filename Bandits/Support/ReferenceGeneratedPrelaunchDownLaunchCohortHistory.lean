/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownCohortInterval

import Lean.Elab.Tactic.Omega

/-!
# Actual prelaunch DOWN cohort at the corrected launch boundary

This module joins the actual corrected launch output to the same generated
prelaunch DOWN cohort whose birth and intervening history are recorded by the
accepted interval producer.  The launch seed, ordinary follower, pending
batch, failure bits, test census, and candidate flags all come from the same
original source.

Sources: `appendix_a_local_protocol.tex:111-153`,
`appendix_b_communication.tex:724-736`, `07_public_setup.tex:60-112,127-164`,
and `05_binary_transport.tex:20-42`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownLaunchCohortHistory

open ConstructorDimensions BootstrapDimensions
open ReferenceInitializationRun ReferencePrelaunchFollower
open ReferenceGeneratedPrelaunchDownPrefix ReferenceGeneratedPrelaunchDownCohort
open ReferenceGeneratedPrelaunchDownHistoricalBirth
open ReferenceGeneratedPrelaunchDownCohortInterval
open ReferenceGeneratedDownBatchCalendar ReferenceCorrectedInitializationLaunch
open ReferenceActivePhysicalHorizon ReferenceFollowerDecoderChronology
open AffineBatchDecoder
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

private theorem run_eq_at_own_completed
    (x : ReferenceInitializationRun.Input p) :
    ∀ r, r ≤ n_boot p →
      (ReferenceInitializationRun.run x r).crossing.isSome = true →
      ReferenceInitializationRun.run x
        (ReferenceInitializationRun.run x r).completed =
        ReferenceInitializationRun.run x r := by
  intro r
  induction r with
  | zero =>
      intro _ hc
      simp only [ReferenceInitializationRun.run_zero,
        ReferenceInitializationRun.initial, Option.isSome_none,
        Bool.false_eq_true] at hc
  | succ r ih =>
      intro hr hc
      by_cases hcross : (ReferenceInitializationRun.run x r).crossing.isSome = true
      · rw [ReferenceInitializationRun.run_succ,
          ReferenceInitializationRun.advance_of_crossing x _ hcross] at hc ⊢
        exact ih (by omega) hcross
      · have hnone : (ReferenceInitializationRun.run x r).crossing = none := by
          cases h : (ReferenceInitializationRun.run x r).crossing <;> simp_all
        have hcompleted :=
          (ReferenceInitializationRun.run_progress x r (by omega)).resolve_left hcross
        have hremain : (ReferenceInitializationRun.run x r).completed < n_boot p := by
          omega
        let b := ReferenceInitializationRun.run x r
        have hstep : ReferenceInitializationRun.run x (r + 1) =
            ReferenceInitializationRun.finishBlock x b hremain := by
          rw [ReferenceInitializationRun.run_succ,
            ReferenceInitializationRun.advance_of_no_crossing x b hnone hremain]
        have hcompleted' :
            (ReferenceInitializationRun.finishBlock x b hremain).completed = r + 1 := by
          simp [ReferenceInitializationRun.finishBlock, b, hcompleted]
        rw [hstep] at hc ⊢
        change ReferenceInitializationRun.run x
          (ReferenceInitializationRun.finishBlock x b hremain).completed =
            ReferenceInitializationRun.finishBlock x b hremain
        rw [hcompleted']
        exact hstep

private theorem actual_stopped_endpoint_before_T
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1))
    (hCross : (ReferenceInitializationRun.output
      (sourceReferenceInput rate rewards C_star C_h z)).crossing.isSome = true)
    (hStop : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (sourceReferenceInput rate rewards C_star C_h z)).completed < p.T)
    (a : Activation p)
    (ha : (ReferenceInitializationRun.output
      (sourceReferenceInput rate rewards C_star C_h z)).activation
        (ActualReferenceInitializationBlock.refFollower i) = some a) :
    sourcePrelaunchDownActualCohort rate rewards C_star C_h z i
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z)).completed)
      (Nat.le_of_lt hStop) =
        some (a, ReferenceInitializationRun.ordinary
          (sourceReferenceInput rate rewards C_star C_h z)
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z))
          (ActualReferenceInitializationBlock.refFollower i)) ∧
      sourcePrelaunchDownTestsAt rate rewards C_star C_h z i
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z)).completed)
        (Nat.le_of_lt hStop) =
          ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
            rate rewards C_star C_h z i := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  let b := ReferenceInitializationRun.output x
  let s := ReferenceInitializationRun.elapsed p b.completed
  let f := ActualReferenceInitializationBlock.refFollower i
  let r : Fin p.T := ⟨s, hStop⟩
  have hStopMin : min p.T (b.completed * B_boot p) < p.T := by
    change min p.T (b.completed * B_boot p) < p.T at hStop
    exact hStop
  have hProduct : s = b.completed * B_boot p := by
    dsimp [s, ReferenceInitializationRun.elapsed]
    have hlt : b.completed * B_boot p < p.T := by
      by_contra hn
      have hle : p.T ≤ b.completed * B_boot p := Nat.le_of_not_gt hn
      rw [Nat.min_eq_left hle] at hStopMin
      omega
    rw [Nat.min_eq_right hlt.le]
  have hIndex : (roundBlockIndex p r).val = b.completed := by
    change s / B_boot p = b.completed
    rw [hProduct]
    rw [Nat.mul_comm]
    exact Nat.mul_div_right _ (B_boot_pos p)
  have hCrossRun :
      (ReferenceInitializationRun.run x (n_boot p)).crossing.isSome = true := by
    simpa [x, sourceReferenceInput, ReferenceInitializationRun.output,
      ActualReferenceInitializationBlock.referenceInput] using hCross
  have hRun : ReferenceInitializationRun.run x
      (roundBlockIndex p r).val = b := by
    rw [hIndex]
    exact run_eq_at_own_completed x (n_boot p) (Nat.le_refl _) hCrossRun
  have hPrefixCross :
      (ReferenceInitializationRun.run x (roundBlockIndex p r).val).crossing.isSome = true := by
    rw [hRun]
    exact hCross
  cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          have hnone :
              (ReferenceInitializationRun.run x (roundBlockIndex p r).val).crossing = none :=
            by
              have hnone' := active.val.1.property.2.1
              rw [active.val.1.property.2.2] at hnone'
              exact hnone'
          simp [hnone] at hPrefixCross
      | inr inactive =>
          have hnone :
              (ReferenceInitializationRun.run x (roundBlockIndex p r).val).crossing = none :=
            by
              have hnone' := inactive.val.1.property.2.1
              rw [inactive.val.1.property.2.2] at hnone'
              exact hnone'
          simp [hnone] at hPrefixCross
  | inr stopped =>
      have hStoppedBoundary : stopped.val.1 = b := by
        calc
          stopped.val.1 = ReferenceInitializationRun.run x
              (roundBlockIndex p r).val := stopped.property.2.1
          _ = b := hRun
      have hStoppedState : stopped.val.2 =
          ReferenceInitializationRun.ordinary x b f := by
        simpa [hStoppedBoundary] using stopped.property.2.2
      constructor
      ·
        have hp' : source_prelaunch_down_prefix rate rewards C_star C_h z i
            ⟨s, hStop⟩ = .inr stopped := by
          simpa [r] using hp
        rw [sourcePrelaunchDownActualCohort_of_stopped rate rewards C_star C_h z i
          s (Nat.le_of_lt hStop) hStop stopped hp']
        have ha' : b.activation f = some a := by
          simpa [b, f] using ha
        rw [hStoppedBoundary, hStoppedState, ha']
        rfl
      · rw [sourcePrelaunchDownTestsAt_prefix rate rewards C_star C_h z i
          s (Nat.le_of_lt hStop) hStop]
        have hp' : source_prelaunch_down_prefix rate rewards C_star C_h z i
            ⟨s, hStop⟩ = .inr stopped := by
          simpa [r] using hp
        rw [source_prelaunch_down_prefix_tests, hp']
        change ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests
          x stopped.val.1 i = ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests
            x b i
        rw [hStoppedBoundary]

private theorem source_boundary_eq_actual_birth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (a : Activation p) (beta : ℕ)
    (hActivation : (ReferenceInitializationRun.output
      (sourceReferenceInput rate rewards C_star C_h z)).activation
        (ActualReferenceInitializationBlock.refFollower i) = some a)
    (hBirth : bankBirth a
      (ReferenceInitializationRun.ordinary
        (sourceReferenceInput rate rewards C_star C_h z)
        (ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z))
        (ActualReferenceInitializationBlock.refFollower i)).downBatch = some beta) :
    sourcePrelaunchDownCohortBoundary rate rewards C_star C_h z i
      ((ReferenceInitializationRun.ordinary
        (sourceReferenceInput rate rewards C_star C_h z)
        (ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z))
        (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length) =
      some beta := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  let b := ReferenceInitializationRun.output x
  let f := ActualReferenceInitializationBlock.refFollower i
  let state := ReferenceInitializationRun.ordinary x b f
  let bank := state.downBatch
  let k := bank.completed.length
  by_cases hk : k = 0
  · have hEmpty : bank.completed = [] := by
      cases h : bank.completed with
      | nil => rfl
      | cons head tail => simp [h, k] at hk
    have hBirth' : bankBirth a bank = some beta := by
      simpa [x, b, state, bank] using hBirth
    have hBeta : a.val - 1 = beta := by
      simpa [bankBirth, hEmpty] using hBirth'
    have hInitial :=
      (ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_initial_boundary
        rate rewards C_star C_h z i).1
    have hInitial' :
        sourcePrelaunchDownCohortBoundary rate rewards C_star C_h z i 0 =
          (b.activation f).map (fun a => a.val - 1) := by
      simpa [x, b, f, sourceReferenceInput,
        ActualReferenceInitializationBlock.referenceInput] using hInitial
    change sourcePrelaunchDownCohortBoundary rate rewards C_star C_h z i k = some beta
    rw [hk, hInitial', hActivation]
    simp [hBeta]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hIndex : k - 1 < bank.completed.length := by omega
    obtain ⟨t, _, hLast, hReset⟩ :=
      ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_reset_boundary
        rate rewards C_star C_h z i (k - 1) hIndex
    have hLastBatch : bank.completed.getLast? = some (bank.completed[k - 1]) := by
      simp [k, List.getLast?_eq_getElem?]
    have hLast' : bank.completed[k - 1].getLast? =
        some ⟨t, (x.row.2 t).2 (0, i)⟩ := by
      simpa [x, b, state, bank, k, sourceReferenceInput,
        ActualReferenceInitializationBlock.referenceInput] using hLast
    have hNonempty : bank.completed ≠ [] := by
      intro hnil
      have hlen : bank.completed.length = 0 := by
        simpa using congrArg List.length hnil
      omega
    have hBirthLast : bankBirth a bank = some (t.val + 1) := by
      simp [bankBirth, List.isEmpty_eq_false_iff.mpr hNonempty,
        hLastBatch, hLast']
    have hBeta : beta = t.val + 1 :=
      Option.some.inj (hBirth.symm.trans hBirthLast)
    change sourcePrelaunchDownCohortBoundary rate rewards C_star C_h z i k = some beta
    have hReset' :
        sourcePrelaunchDownCohortBoundary rate rewards C_star C_h z i k =
          some (t.val + 1) := by
      simpa [Nat.sub_add_cancel hkpos] using hReset
    rw [hBeta]
    exact hReset'

private theorem actual_endpoint_historical_birth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (n : ℕ) (hn : n ≤ p.T)
    (a : Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hActual : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i n hn =
      some (a, state))
    (hState : state = ReferenceInitializationRun.ordinary
      (sourceReferenceInput rate rewards C_star C_h z)
      (ReferenceInitializationRun.output
        (sourceReferenceInput rate rewards C_star C_h z))
      (ActualReferenceInitializationBlock.refFollower i))
    (hActivation : (ReferenceInitializationRun.output
      (sourceReferenceInput rate rewards C_star C_h z)).activation
        (ActualReferenceInitializationBlock.refFollower i) = some a) :
    ∃ beta, ∃ hBeta : beta ≤ p.T, beta ≤ n ∧
      bankBirth a state.downBatch = some beta ∧
      birthAt rate rewards C_star C_h z i beta hBeta state.downBatch.completed.length ∧
      (∀ beta', bankBirth a state.downBatch = some beta' → beta' = beta) ∧
      sourcePrelaunchDownCohortBoundary rate rewards C_star C_h z i
        state.downBatch.completed.length = some beta ∧
      (let k := state.downBatch.completed.length
       let Old := (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i n hn).drop
         (AffineBatchDecoder.quota p * k)
       Old.map ReferenceGeneratedPrelaunchDownCohort.testEntry = state.downBatch.pending ∧
       Old.length < AffineBatchDecoder.quota p ∧
       (∀ test ∈ Old, beta ≤ test.time.val ∧ test.time.val < n) ∧
       (∀ u, beta ≤ u → ∀ hu : u ≤ n,
         ∃ stateU,
           sourcePrelaunchDownActualCohort rate rewards C_star C_h z i u (hu.trans hn) =
             some (a, stateU) ∧
           stateU.downBatch.completed = state.downBatch.completed ∧
           bankBirth a stateU.downBatch = some beta ∧
           stateU.downBatch.pending =
             (Old.filter (fun test => test.time.val < u)).map
               ReferenceGeneratedPrelaunchDownCohort.testEntry ∧
           ∀ w,
             (if hU : u < p.T then
                source_prelaunch_down_current_cohort_flags rate rewards C_star C_h z i
                  ⟨u, hU⟩ w
              else
                ((sourcePrelaunchDownTests rate rewards C_star C_h z i).map
                  (sourcePrelaunchDownCandidateFlag w)).drop
                    (AffineBatchDecoder.quota p * k)) =
             (Old.filter (fun test => test.time.val < u)).map
               (sourcePrelaunchDownCandidateFlag w))) := by
  classical
  obtain ⟨beta, hBeta, hBetaN, hBirth, hAtBirth, hUnique, hHistory⟩ :=
    ReferenceGeneratedPrelaunchDownCohortInterval.source_prelaunch_down_same_birth_cohort_interval
      rate rewards C_star C_h z i n hn a state hActual
  have hBoundary := source_boundary_eq_actual_birth rate rewards C_star C_h z i a beta
    hActivation (by simpa [hState] using hBirth)
  refine ⟨beta, hBeta, hBetaN, hBirth, hAtBirth, hUnique, ?_, hHistory⟩
  simpa [hState] using hBoundary

private theorem source_launch_down_before_T
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1))
    (hCross : (ReferenceInitializationRun.output
      (sourceReferenceInput rate rewards C_star C_h z)).crossing.isSome = true)
    (hStop : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (sourceReferenceInput rate rewards C_star C_h z)).completed < p.T) :
    ∃ launchSource : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z)).completed) hStop,
      launchSource.val = z ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
        some (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h
          (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z)).completed) hStop launchSource) ∧
      (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z)).completed) hStop launchSource).followers i =
        .ordinary (ReferenceInitializationRun.ordinary
          (sourceReferenceInput rate rewards C_star C_h z)
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z))
          (ActualReferenceInitializationBlock.refFollower i))
          (ActiveFollowerLifecycle.initialMemory p) ∧
      ReferenceFollowerDecoderChronology.downBatchSeed
        (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h
          (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z)).completed) hStop launchSource)
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z)).completed) ∧
      ReferenceInitializationRun.initializationFailure
        (sourceReferenceInput rate rewards C_star C_h z)
        (ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z))
        (ActualReferenceInitializationBlock.refFollower i) =
        ((ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z)).forcedFailure
            (ActualReferenceInitializationBlock.refFollower i) ||
          (ReferenceInitializationRun.ordinary
            (sourceReferenceInput rate rewards C_star C_h z)
            (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z))
            (ActualReferenceInitializationBlock.refFollower i)).initializationFailure) ∧
      (∀ a', (ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z)).activation
            (ActualReferenceInitializationBlock.refFollower i) = some a' →
        a'.val = ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z)).completed + 1 →
        (ReferenceInitializationRun.ordinary
          (sourceReferenceInput rate rewards C_star C_h z)
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z))
          (ActualReferenceInitializationBlock.refFollower i)).downBatch.pending = [] ∧
        (ReferenceInitializationRun.ordinary
          (sourceReferenceInput rate rewards C_star C_h z)
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z))
          (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length = 0 ∧
        bankBirth a'
          (ReferenceInitializationRun.ordinary
            (sourceReferenceInput rate rewards C_star C_h z)
            (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z))
            (ActualReferenceInitializationBlock.refFollower i)).downBatch =
          some (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z)).completed)) ∧
      (ReferenceInitializationRun.ordinary
        (sourceReferenceInput rate rewards C_star C_h z)
        (ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z))
        (ActualReferenceInitializationBlock.refFollower i)).downBatch.pending.length <
          AffineBatchDecoder.quota p ∧
      (ReferenceInitializationRun.ordinary
        (sourceReferenceInput rate rewards C_star C_h z)
        (ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z))
        (ActualReferenceInitializationBlock.refFollower i)).downBatch.pending =
        ((ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
          rate rewards C_star C_h z i).map
            ReferenceGeneratedPrelaunchDownCohort.testEntry).drop
          (AffineBatchDecoder.quota p *
            (ReferenceInitializationRun.ordinary
              (sourceReferenceInput rate rewards C_star C_h z)
              (ReferenceInitializationRun.output
                (sourceReferenceInput rate rewards C_star C_h z))
              (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length) ∧
      ∃ a, (ReferenceInitializationRun.output
        (sourceReferenceInput rate rewards C_star C_h z)).activation
          (ActualReferenceInitializationBlock.refFollower i) = some a ∧
        ((ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z)).forcedFailure
              (ActualReferenceInitializationBlock.refFollower i) = true ∧
            ReferenceInitializationRun.ordinary
              (sourceReferenceInput rate rewards C_star C_h z)
              (ReferenceInitializationRun.output
                (sourceReferenceInput rate rewards C_star C_h z))
              (ActualReferenceInitializationBlock.refFollower i) =
                ReferencePrelaunchFollower.initial p rate.eta ∧
            a.val = ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (sourceReferenceInput rate rewards C_star C_h z)).completed + 1 ∨
         (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z)).forcedFailure
              (ActualReferenceInitializationBlock.refFollower i) = false ∧
            ReferenceInitializationRun.ordinary
              (sourceReferenceInput rate rewards C_star C_h z)
              (ReferenceInitializationRun.output
                (sourceReferenceInput rate rewards C_star C_h z))
              (ActualReferenceInitializationBlock.refFollower i) =
                ReferencePrelaunchFollower.replay rate.eta i
                  (sourceReferenceInput rate rewards C_star C_h z).row a
                  ((ReferenceInitializationRun.output
                    (sourceReferenceInput rate rewards C_star C_h z)).history
                    (PublicDiscreteDraws.followerPlayer p.two_le_m
                      (ActualReferenceInitializationBlock.refFollower i)))
                  (ReferenceInitializationRun.elapsed_le_T p
                    (ReferenceInitializationRun.output
                      (sourceReferenceInput rate rewards C_star C_h z)).completed)) ∧
        sourcePrelaunchDownActualCohort rate rewards C_star C_h z i
          (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z)).completed)
          (Nat.le_of_lt hStop) =
            some (a, ReferenceInitializationRun.ordinary
              (sourceReferenceInput rate rewards C_star C_h z)
              (ReferenceInitializationRun.output
                (sourceReferenceInput rate rewards C_star C_h z))
              (ActualReferenceInitializationBlock.refFollower i)) ∧
        sourcePrelaunchDownTestsAt rate rewards C_star C_h z i
          (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z)).completed)
          (Nat.le_of_lt hStop) =
            ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
              rate rewards C_star C_h z i ∧
        ∃ beta, ∃ hBeta : beta ≤ p.T,
          beta ≤ ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z)).completed ∧
          bankBirth a
            (ReferenceInitializationRun.ordinary
              (sourceReferenceInput rate rewards C_star C_h z)
              (ReferenceInitializationRun.output
                (sourceReferenceInput rate rewards C_star C_h z))
              (ActualReferenceInitializationBlock.refFollower i)).downBatch = some beta ∧
          birthAt rate rewards C_star C_h z i beta hBeta
            (ReferenceInitializationRun.ordinary
              (sourceReferenceInput rate rewards C_star C_h z)
              (ReferenceInitializationRun.output
                (sourceReferenceInput rate rewards C_star C_h z))
              (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length ∧
          (∀ beta', bankBirth a
              (ReferenceInitializationRun.ordinary
                (sourceReferenceInput rate rewards C_star C_h z)
                (ReferenceInitializationRun.output
                  (sourceReferenceInput rate rewards C_star C_h z))
                (ActualReferenceInitializationBlock.refFollower i)).downBatch = some beta' →
              beta' = beta) ∧
          sourcePrelaunchDownCohortBoundary rate rewards C_star C_h z i
            (ReferenceInitializationRun.ordinary
              (sourceReferenceInput rate rewards C_star C_h z)
              (ReferenceInitializationRun.output
                (sourceReferenceInput rate rewards C_star C_h z))
              (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length =
              some beta ∧
          (let k := (ReferenceInitializationRun.ordinary
                (sourceReferenceInput rate rewards C_star C_h z)
                (ReferenceInitializationRun.output
                  (sourceReferenceInput rate rewards C_star C_h z))
                (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length
           let Old := (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i
                (ReferenceInitializationRun.elapsed p
                  (ReferenceInitializationRun.output
                    (sourceReferenceInput rate rewards C_star C_h z)).completed)
                (Nat.le_of_lt hStop)).drop (AffineBatchDecoder.quota p * k)
           Old.map ReferenceGeneratedPrelaunchDownCohort.testEntry =
                (ReferenceInitializationRun.ordinary
                  (sourceReferenceInput rate rewards C_star C_h z)
                  (ReferenceInitializationRun.output
                    (sourceReferenceInput rate rewards C_star C_h z))
                  (ActualReferenceInitializationBlock.refFollower i)).downBatch.pending ∧
           Old.length < AffineBatchDecoder.quota p ∧
           (∀ test ∈ Old, beta ≤ test.time.val ∧
             test.time.val < ReferenceInitializationRun.elapsed p
                (ReferenceInitializationRun.output
                  (sourceReferenceInput rate rewards C_star C_h z)).completed) ∧
           (∀ u, beta ≤ u → ∀ hu : u ≤ ReferenceInitializationRun.elapsed p
                (ReferenceInitializationRun.output
                  (sourceReferenceInput rate rewards C_star C_h z)).completed,
             ∃ stateU,
               sourcePrelaunchDownActualCohort rate rewards C_star C_h z i u
                 (hu.trans (Nat.le_of_lt hStop)) = some (a, stateU) ∧
               stateU.downBatch.completed =
                 (ReferenceInitializationRun.ordinary
                   (sourceReferenceInput rate rewards C_star C_h z)
                   (ReferenceInitializationRun.output
                     (sourceReferenceInput rate rewards C_star C_h z))
                   (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed ∧
               bankBirth a stateU.downBatch = some beta ∧
               stateU.downBatch.pending =
                 (Old.filter (fun test => test.time.val < u)).map
                   ReferenceGeneratedPrelaunchDownCohort.testEntry ∧
               ∀ w,
                 (if hU : u < p.T then
                    source_prelaunch_down_current_cohort_flags rate rewards C_star C_h z i
                      ⟨u, hU⟩ w
                  else
                    ((sourcePrelaunchDownTests rate rewards C_star C_h z i).map
                      (sourcePrelaunchDownCandidateFlag w)).drop
                        (AffineBatchDecoder.quota p * k)) =
                   (Old.filter (fun test => test.time.val < u)).map
                     (sourcePrelaunchDownCandidateFlag w))) ∧
      (∀ a', (ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z)).activation
            (ActualReferenceInitializationBlock.refFollower i) = some a' →
        a'.val = ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z)).completed + 1 →
        beta = ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z)).completed ∧
        ReferenceInitializationRun.ordinary
          (sourceReferenceInput rate rewards C_star C_h z)
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z))
          (ActualReferenceInitializationBlock.refFollower i) =
            ReferencePrelaunchFollower.initial p rate.eta ∧
        (ReferenceInitializationRun.ordinary
          (sourceReferenceInput rate rewards C_star C_h z)
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z))
          (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length = 0 ∧
        (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i
          (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z)).completed)
          (Nat.le_of_lt hStop)).drop
            (AffineBatchDecoder.quota p *
              (ReferenceInitializationRun.ordinary
                (sourceReferenceInput rate rewards C_star C_h z)
                (ReferenceInitializationRun.output
                  (sourceReferenceInput rate rewards C_star C_h z))
                (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length) = []) := by
  classical
  have hlaunchData :=
    ReferenceGeneratedPrelaunchDownPrefix.source_launch_down_pending_prefix
      rate rewards C_star C_h z i hStop hCross
  dsimp only at hlaunchData
  let launchSource := Classical.choose hlaunchData
  have hprops1 := Classical.choose_spec hlaunchData
  have hsource := hprops1.1
  have hprops2 := hprops1.2
  have hcorrect := hprops2.1
  have hprops3 := hprops2.2
  have hseed := hprops3.1
  have hprops4 := hprops3.2
  have hbatch := hprops4.1
  have hprops5 := hprops4.2
  have hfailure := hprops5.1
  have hprops6 := hprops5.2
  have hactivationExists := hprops6.1
  let a := Classical.choose hactivationExists
  have hactivationProps := Classical.choose_spec hactivationExists
  have ha := hactivationProps.1
  have hactivationCase := hactivationProps.2
  have hprops7 := hprops6.2
  have hnewBoundary := hprops7.1
  have hprops8 := hprops7.2
  have hshort := hprops8.1
  have hpending := hprops8.2
  have hActualTests := actual_stopped_endpoint_before_T rate rewards C_star C_h z i
    hCross hStop a ha
  have hinitialCases :=
    ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_initial_cases
      rate rewards C_star C_h z i
  have hActual : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z)).completed)
      (Nat.le_of_lt hStop) =
        some (a, ReferenceInitializationRun.ordinary
          (sourceReferenceInput rate rewards C_star C_h z)
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z))
          (ActualReferenceInitializationBlock.refFollower i)) := hActualTests.1
  obtain ⟨beta, hBeta, hBetaN, hBirthBank, hBirth, hUnique,
    hBoundary, hInterval⟩ :=
    actual_endpoint_historical_birth rate rewards C_star C_h z i
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z)).completed)
      (Nat.le_of_lt hStop) a _ hActual rfl ha
  refine ⟨launchSource, hsource, hcorrect, hseed, hbatch, hfailure,
    hnewBoundary, hshort, hpending, a, ha, ?_, hActual, hActualTests.2,
    beta, hBeta, hBetaN, hBirthBank, hBirth, hUnique,
    hBoundary, hInterval, ?_⟩
  · exact hactivationCase
  · intro a' ha' hnew
    have haActual : (ReferenceInitializationRun.output
        (sourceReferenceInput rate rewards C_star C_h z)).activation
          (ActualReferenceInitializationBlock.refFollower i) = some a' := ha'
    have hnewActual : a'.val = ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z)).completed + 1 := hnew
    have hinitial := hinitialCases.2 a' haActual hnewActual
    have hstateInitial : ReferenceInitializationRun.ordinary
        (sourceReferenceInput rate rewards C_star C_h z)
        (ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z))
        (ActualReferenceInitializationBlock.refFollower i) =
          ReferencePrelaunchFollower.initial p rate.eta := hinitial.1
    have hsame : a' = a := Option.some.inj (ha'.symm.trans ha)
    have hnewBank := hnewBoundary a' ha' hnew
    have hBirthAtNew : bankBirth a'
        (ReferenceInitializationRun.ordinary
          (sourceReferenceInput rate rewards C_star C_h z)
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z))
          (ActualReferenceInitializationBlock.refFollower i)).downBatch = some beta := by
      simpa [hsame] using hBirthBank
    have hBetaEq : beta = ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z)).completed :=
      Option.some.inj (hBirthAtNew.symm.trans hnewBank.2.2)
    have hTestsEmpty : sourcePrelaunchDownTestsAt rate rewards C_star C_h z i
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z)).completed)
        (Nat.le_of_lt hStop) = [] := by
      rw [hActualTests.2, hinitial.2]
    refine ⟨hBetaEq, hstateInitial, hnewBank.2.1, ?_⟩
    simp [hTestsEmpty]

/-- Deterministic launch join for the actual generated DOWN cohort.

For a crossing before `T`, the same corrected launch seed carries the actual
ordinary follower and its bank.  Its boundary is identified from the real
initial boundary or last completed-batch stamp, and the public interval result
retains every earlier test flag on the same original source.  At `T`, the
literal terminal census and empty physical suffix are used.  Without a
crossing, the terminal output, ancestry, census, and absent launch are retained.

The theorem is a deterministic history statement only; it asserts no
probability or event bound.
-/
theorem source_launch_down_historical_cohort
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let b := ReferenceInitializationRun.output x
    let s := ReferenceInitializationRun.elapsed p b.completed
    let f := ActualReferenceInitializationBlock.refFollower i
    let state := ReferenceInitializationRun.ordinary x b f
    (b.crossing = none →
      s = p.T ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = none ∧
      let W := (ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
        rate rewards C_star C_h z i).map ReferenceGeneratedPrelaunchDownCohort.testEntry
      W = AffineBatchDecoder.collected state.downBatch ∧
      state.downBatch.pending = W.drop
        (AffineBatchDecoder.quota p * state.downBatch.completed.length) ∧
      (∀ k (hk : k < state.downBatch.completed.length),
        state.downBatch.completed[k] =
          (W.drop (k * AffineBatchDecoder.quota p)).take (AffineBatchDecoder.quota p) ∧
        state.downBatch.completed[k].length = AffineBatchDecoder.quota p) ∧
      state.downBatch.pending.length < AffineBatchDecoder.quota p ∧
      sourcePrelaunchDownActualCohort rate rewards C_star C_h z i p.T le_rfl =
        ((b.activation f).map (fun a => (a, state))) ∧
      sourcePrelaunchDownTestsAt rate rewards C_star C_h z i p.T le_rfl =
        ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
          rate rewards C_star C_h z i ∧
      ∀ a, b.activation f = some a →
        ∃ beta, ∃ hBeta : beta ≤ p.T,
          beta ≤ s ∧ bankBirth a state.downBatch = some beta ∧
          birthAt rate rewards C_star C_h z i beta hBeta state.downBatch.completed.length ∧
          ∀ beta', bankBirth a state.downBatch = some beta' → beta' = beta) ∧
    (∀ _hCross : b.crossing.isSome = true,
      (∀ hStop : s < p.T,
        ∃ launchSource : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hStop,
          launchSource.val = z ∧
          ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
            some (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
              rate rewards C_star C_h s hStop launchSource) ∧
          (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
            rate rewards C_star C_h s hStop launchSource).followers i =
            .ordinary state (ActiveFollowerLifecycle.initialMemory p) ∧
          ReferenceFollowerDecoderChronology.downBatchSeed
            (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
              rate rewards C_star C_h s hStop launchSource) s ∧
          ReferenceInitializationRun.initializationFailure x b f =
            (b.forcedFailure f || state.initializationFailure) ∧
          (∀ a', b.activation f = some a' → a'.val = s + 1 →
            state.downBatch.pending = [] ∧ state.downBatch.completed.length = 0 ∧
            bankBirth a' state.downBatch = some s) ∧
          state.downBatch.pending.length < AffineBatchDecoder.quota p ∧
          state.downBatch.pending =
            ((ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
              rate rewards C_star C_h z i).map
                ReferenceGeneratedPrelaunchDownCohort.testEntry).drop
              (AffineBatchDecoder.quota p * state.downBatch.completed.length) ∧
          ∃ a, b.activation f = some a ∧
            ((b.forcedFailure f = true ∧ state = ReferencePrelaunchFollower.initial p rate.eta ∧
                a.val = s + 1) ∨
             (b.forcedFailure f = false ∧
                state = ReferencePrelaunchFollower.replay rate.eta i x.row a
                  (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m f))
                  (ReferenceInitializationRun.elapsed_le_T p b.completed))) ∧
            sourcePrelaunchDownActualCohort rate rewards C_star C_h z i s
              (Nat.le_of_lt hStop) = some (a, state) ∧
            sourcePrelaunchDownTestsAt rate rewards C_star C_h z i s
              (Nat.le_of_lt hStop) =
                ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
                  rate rewards C_star C_h z i ∧
            ∃ beta, ∃ hBeta : beta ≤ p.T,
              beta ≤ s ∧ bankBirth a state.downBatch = some beta ∧
              birthAt rate rewards C_star C_h z i beta hBeta state.downBatch.completed.length ∧
              (∀ beta', bankBirth a state.downBatch = some beta' → beta' = beta) ∧
              sourcePrelaunchDownCohortBoundary rate rewards C_star C_h z i
                state.downBatch.completed.length = some beta ∧
              (let k := state.downBatch.completed.length
               let Old := (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i s
                    (Nat.le_of_lt hStop)).drop (AffineBatchDecoder.quota p * k)
               Old.map ReferenceGeneratedPrelaunchDownCohort.testEntry = state.downBatch.pending ∧
               Old.length < AffineBatchDecoder.quota p ∧
               (∀ test ∈ Old, beta ≤ test.time.val ∧ test.time.val < s) ∧
               ∀ u, beta ≤ u → ∀ hu : u ≤ s,
                 ∃ stateU,
                   sourcePrelaunchDownActualCohort rate rewards C_star C_h z i u
                     (hu.trans (Nat.le_of_lt hStop)) = some (a, stateU) ∧
                   stateU.downBatch.completed = state.downBatch.completed ∧
                   bankBirth a stateU.downBatch = some beta ∧
                   stateU.downBatch.pending =
                     (Old.filter (fun test => test.time.val < u)).map
                       ReferenceGeneratedPrelaunchDownCohort.testEntry ∧
                   ∀ w,
                     (if hU : u < p.T then
                        source_prelaunch_down_current_cohort_flags rate rewards C_star C_h z i
                          ⟨u, hU⟩ w
                      else
                        ((sourcePrelaunchDownTests rate rewards C_star C_h z i).map
                          (sourcePrelaunchDownCandidateFlag w)).drop
                            (AffineBatchDecoder.quota p * k)) =
                     (Old.filter (fun test => test.time.val < u)).map
                       (sourcePrelaunchDownCandidateFlag w)) ∧
            (∀ a', b.activation f = some a' → a'.val = s + 1 →
              beta = s ∧
              state = ReferencePrelaunchFollower.initial p rate.eta ∧
              state.downBatch.completed.length = 0 ∧
              (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i s
                (Nat.le_of_lt hStop)).drop
                  (AffineBatchDecoder.quota p * state.downBatch.completed.length) = []))
      ∧ (¬ s < p.T →
        s = p.T ∧
        ∃ active, ∃ hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active p.T,
          ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
            some active ∧
          ReferenceInitializationRun.launchRound x = p.T + 1 ∧
          (ReferenceActivePhysicalHorizon.run active z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards p.T 0
            (Nat.le_refl _) hmode).finalState = active ∧
          (ReferenceActivePhysicalHorizon.run active z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards p.T 0
            (Nat.le_refl _) hmode).records = [] ∧
          active.followers i = .ordinary state (ActiveFollowerLifecycle.initialMemory p) ∧
          (∀ j, some (active.activations j) =
            b.activation (ActualReferenceInitializationBlock.refFollower j)) ∧
          ∃ a, b.activation f = some a ∧
            ReferenceInitializationRun.initializationFailure x b f =
              (b.forcedFailure f || state.initializationFailure) ∧
            sourcePrelaunchDownActualCohort rate rewards C_star C_h z i p.T le_rfl =
              some (a, state) ∧
            sourcePrelaunchDownTestsAt rate rewards C_star C_h z i p.T le_rfl =
              ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
                rate rewards C_star C_h z i ∧
            ∃ beta, ∃ hBeta : beta ≤ p.T,
              beta ≤ s ∧ bankBirth a state.downBatch = some beta ∧
              birthAt rate rewards C_star C_h z i beta hBeta state.downBatch.completed.length ∧
              (∀ beta', bankBirth a state.downBatch = some beta' → beta' = beta) ∧
              sourcePrelaunchDownCohortBoundary rate rewards C_star C_h z i
                state.downBatch.completed.length = some beta ∧
              (let k := state.downBatch.completed.length
               let Old := (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i p.T le_rfl).drop
                    (AffineBatchDecoder.quota p * k)
               Old.map ReferenceGeneratedPrelaunchDownCohort.testEntry = state.downBatch.pending ∧
               Old.length < AffineBatchDecoder.quota p ∧
               (∀ test ∈ Old, beta ≤ test.time.val ∧ test.time.val < p.T) ∧
               ∀ u, beta ≤ u → ∀ hu : u ≤ p.T,
                 ∃ stateU,
                   sourcePrelaunchDownActualCohort rate rewards C_star C_h z i u hu =
                     some (a, stateU) ∧
                   stateU.downBatch.completed = state.downBatch.completed ∧
                   bankBirth a stateU.downBatch = some beta ∧
                   stateU.downBatch.pending =
                     (Old.filter (fun test => test.time.val < u)).map
                       ReferenceGeneratedPrelaunchDownCohort.testEntry ∧
                   ∀ w,
                     (if hU : u < p.T then
                        source_prelaunch_down_current_cohort_flags rate rewards C_star C_h z i
                          ⟨u, hU⟩ w
                      else
                        ((sourcePrelaunchDownTests rate rewards C_star C_h z i).map
                          (sourcePrelaunchDownCandidateFlag w)).drop
                            (AffineBatchDecoder.quota p * k)) =
                     (Old.filter (fun test => test.time.val < u)).map
                       (sourcePrelaunchDownCandidateFlag w)) ∧
              (∀ a', b.activation f = some a' → a'.val = s + 1 →
                beta = s ∧
                state = ReferencePrelaunchFollower.initial p rate.eta ∧
                state.downBatch.completed.length = 0 ∧
                (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i p.T le_rfl).drop
                  (AffineBatchDecoder.quota p * state.downBatch.completed.length) = []))) := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  let b := ReferenceInitializationRun.output x
  let s := ReferenceInitializationRun.elapsed p b.completed
  let f := ActualReferenceInitializationBlock.refFollower i
  let state := ReferenceInitializationRun.ordinary x b f
  constructor
  · intro hNoCross
    have hNoCross' : (ReferenceInitializationRun.output x).crossing = none := by
      simpa [b, x] using hNoCross
    have hNoCrossData :=
      ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_no_crossing
        rate rewards C_star C_h z hNoCross'
    have hTerminal :=
      ReferenceGeneratedPrelaunchDownHistoricalBirth.source_prelaunch_down_terminal_birth_history
        rate rewards C_star C_h z i
    have hCensus :=
      ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_cohorts
        rate rewards C_star C_h z i
    dsimp only at hCensus
    refine ⟨hNoCrossData.1, hNoCrossData.2, ?_, ?_, ?_, ?_, ?_,
      sourcePrelaunchDownTestsAt_terminal rate rewards C_star C_h z i le_rfl, ?_⟩
    · simpa [sourceReferenceInput, x, b, state, f] using hCensus.1
    · simpa [sourceReferenceInput, x, b, state, f] using hCensus.2.1
    · simpa [sourceReferenceInput, x, b, state, f] using hCensus.2.2.1
    · simpa [sourceReferenceInput, x, b, state, f] using hCensus.2.2.2
    · exact sourcePrelaunchDownActualCohort_at_terminal
        rate rewards C_star C_h z i le_rfl
    · intro a ha
      simpa [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_terminal,
        sourceReferenceInput, x, b, state, f, s] using hTerminal a ha
  · intro hCross
    constructor
    · intro hStop
      exact source_launch_down_before_T rate rewards C_star C_h z i hCross hStop
    · intro hNotStop
      have hTerminalTime : s = p.T := by
        have hNotStop' : ¬ ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output x).completed < p.T := by
          simpa [b, x] using hNotStop
        have hle : ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output x).completed ≤ p.T :=
          ReferenceInitializationRun.elapsed_le_T p _
        have heq := Nat.le_antisymm hle (Nat.le_of_not_gt hNotStop')
        simpa [b, x, s] using heq
      have hCross' :
          (ReferenceInitializationRun.output x).crossing.isSome = true := by
        simpa [b, x, sourceReferenceInput,
          ActualReferenceInitializationBlock.referenceInput] using hCross
      have hTerminalTime' :
          ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output x).completed = p.T := by
        simpa [b, x] using hTerminalTime
      have hTerminalCross :=
        ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_terminal_crossing
          rate rewards C_star C_h z hCross' hTerminalTime'
      obtain ⟨terminalActive, hmode, hlaunch, hround, hfinal, hrecords⟩ := hTerminalCross
      obtain ⟨active, hfields, _⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
          rate z rewards C_star C_h hCross'
      have hsame : active = terminalActive :=
        Option.some.inj (hfields.1.symm.trans hlaunch)
      subst active
      have hCrossRun :
          (ReferenceInitializationRun.run x (n_boot p)).crossing.isSome = true := by
        simpa [x, sourceReferenceInput, ReferenceInitializationRun.output,
          ActualReferenceInitializationBlock.referenceInput] using hCross
      have hallActivated := ReferenceInitializationRun.run_all_activated_at_crossing
        x (n_boot p) hCrossRun f
      have hallActivated' : (b.activation f).isSome = true := by
        simpa [b, ReferenceInitializationRun.output] using hallActivated
      have hSomeActivation : ∃ a, b.activation f = some a := by
        cases ha : b.activation f with
        | none => simp [ha] at hallActivated'
        | some a => exact ⟨a, rfl⟩
      obtain ⟨a, hActivation⟩ := hSomeActivation
      have hActual : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i p.T le_rfl =
          some (a, state) := by
        rw [sourcePrelaunchDownActualCohort_at_terminal rate rewards C_star C_h z i le_rfl]
        simp [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_terminal,
          b, x, state, f, hActivation]
        rfl
      obtain ⟨beta, hBeta, hBetaN, hBirthBank, hBirth, hUnique,
        hBoundary, hInterval⟩ :=
        actual_endpoint_historical_birth rate rewards C_star C_h z i p.T le_rfl a state
          hActual rfl hActivation
      have hBetaS : beta ≤ s := by
        simpa [hTerminalTime] using hBetaN
      have hTests := sourcePrelaunchDownTestsAt_terminal rate rewards C_star C_h z i le_rfl
      have hinitialCases :=
        ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_initial_cases
          rate rewards C_star C_h z i
      refine ⟨hTerminalTime, terminalActive, hmode, hlaunch, hround,
        hfinal, hrecords, ?_, ?_, a, hActivation, rfl, hActual, hTests,
        beta, hBeta, hBetaS, hBirthBank, hBirth, hUnique, hBoundary, hInterval, ?_⟩
      · exact hfields.2.2.2.2 i
      · intro j
        exact hfields.2.2.2.1 j
      · intro a' ha' hnew
        have haActual : b.activation f = some a' := by
          simpa [b] using ha'
        have hnewActual : a'.val = ReferenceInitializationRun.elapsed p b.completed + 1 := by
          simpa [s, b] using hnew
        have hinitial := hinitialCases.2 a' haActual hnewActual
        have hstateInitial : state = ReferencePrelaunchFollower.initial p rate.eta := by
          simpa [state, f, b, x, sourceReferenceInput] using hinitial.1
        have hsame : a' = a := Option.some.inj (ha'.symm.trans hActivation)
        have hBirthA' : bankBirth a' state.downBatch = some beta := by
          simpa [hsame] using hBirthBank
        have hBirthNew : bankBirth a' state.downBatch = some s := by
          rw [hstateInitial]
          simp [bankBirth, ReferencePrelaunchFollower.initial,
            AffineBatchDecoder.initial, hnew, s, b, x]
        have hBetaEq : beta = s := Option.some.inj (hBirthA'.symm.trans hBirthNew)
        have hbankEmpty : state.downBatch.completed.length = 0 := by
          simp [hstateInitial, ReferencePrelaunchFollower.initial,
            AffineBatchDecoder.initial]
        have hOldEmpty :
            (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i p.T le_rfl).drop
              (AffineBatchDecoder.quota p * state.downBatch.completed.length) = [] := by
          rw [hTests, hinitial.2]
          simp
        exact ⟨hBetaEq, hstateInitial, hbankEmpty, hOldEmpty⟩

end Bandits.Support.ReferenceGeneratedPrelaunchDownLaunchCohortHistory

end
