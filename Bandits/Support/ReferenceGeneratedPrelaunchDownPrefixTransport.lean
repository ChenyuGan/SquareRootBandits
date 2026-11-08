/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownPrefix

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.OfFn

/-!
# Calendar and block transport for generated prelaunch DOWN prefixes

Sources: `appendix_a_local_protocol.tex:111-153`,
`appendix_b_communication.tex:724-736`, `07_public_setup.tex:60-112,127-142`,
and `05_binary_transport.tex:20-42`.

This module transports the actual prefix selectors and follower replay. It
does not add a history, a decoder bank, or a successful-observation premise.
The source input remains the original whole row and private stream.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownPrefixTransport

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceGeneratedPrelaunchDownPrefix
open Bandits.Support.ReferenceGeneratedPrelaunchDownCohort
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.AffineBatchDecoder
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

private theorem prefixHistory_same_generated_boundary
    (x : ReferenceInitializationRun.Input p) (j : Fin p.m)
    {bNext b : ReferenceInitializationRun.Boundary p} (hboundary : bNext = b)
    (hremainNext : bNext.completed < n_boot p) (hremain : b.completed < n_boot p)
    {k : ℕ} (hbeforeNext : k ≤ ReferenceInitializationRun.elapsed p (bNext.completed + 1))
    (hbefore : k ≤ ReferenceInitializationRun.elapsed p (b.completed + 1)) :
    ReferencePrelaunchLifecycleReplay.prefixHistory
        (ReferenceInitializationRun.extendedHistory x bNext hremainNext j) k hbeforeNext =
      ReferencePrelaunchLifecycleReplay.prefixHistory
        (ReferenceInitializationRun.extendedHistory x b hremain j) k hbefore := by
  revert hremainNext hremain hbeforeNext hbefore
  cases hboundary
  intro hremainNext hremain hbeforeNext hbefore
  have hproof : hremainNext = hremain := Subsingleton.elim _ _
  subst hremainNext
  have hbound : hbeforeNext = hbefore := Subsingleton.elim _ _
  subst hbeforeNext
  rfl

/-- The generated active branch has the literal ordinary replay registers and
the actual prefix census invariant. Its step retains the full sparse log and
the suppressed-DOWN failure disjunction. -/
theorem source_prelaunch_down_active_operation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inl active) =>
        let x := sourceReferenceInput rate rewards C_star C_h z
        let b := active.val.1.val
        let a := active.val.2.1
        let state := active.val.2.2.2
        let own := ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical x b active.val.1.property.1)
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) r
        let bank := state.downBatch
        source_prelaunch_down_current_test rate rewards C_star C_h z i r =
            ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a r own ∧
          state.status = .unoccupied ∧
          bank.pending.length < AffineBatchDecoder.quota p ∧
          (∀ batch ∈ bank.completed, batch.length = AffineBatchDecoder.quota p) ∧
          (ReferencePrelaunchFollower.step i x.row a r own state).downBatch =
            (ReferencePrelaunchFollower.decodeAt i x.row a r own bank).1 ∧
          (ReferencePrelaunchFollower.step i x.row a r own state).buffer =
            state.buffer ++ ReferencePrelaunchFollower.logAt i x.row a r own ∧
          (ReferencePrelaunchFollower.step i x.row a r own state).initializationFailure =
            (state.initializationFailure || decide
              (ReferencePrelaunchFollower.passing_at rate.eta i x.row a r own bank))
    | _ => True := by
  classical
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          simp only [hpref]
          let x := sourceReferenceInput rate rewards C_star C_h z
          let b := active.val.1.val
          let a := active.val.2.1
          let history := active.val.2.2.1
          let state := active.val.2.2.2
          let f := ActualReferenceInitializationBlock.refFollower i
          let own := ReferenceInitializationRun.ownEntry
            (ReferenceInitializationRun.physical x b active.val.1.property.1)
            (PublicDiscreteDraws.followerPlayer p.two_le_m f) r
          rcases active.property with ⟨hbefore, hactivation, hstate, hhistory⟩
          have hregisters := ReferencePrelaunchFollower.replay_registers
            x.eta i x.row a history (Nat.le_of_lt r.isLt)
          have hstatus : state.status = .unoccupied := by
            simpa only [state, hstate] using hregisters.2.2.2.2.2
          have hcensus := source_prelaunch_down_prefix_census
            rate rewards C_star C_h z i r
          have hcensus' :
              (source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r).map
                  ReferenceGeneratedPrelaunchDownCohort.testEntry =
                  AffineBatchDecoder.collected state.downBatch ∧
                state.downBatch.pending =
                  ((source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r).map
                    ReferenceGeneratedPrelaunchDownCohort.testEntry).drop
                    (AffineBatchDecoder.quota p * state.downBatch.completed.length) ∧
                (∀ batch ∈ state.downBatch.completed,
                  batch.length = AffineBatchDecoder.quota p) ∧
                state.downBatch.pending.length < AffineBatchDecoder.quota p := by
            simpa only [hpref] using hcensus
          have hcurrent : source_prelaunch_down_current_test rate rewards C_star C_h z i r =
              ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a r own := by
            simp only [source_prelaunch_down_current_test, hpref]
            rfl
          have hbank := ReferencePrelaunchFollower.decodeAt_fst i x.row a r own
            state.downBatch hcensus'.2.2.2
          have hstepbank :
              (ReferencePrelaunchFollower.step i x.row a r own state).downBatch =
                AffineBatchDecoder.step p (ReferencePrelaunchFollower.traceAt i x.row a r own)
                  state.downBatch r := by
            simp only [ReferencePrelaunchFollower.step, hstatus, if_pos, hbank]
          refine ⟨hcurrent, hstatus, hcensus'.2.2.2, hcensus'.2.2.1, ?_, ?_, ?_⟩
          · calc
              (ReferencePrelaunchFollower.step i x.row a r own state).downBatch =
                  AffineBatchDecoder.step p
                    (ReferencePrelaunchFollower.traceAt i x.row a r own) state.downBatch r :=
                    hstepbank
              _ = (ReferencePrelaunchFollower.decodeAt i x.row a r own state.downBatch).1 :=
                hbank.symm
          · change (ReferencePrelaunchFollower.step i x.row a r own state).buffer =
                state.buffer ++ ReferencePrelaunchFollower.logAt i x.row a r own
            simp [ReferencePrelaunchFollower.step, hstatus]
          · change (ReferencePrelaunchFollower.step i x.row a r own state).initializationFailure =
                (state.initializationFailure || decide
                  (ReferencePrelaunchFollower.passing_at
                    (sourceReferenceInput rate rewards C_star C_h z).eta
                    i x.row a r own state.downBatch))
            simp [ReferencePrelaunchFollower.step, hstatus]
      | inr _ => simp only [hpref]
  | inr _ => simp only [hpref]

/-- Exact local bank operation for a generated active step. Eligible subquota
positives append the stamped current entry. At quota, the same batch is
completed and its raw solver result is returned, including `none`. -/
theorem source_prelaunch_down_active_batch_transition
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inl active) =>
        let x := sourceReferenceInput rate rewards C_star C_h z
        let a := active.val.2.1
        let state := active.val.2.2.2
        let own := ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical x active.val.1.val
            active.val.1.property.1)
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) r
        let tr := ReferencePrelaunchFollower.traceAt i x.row a r own
        let bank := state.downBatch
        let appended := bank.pending ++ AffineBatchDecoder.positiveAt p tr r
        let decoded := ReferencePrelaunchFollower.decodeAt i x.row a r own bank
        let next := (ReferencePrelaunchFollower.step i x.row a r own state).downBatch
        (AffineBatchDecoder.eligible (tr r) →
          appended.length < AffineBatchDecoder.quota p →
            next = ⟨appended, bank.completed⟩ ∧ decoded.2 = none) ∧
        (AffineBatchDecoder.eligible (tr r) →
          AffineBatchDecoder.quota p ≤ appended.length →
            next = ⟨[], bank.completed ++ [appended]⟩ ∧
              decoded.2 = AffineBatchDecoder.batchOutput appended) ∧
        (¬ AffineBatchDecoder.eligible (tr r) → next = bank ∧ decoded.2 = none)
    | _ => True := by
  classical
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          simp only [hpref]
          let x := sourceReferenceInput rate rewards C_star C_h z
          let a := active.val.2.1
          let history := active.val.2.2.1
          let state := active.val.2.2.2
          let own := ReferenceInitializationRun.ownEntry
            (ReferenceInitializationRun.physical x active.val.1.val
              active.val.1.property.1)
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) r
          let tr := ReferencePrelaunchFollower.traceAt i x.row a r own
          let bank := state.downBatch
          let appended := bank.pending ++ AffineBatchDecoder.positiveAt p tr r
          let decoded := ReferencePrelaunchFollower.decodeAt i x.row a r own bank
          let next := (ReferencePrelaunchFollower.step i x.row a r own state).downBatch
          rcases active.property with ⟨_, _, hstate, _⟩
          have hregisters := ReferencePrelaunchFollower.replay_registers
            x.eta i x.row a history (Nat.le_of_lt r.isLt)
          have hstatus : state.status = .unoccupied := by
            simpa only [state, hstate] using hregisters.2.2.2.2.2
          have hcensus := source_prelaunch_down_prefix_census
            rate rewards C_star C_h z i r
          rw [hpref] at hcensus
          have hcensus' : bank.pending.length < AffineBatchDecoder.quota p := by
            simpa only [state, bank] using hcensus.2.2.2
          have hnext : next = AffineBatchDecoder.step p tr bank r := by
            change (ReferencePrelaunchFollower.step i x.row a r own state).downBatch =
              AffineBatchDecoder.step p tr bank r
            unfold ReferencePrelaunchFollower.step
            rw [if_pos hstatus]
            exact ReferencePrelaunchFollower.decodeAt_fst i x.row a r own state.downBatch hcensus'
          constructor
          · intro heligible hsubquota
            have hpositive : AffineBatchDecoder.positiveAt p tr r =
                [AffineBatchDecoder.entry p tr r] := by
              change (if AffineBatchDecoder.eligible (tr r) then
                [AffineBatchDecoder.entry p tr r] else []) = _
              rw [if_pos heligible]
            have happended : appended = bank.pending ++ [AffineBatchDecoder.entry p tr r] := by
              simp only [appended, hpositive]
            have hlen : bank.pending.length + (AffineBatchDecoder.positiveAt p tr r).length <
                AffineBatchDecoder.quota p := by
              simpa only [List.length_append] using hsubquota
            have hstate : AffineBatchDecoder.step p tr bank r =
                ⟨appended, bank.completed⟩ := by
              unfold AffineBatchDecoder.step
              simp only [List.length_append, if_pos hlen]
              rfl
            have hpair : decoded = AffineBatchDecoder.decodeStep p tr bank r := by
              change (if (tr r).selected = true then
                AffineBatchDecoder.decodeStep p tr bank r
              else (bank, none)) = AffineBatchDecoder.decodeStep p tr bank r
              rw [heligible.1]
              rfl
            have hraw : decoded.2 = none := by
              rw [hpair]
              change AffineBatchDecoder.stepOutput p tr bank r = none
              simp [AffineBatchDecoder.stepOutput, hlen]
            exact ⟨hnext.trans hstate, hraw⟩
          constructor
          · intro heligible hquotaBound
            have hpositive : AffineBatchDecoder.positiveAt p tr r =
                [AffineBatchDecoder.entry p tr r] := by
              change (if AffineBatchDecoder.eligible (tr r) then
                [AffineBatchDecoder.entry p tr r] else []) = _
              rw [if_pos heligible]
            have happended : appended = bank.pending ++ [AffineBatchDecoder.entry p tr r] := by
              simp only [appended, hpositive]
            have hquotaBound' : AffineBatchDecoder.quota p ≤
                (bank.pending ++ AffineBatchDecoder.positiveAt p tr r).length := by
              simpa only [appended] using hquotaBound
            have hupper : AffineBatchDecoder.quota p ≤ bank.pending.length + 1 := by
              rw [List.length_append, hpositive, List.length_singleton] at hquotaBound'
              exact hquotaBound'
            have hquota : bank.pending.length + 1 = AffineBatchDecoder.quota p := by
              omega
            have hstate : AffineBatchDecoder.step p tr bank r =
                ⟨[], bank.completed ++ [appended]⟩ := by
              simpa [appended, hpositive] using
                AffineBatchDecoder.step_complete p tr bank r heligible hquota
            have hpair : decoded = AffineBatchDecoder.decodeStep p tr bank r := by
              change (if (tr r).selected = true then
                AffineBatchDecoder.decodeStep p tr bank r
              else (bank, none)) = AffineBatchDecoder.decodeStep p tr bank r
              rw [heligible.1]
              rfl
            have hraw : decoded.2 = AffineBatchDecoder.batchOutput appended := by
              rw [hpair]
              simpa [appended, hpositive] using congrArg Prod.snd
                (AffineBatchDecoder.decodeStep_complete p tr bank r heligible hquota)
            exact ⟨hnext.trans hstate, hraw⟩
          · intro heligible
            have hstate : AffineBatchDecoder.step p tr bank r = bank :=
              AffineBatchDecoder.step_ineligible p tr bank r hcensus' heligible
            have hraw : decoded.2 = none := by
              cases hselected : (ReferencePrelaunchFollower.downInput i x.row a r own).selected with
              | false =>
                  change (if (tr r).selected = true then
                    AffineBatchDecoder.decodeStep p
                      tr bank r
                  else (bank, none)).2 = none
                  have hnot : (tr r).selected ≠ true := by
                    change (ReferencePrelaunchFollower.downInput i x.row a r own).selected ≠ true
                    simp [hselected]
                  simp [hnot]
              | true =>
                  have hzero : (tr r).roundedReward = 0 := by
                    apply le_antisymm
                    · exact le_of_not_gt fun hpos => heligible ⟨hselected, rfl, hpos⟩
                    · change 0 ≤ own.2.val.val
                      exact (own.2.val.property).1
                  have hpair : decoded = AffineBatchDecoder.decodeStep p tr bank r := by
                    change (if (tr r).selected = true then
                      AffineBatchDecoder.decodeStep p tr bank r
                    else (bank, none)) = AffineBatchDecoder.decodeStep p tr bank r
                    change (tr r).selected = true at hselected
                    rw [hselected]
                    rfl
                  rw [hpair]
                  change AffineBatchDecoder.stepOutput p tr bank r = none
                  have hpositive : AffineBatchDecoder.positiveAt p tr r = [] := by
                    rw [AffineBatchDecoder.positiveAt, if_neg heligible]
                  simp [AffineBatchDecoder.stepOutput, hpositive, hcensus']
            exact ⟨hnext.trans hstate, hraw⟩
      | inr _ => trivial
  | inr _ => trivial

/-- Within one actual calendar block, an active generated prefix extends by
the physical own entry at the next round. The successor replay is the actual
`F.step`, and the chronological test census appends exactly the current test's
option list. At a block boundary the next theorem must use the run successor. -/
theorem source_prelaunch_down_same_block_active_transport
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hnext : r.val + 1 < p.T) :
    let rNext : Fin p.T := ⟨r.val + 1, hnext⟩
    roundBlockIndex p rNext = roundBlockIndex p r →
      match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
      | .inl (.inl active) =>
          match source_prelaunch_down_prefix rate rewards C_star C_h z i rNext with
          | .inl (.inl nextActive) =>
              nextActive.val.2.2.2 =
                  ReferencePrelaunchFollower.step i
                    (sourceReferenceInput rate rewards C_star C_h z).row
                    active.val.2.1 r
                    (ReferenceInitializationRun.ownEntry
                      (ReferenceInitializationRun.physical
                        (sourceReferenceInput rate rewards C_star C_h z)
                        active.val.1.val active.val.1.property.1)
                      (PublicDiscreteDraws.followerPlayer p.two_le_m
                        (ActualReferenceInitializationBlock.refFollower i)) r)
                    active.val.2.2.2 ∧
                source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rNext =
                  source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++
                    (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList
          | _ => False
      | _ => True
    := by
  classical
  dsimp only
  intro hsame
  let rNext : Fin p.T := ⟨r.val + 1, hnext⟩
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | inl branch =>
        cases branch with
        | inl active =>
            cases hnext : source_prelaunch_down_prefix rate rewards C_star C_h z i rNext with
            | inl nextBranch =>
                cases nextBranch with
                | inl nextActive =>
                    simp only [hpref, hnext]
                    let x := sourceReferenceInput rate rewards C_star C_h z
                    let follower := ActualReferenceInitializationBlock.refFollower i
                    let b := active.val.1.val
                    let a := active.val.2.1
                    let history := active.val.2.2.1
                    let historyNext := nextActive.val.2.2.1
                    let state := active.val.2.2.2
                    let stateNext := nextActive.val.2.2.2
                    let own := ReferenceInitializationRun.ownEntry
                      (ReferenceInitializationRun.physical x b active.val.1.property.1)
                      (PublicDiscreteDraws.followerPlayer p.two_le_m follower) r
                    rcases active.property with ⟨hbefore, hactivation, hstate, hhistory⟩
                    rcases nextActive.property with
                      ⟨hbeforeNext, hactivationNext, hstateNext, hhistoryNext⟩
                    have hboundary : nextActive.val.1.val = b := by
                      calc
                        nextActive.val.1.val = ReferenceInitializationRun.run x
                            (roundBlockIndex p rNext).val :=
                          nextActive.val.1.property.2.2
                        _ = ReferenceInitializationRun.run x
                            (roundBlockIndex p r).val := by
                              rw [hsame]
                        _ = active.val.1.val :=
                          active.val.1.property.2.2.symm
                        _ = b := rfl
                    have hactivationEq : nextActive.val.2.1 = a := by
                      have hs : some nextActive.val.2.1 = some a := by
                        calc
                          some nextActive.val.2.1 = nextActive.val.1.val.activation follower :=
                            hactivationNext.symm
                          _ = b.activation follower := by rw [hboundary]
                          _ = some a := hactivation
                      exact Option.some.inj hs
                    rw [hactivationEq] at hstateNext
                    have hremain : b.completed < n_boot p := active.val.1.property.1
                    have hbeforeNext' : rNext.val ≤
                        ReferenceInitializationRun.elapsed p (b.completed + 1) := by
                      rw [← hboundary]
                      exact hbeforeNext
                    have hremainNext : nextActive.val.1.val.completed < n_boot p :=
                      nextActive.val.1.property.1
                    have hprefixEq := prefixHistory_same_generated_boundary x
                      (PublicDiscreteDraws.followerPlayer p.two_le_m follower)
                      hboundary hremainNext hremain hbeforeNext hbeforeNext'
                    have hhistoryNext' : historyNext =
                        ReferencePrelaunchLifecycleReplay.prefixHistory
                          (ReferenceInitializationRun.extendedHistory x b hremain
                            (PublicDiscreteDraws.followerPlayer p.two_le_m follower))
                          rNext.val hbeforeNext' := hhistoryNext.trans hprefixEq
                    have hcompleted : b.completed =
                        (roundBlockIndex p r).val := by
                      have hgen := active.val.1.property.2.2
                      have hrunCross :
                          (ReferenceInitializationRun.run
                            (GeneratedBootstrapRoundLaw.input p x.ids x.rewards x.C_star x.C_h
                              x.eta (x.row, x.coordinates))
                            (roundBlockIndex p r).val).crossing = none := by
                        change (ReferenceInitializationRun.run x
                          (roundBlockIndex p r).val).crossing = none
                        rw [← hgen]
                        exact active.val.1.property.2.1
                      calc
                        b.completed = active.val.1.val.completed := rfl
                        _ = (ReferenceInitializationRun.run x
                            (roundBlockIndex p r).val).completed :=
                          congrArg ReferenceInitializationRun.Boundary.completed
                            active.val.1.property.2.2
                        _ = (roundBlockIndex p r).val := by
                          change (ReferenceInitializationRun.run
                            (GeneratedBootstrapRoundLaw.input p x.ids x.rewards x.C_star x.C_h
                              x.eta (x.row, x.coordinates))
                            (roundBlockIndex p r).val).completed = _
                          exact GeneratedBootstrapRoundLaw.processed_completed x.ids x.rewards
                            x.C_star x.C_h x.eta
                            (roundBlockIndex p r)
                            (x.row, x.coordinates) hrunCross
                    have hcalendar := BootstrapDimensions.round_mem_quotient_block p r
                    have htime : ReferenceInitializationRun.elapsed p b.completed ≤ r.val := by
                      rw [hcompleted]
                      exact GeneratedBootstrapRoundLaw.elapsed_le_of_mem_calendarBlock
                        (s := roundBlockIndex p r)
                        (t := r) hcalendar
                    have hshort :
                        (fun u : Fin r.val => historyNext u.castSucc) = history := by
                      funext u
                      rw [hhistoryNext']
                      change _ = active.val.2.2.1 u
                      rw [hhistory]
                      unfold ReferencePrelaunchLifecycleReplay.prefixHistory
                      apply congrArg
                        (ReferenceInitializationRun.extendedHistory x b hremain
                          (PublicDiscreteDraws.followerPlayer p.two_le_m follower))
                      apply Fin.ext
                      rfl
                    have hlast : historyNext (Fin.last r.val) = own := by
                      rw [hhistoryNext']
                      unfold ReferencePrelaunchLifecycleReplay.prefixHistory
                      change ReferenceInitializationRun.extendedHistory x b hremain
                          (PublicDiscreteDraws.followerPlayer p.two_le_m follower)
                          (Fin.castLE hbeforeNext' (Fin.last r.val)) = own
                      have hsuccessorBound : r.val + 1 ≤
                          ReferenceInitializationRun.elapsed p (b.completed + 1) := by
                        simpa only [rNext] using hbeforeNext'
                      have hlastBound : r.val <
                          ReferenceInitializationRun.elapsed p (b.completed + 1) :=
                        Nat.lt_of_lt_of_le (Nat.lt_succ_self r.val) hsuccessorBound
                      have hcast :
                          Fin.castLE hbeforeNext' (Fin.last r.val) =
                            (⟨r.val, hlastBound⟩ :
                              Fin (ReferenceInitializationRun.elapsed p (b.completed + 1))) :=
                        Fin.ext rfl
                      rw [hcast]
                      have hnotPast : ¬ r.val <
                          ReferenceInitializationRun.elapsed p b.completed :=
                        Nat.not_lt_of_ge htime
                      simp only [ReferenceInitializationRun.extendedHistory,
                        dite_eq_right hnotPast]
                      rfl
                    have hsuccessorReplay :=
                      ActualReferenceInitializationBlock.replay_succ x.eta i x.row a
                        historyNext (Nat.succ_le_of_lt r.isLt)
                    rw [hshort, hlast, ← hstate] at hsuccessorReplay
                    have hstateTransport : stateNext =
                        ReferencePrelaunchFollower.step i x.row a r own state := by
                      calc
                        stateNext = ReferencePrelaunchFollower.replay x.eta i x.row a
                            historyNext (Nat.le_of_lt rNext.isLt) := hstateNext
                        _ = ReferencePrelaunchFollower.step i x.row a r own state := by
                          simpa only [rNext] using hsuccessorReplay
                    refine ⟨hstateTransport, ?_⟩
                    have htestAppend :
                        source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rNext =
                          source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++
                            (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList := by
                      simp only [source_prelaunch_down_prefix_tests, hpref, hnext]
                      rw [hactivationEq]
                      have hcurrent :
                          source_prelaunch_down_current_test rate rewards C_star C_h z i r =
                            ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a r own := by
                        simp only [source_prelaunch_down_current_test, hpref]
                        rfl
                      rw [hcurrent]
                      change
                        (List.ofFn (fun u : Fin (r.val + 1) => u)).filterMap
                            (fun u => ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i
                              x.row a
                              (ReferencePrelaunchFollower.calendar
                                (Nat.le_of_lt rNext.isLt) u) (historyNext u)) =
                          (List.ofFn (fun u : Fin r.val => u)).filterMap
                              (fun u => ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i
                                x.row a
                                (ReferencePrelaunchFollower.calendar
                                  (Nat.le_of_lt r.isLt) u) (history u)) ++
                            (ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a r own).toList
                      rw [List.ofFn_succ_last, List.filterMap_append]
                      have hfilter :
                          (List.ofFn (fun u : Fin r.val => u.castSucc)).filterMap
                              (fun t : Fin (r.val + 1) => ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i
                                x.row a
                                (ReferencePrelaunchFollower.calendar
                                  (Nat.le_of_lt rNext.isLt) t)
                                (historyNext t)) =
                            (List.ofFn (fun u : Fin r.val => u)).filterMap
                              (fun u => ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i
                                x.row a
                                (ReferencePrelaunchFollower.calendar
                                  (Nat.le_of_lt r.isLt) u) (history u)) := by
                        have hOfFn :
                            List.ofFn (fun u : Fin r.val => u.castSucc) =
                              (List.ofFn (fun u : Fin r.val => u)).map Fin.castSucc := by
                          rw [List.map_ofFn]
                          rfl
                        rw [hOfFn, List.filterMap_map]
                        apply List.filterMap_congr
                        intro u hu
                        change ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a
                          (ReferencePrelaunchFollower.calendar
                            (Nat.le_of_lt rNext.isLt) u.castSucc)
                          (historyNext u.castSucc) =
                          ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a
                            (ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) u)
                            (history u)
                        have hcal :
                            ReferencePrelaunchFollower.calendar
                              (Nat.le_of_lt rNext.isLt) u.castSucc =
                            ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) u := by
                          apply Fin.ext
                          rfl
                        rw [hcal, congrFun hshort u]
                      rw [hfilter]
                      simp only [List.filterMap_cons, List.filterMap_nil]
                      have hcalendarLast :
                          ReferencePrelaunchFollower.calendar (Nat.le_of_lt rNext.isLt)
                            (Fin.last r.val) = r := by
                        apply Fin.ext
                        rfl
                      rw [hcalendarLast, hlast]
                      cases htest :
                          ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a r own <;>
                        simp [htest, Option.toList]
                    exact htestAppend
                | inr nextInactive =>
                    simp only [hpref, hnext]
                    let x := sourceReferenceInput rate rewards C_star C_h z
                    let follower := ActualReferenceInitializationBlock.refFollower i
                    let b := active.val.1.val
                    let bNext := nextInactive.val.1.val
                    let a := active.val.2.1
                    rcases active.property with ⟨_, hactivation, _, _⟩
                    have hboundary : bNext = b := by
                      calc
                        bNext = ReferenceInitializationRun.run x
                            (roundBlockIndex p rNext).val :=
                          nextInactive.val.1.property.2.2
                        _ = ReferenceInitializationRun.run x (roundBlockIndex p r).val := by
                          rw [hsame]
                        _ = b := active.val.1.property.2.2.symm
                    have hbad : some a = none := by
                      calc
                        some a = b.activation follower := hactivation.symm
                        _ = bNext.activation follower := by rw [← hboundary]
                        _ = none := nextInactive.property.2.1
                    exact False.elim (by cases hbad)
            | inr nextStopped =>
                simp only [hpref, hnext]
                let x := sourceReferenceInput rate rewards C_star C_h z
                let b := active.val.1.val
                let bNext := nextStopped.val.1
                have hboundary : bNext = b := by
                  calc
                    bNext = ReferenceInitializationRun.run x
                        (roundBlockIndex p rNext).val := nextStopped.property.2.1
                    _ = ReferenceInitializationRun.run x (roundBlockIndex p r).val := by
                      rw [hsame]
                    _ = b := active.val.1.property.2.2.symm
                have hcross : b.crossing = none := active.val.1.property.2.1
                have hcrossSome : b.crossing.isSome = true := by
                  rw [← hboundary]
                  cases hcross : nextStopped.val.1.crossing with
                  | none => exact False.elim (nextStopped.property.1 hcross)
                  | some _ => rfl
                exact False.elim (by simp [hcross] at hcrossSome)
        | inr _ => simp [hpref]
    | inr _ => simp [hpref]

/-- At an actual generated processed boundary, the next run value is either
the same crossing boundary, or the genuine `finishBlock` result. The input is
constructed from the original whole rewards and private streams; no boundary
or no-crossing condition is supplied by the caller. -/
theorem source_prelaunch_down_boundary_successor
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (s : Fin (n_boot p)) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let b := ReferenceInitializationRun.run x s.val
    (b.crossing = none ∧ ∃ h : b.completed < n_boot p,
        ReferenceInitializationRun.run x (s.val + 1) =
          ReferenceInitializationRun.finishBlock x b h) ∨
      (b.crossing ≠ none ∧ ReferenceInitializationRun.run x (s.val + 1) = b) := by
  classical
  dsimp only
  let x := sourceReferenceInput rate rewards C_star C_h z
  let b := ReferenceInitializationRun.run x s.val
  by_cases hcross : b.crossing = none
  · have hcompleted : b.completed = s.val := by
      change (ReferenceInitializationRun.run
        (GeneratedBootstrapRoundLaw.input p x.ids x.rewards x.C_star x.C_h x.eta
          (x.row, x.coordinates)) s.val).completed = s.val
      exact GeneratedBootstrapRoundLaw.processed_completed x.ids x.rewards
        x.C_star x.C_h x.eta s (x.row, x.coordinates) hcross
    have hremain : b.completed < n_boot p := by
      rw [hcompleted]
      exact s.isLt
    left
    refine ⟨hcross, hremain, ?_⟩
    rw [ReferenceInitializationRun.run_succ,
      ReferenceInitializationRun.advance_of_no_crossing x b hcross hremain]
  · have hcrossSome : b.crossing.isSome = true := by
      cases hc : b.crossing with
      | none => exact False.elim (hcross hc)
      | some c => rfl
    right
    refine ⟨hcross, ?_⟩
    rw [ReferenceInitializationRun.run_succ,
      ReferenceInitializationRun.advance_of_crossing x b hcrossSome]

/-- Within one calendar block, a genuinely inactive generated prefix stays
inactive at the next round. Its real activation selector remains absent, and
both chronological test lists are empty. -/
theorem source_prelaunch_down_same_block_inactive_transport
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hnext : r.val + 1 < p.T) :
    let rNext : Fin p.T := ⟨r.val + 1, hnext⟩
    roundBlockIndex p rNext = roundBlockIndex p r →
      match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
      | .inl (.inr inactive) =>
          match source_prelaunch_down_prefix rate rewards C_star C_h z i rNext with
          | .inl (.inr nextInactive) =>
              nextInactive.val.1.val = inactive.val.1.val ∧
                nextInactive.val.1.val.activation
                    (ActualReferenceInitializationBlock.refFollower i) = none ∧
                source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r = [] ∧
                source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rNext = [] ∧
                source_prelaunch_down_current_test rate rewards C_star C_h z i r = none
          | _ => False
      | _ => True := by
  classical
  dsimp only
  intro hsame
  let rNext : Fin p.T := ⟨r.val + 1, hnext⟩
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl _ => trivial
      | inr inactive =>
          cases hnextPrefix : source_prelaunch_down_prefix rate rewards C_star C_h z i rNext with
          | inl nextBranch =>
              cases nextBranch with
              | inl nextActive =>
                  have hboundary : nextActive.val.1.val = inactive.val.1.val := by
                    calc
                      nextActive.val.1.val = ReferenceInitializationRun.run
                          (sourceReferenceInput rate rewards C_star C_h z)
                          (roundBlockIndex p rNext).val :=
                        nextActive.val.1.property.2.2
                      _ = ReferenceInitializationRun.run
                          (sourceReferenceInput rate rewards C_star C_h z)
                          (roundBlockIndex p r).val := by rw [hsame]
                      _ = inactive.val.1.val := inactive.val.1.property.2.2.symm
                  have hnone : none = some nextActive.val.2.1 := by
                    calc
                      none = inactive.val.1.val.activation
                          (ActualReferenceInitializationBlock.refFollower i) :=
                        inactive.property.2.1.symm
                      _ = nextActive.val.1.val.activation
                          (ActualReferenceInitializationBlock.refFollower i) := by
                        rw [hboundary]
                      _ = some nextActive.val.2.1 := nextActive.property.2.1
                  cases hnone
              | inr nextInactive =>
                  simp only [hpref, hnextPrefix]
                  have hnextPrefix' :
                      source_prelaunch_down_prefix rate rewards C_star C_h z i
                        (⟨r.val + 1, hnext⟩ : Fin p.T) = .inl (.inr nextInactive) := by
                    simpa only [rNext] using hnextPrefix
                  have hboundary : nextInactive.val.1.val = inactive.val.1.val := by
                    calc
                      nextInactive.val.1.val = ReferenceInitializationRun.run
                          (sourceReferenceInput rate rewards C_star C_h z)
                          (roundBlockIndex p rNext).val :=
                        nextInactive.val.1.property.2.2
                      _ = ReferenceInitializationRun.run
                          (sourceReferenceInput rate rewards C_star C_h z)
                          (roundBlockIndex p r).val := by rw [hsame]
                      _ = inactive.val.1.val := inactive.val.1.property.2.2.symm
                  refine ⟨hboundary, nextInactive.property.2.1, ?_, ?_, ?_⟩
                  · simp [rNext, source_prelaunch_down_prefix_tests, hpref]
                  · simp [source_prelaunch_down_prefix_tests, hnextPrefix']
                  · simp [source_prelaunch_down_current_test, hpref]
          | inr nextStopped =>
              have hboundary : nextStopped.val.1 = inactive.val.1.val := by
                calc
                  nextStopped.val.1 = ReferenceInitializationRun.run
                      (sourceReferenceInput rate rewards C_star C_h z)
                      (roundBlockIndex p rNext).val := nextStopped.property.2.1
                  _ = ReferenceInitializationRun.run
                      (sourceReferenceInput rate rewards C_star C_h z)
                      (roundBlockIndex p r).val := by rw [hsame]
                  _ = inactive.val.1.val := inactive.val.1.property.2.2.symm
              exact False.elim (nextStopped.property.1
                (by rw [hboundary]; exact inactive.val.1.property.2.1))
  | inr _ => trivial

/-- A stopped generated prefix remains the same stopped boundary throughout
one calendar block. Its boundary census is constant, and no current physical
test is introduced. -/
theorem source_prelaunch_down_same_block_stopped_transport
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hnext : r.val + 1 < p.T) :
    let rNext : Fin p.T := ⟨r.val + 1, hnext⟩
    roundBlockIndex p rNext = roundBlockIndex p r →
      match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
      | .inr stopped =>
          match source_prelaunch_down_prefix rate rewards C_star C_h z i rNext with
          | .inr nextStopped =>
              nextStopped.val.1 = stopped.val.1 ∧
                source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r =
                  source_prelaunch_down_prefix_tests rate rewards C_star C_h z i rNext ∧
                source_prelaunch_down_current_test rate rewards C_star C_h z i r = none
          | _ => False
      | _ => True := by
  classical
  dsimp only
  intro hsame
  let rNext : Fin p.T := ⟨r.val + 1, hnext⟩
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl _ => trivial
  | inr stopped =>
      cases hnextPrefix : source_prelaunch_down_prefix rate rewards C_star C_h z i rNext with
      | inl nextProcessed =>
          cases nextProcessed with
          | inl nextActive =>
              have hboundary : nextActive.val.1.val = stopped.val.1 := by
                calc
                  nextActive.val.1.val = ReferenceInitializationRun.run
                      (sourceReferenceInput rate rewards C_star C_h z)
                      (roundBlockIndex p rNext).val := nextActive.val.1.property.2.2
                  _ = ReferenceInitializationRun.run
                      (sourceReferenceInput rate rewards C_star C_h z)
                      (roundBlockIndex p r).val := by rw [hsame]
                  _ = stopped.val.1 := stopped.property.2.1.symm
              have hcrossnone : stopped.val.1.crossing = none := by
                simpa only [hboundary] using nextActive.val.1.property.2.1
              exact False.elim (stopped.property.1 hcrossnone)
          | inr nextInactive =>
              have hboundary : nextInactive.val.1.val = stopped.val.1 := by
                calc
                  nextInactive.val.1.val = ReferenceInitializationRun.run
                      (sourceReferenceInput rate rewards C_star C_h z)
                      (roundBlockIndex p rNext).val := nextInactive.val.1.property.2.2
                  _ = ReferenceInitializationRun.run
                      (sourceReferenceInput rate rewards C_star C_h z)
                      (roundBlockIndex p r).val := by rw [hsame]
                  _ = stopped.val.1 := stopped.property.2.1.symm
              have hcrossnone : stopped.val.1.crossing = none := by
                simpa only [hboundary] using nextInactive.val.1.property.2.1
              exact False.elim (stopped.property.1 hcrossnone)
      | inr nextStopped =>
          simp only [hpref, hnextPrefix]
          have hnextPrefix' :
              source_prelaunch_down_prefix rate rewards C_star C_h z i
                (⟨r.val + 1, hnext⟩ : Fin p.T) = .inr nextStopped := by
            simpa only [rNext] using hnextPrefix
          have hboundary : nextStopped.val.1 = stopped.val.1 := by
            calc
              nextStopped.val.1 = ReferenceInitializationRun.run
                  (sourceReferenceInput rate rewards C_star C_h z)
                  (roundBlockIndex p rNext).val := nextStopped.property.2.1
              _ = ReferenceInitializationRun.run
                  (sourceReferenceInput rate rewards C_star C_h z)
                  (roundBlockIndex p r).val := by rw [hsame]
              _ = stopped.val.1 := stopped.property.2.1.symm
          refine ⟨hboundary, ?_, ?_⟩
          · simp only [source_prelaunch_down_prefix_tests, hpref, hnextPrefix']
            rw [hboundary]
          · simp [source_prelaunch_down_current_test, hpref]

/-- The terminal projection is the actual output boundary and ordinary state.
That boundary is stopped either by the recorded crossing or by exhaustion of
the initialization blocks; no physical round index is introduced at `T`. -/
theorem source_prelaunch_down_terminal_boundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let terminal := source_prelaunch_down_terminal rate rewards C_star C_h z i
    terminal.1 = ReferenceInitializationRun.output x ∧
      terminal.2 = ReferenceInitializationRun.ordinary x terminal.1
        (ActualReferenceInitializationBlock.refFollower i) ∧
      ReferenceInitializationRun.advance x terminal.1 = terminal.1 ∧
      ((terminal.1.crossing.isSome = true) ∨ n_boot p ≤ terminal.1.completed) := by
  dsimp only
  let x := sourceReferenceInput rate rewards C_star C_h z
  let terminal := source_prelaunch_down_terminal rate rewards C_star C_h z i
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact ReferenceInitializationRun.output_stopped x
  · rcases ReferenceInitializationRun.run_progress x (n_boot p) le_rfl with hcross | hexhausted
    · exact Or.inl hcross
    · right
      change n_boot p ≤ (ReferenceInitializationRun.output x).completed
      change n_boot p ≤ (ReferenceInitializationRun.run x (n_boot p)).completed
      exact Nat.le_of_eq hexhausted.symm

end Bandits.Support.ReferenceGeneratedPrelaunchDownPrefixTransport

end
