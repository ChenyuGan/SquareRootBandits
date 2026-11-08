/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownPrefixTransport

import Lean.Elab.Tactic.Omega

/-!
# Actual active prelaunch DOWN bank and candidate-flag step

Sources: `05_binary_transport.tex:20-42`, `07_public_setup.tex:127-142`, and
`appendix_a_local_protocol.tex:111-138`.

This result refines one actual active branch of the generated strict prefix.
The bank, current test, local registers, and candidate flags are read from the
existing source construction and follower step. It does not characterize a
later prefix or a historical birth.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownCohortStep

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceGeneratedPrelaunchDownPrefix
open Bandits.Support.ReferenceGeneratedPrelaunchDownPrefixTransport
open Bandits.Support.ReferenceGeneratedPrelaunchDownCohort
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.AffineChannelLaw
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

private theorem completed_flatten_length
    {α : Type} (quota : ℕ) (batches : List (List α))
    (hbatch : ∀ batch ∈ batches, batch.length = quota) :
    batches.flatten.length = quota * batches.length := by
  induction batches with
  | nil => simp
  | cons batch batches ih =>
      have hhead : batch.length = quota := hbatch batch (by simp)
      have htail : ∀ c ∈ batches, c.length = quota := by
        intro c hc
        exact hbatch c (List.mem_cons_of_mem _ hc)
      have hrest := ih htail
      rw [List.flatten_cons, List.length_append, hhead, hrest,
        List.length_cons, Nat.mul_succ]
      omega

/-- The actual active update gives the local bank ordinal, birth, decoder
output, full candidate flags, and pending-cohort flags. Every hypothesis used
by the branch is obtained from the actual prefix census and `F.step`. -/
theorem source_prelaunch_down_active_step_census
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
        let next := (ReferencePrelaunchFollower.step i x.row a r own state).downBatch
        let decoded := ReferencePrelaunchFollower.decodeAt i x.row a r own bank
        let current := source_prelaunch_down_current_test rate rewards C_star C_h z i r
        let tests := source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r
        state.status = .unoccupied ∧
          bank.pending.length < AffineBatchDecoder.quota p ∧
          (∀ batch ∈ bank.completed, batch.length = AffineBatchDecoder.quota p) ∧
          bank.pending = (tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry).drop
            (AffineBatchDecoder.quota p * bank.completed.length) ∧
          next = decoded.1 ∧
          (ReferencePrelaunchFollower.step i x.row a r own state).buffer =
            state.buffer ++ ReferencePrelaunchFollower.logAt i x.row a r own ∧
          (ReferencePrelaunchFollower.step i x.row a r own state).initializationFailure =
            (state.initializationFailure || decide
              (ReferencePrelaunchFollower.passing_at rate.eta i x.row a r own bank)) ∧
          current = (if AffineBatchDecoder.eligible (tr r) then
            some ⟨r, (tr r).sample, none⟩ else none) ∧
          current.toList.map ReferenceGeneratedPrelaunchDownCohort.testEntry =
            AffineBatchDecoder.positiveAt p tr r ∧
          (¬ AffineBatchDecoder.eligible (tr r) →
            next = bank ∧
            next.completed.length = bank.completed.length ∧
            decoded.2 = none ∧
            bankBirth a next = bankBirth a bank) ∧
          (AffineBatchDecoder.eligible (tr r) →
            bank.pending.length + 1 < AffineBatchDecoder.quota p ∨
              bank.pending.length + 1 = AffineBatchDecoder.quota p) ∧
          (AffineBatchDecoder.eligible (tr r) →
            bank.pending.length + 1 < AffineBatchDecoder.quota p →
            next.pending = bank.pending ++ [AffineBatchDecoder.entry p tr r] ∧
              next.completed = bank.completed ∧
              next.completed.length = bank.completed.length ∧
              bankBirth a next = bankBirth a bank ∧ decoded.2 = none) ∧
          (AffineBatchDecoder.eligible (tr r) →
            bank.pending.length + 1 = AffineBatchDecoder.quota p →
            next.pending = [] ∧
              next.completed = bank.completed ++
                [bank.pending ++ [AffineBatchDecoder.entry p tr r]] ∧
              next.completed.length = bank.completed.length + 1 ∧
              bankBirth a next = some (r.val + 1) ∧
              decoded.2 = AffineBatchDecoder.batchOutput
                (bank.pending ++ [AffineBatchDecoder.entry p tr r])) ∧
          ∀ w : AffineChannelLaw.Word (AffineBatchDecoder.width p),
            let flag := fun test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p =>
              (test.sent ≠ some w,
                AffineChannelLaw.affineHash test.sample w = 1)
            let oldFlags := source_prelaunch_down_prefix_flags
              rate rewards C_star C_h z i r w
            let oldCohortFlags := source_prelaunch_down_current_cohort_flags
              rate rewards C_star C_h z i r w
            let appendedFlags := current.toList.map flag
            let nextFlags := (tests ++ current.toList).map flag |>.drop
              (AffineBatchDecoder.quota p * next.completed.length)
            oldCohortFlags = oldFlags.drop
                (AffineBatchDecoder.quota p * bank.completed.length) ∧
              oldCohortFlags.length = bank.pending.length ∧
              oldFlags ++ appendedFlags = (tests ++ current.toList).map flag ∧
              (¬ AffineBatchDecoder.eligible (tr r) → nextFlags = oldCohortFlags) ∧
              (AffineBatchDecoder.eligible (tr r) →
                bank.pending.length + 1 < AffineBatchDecoder.quota p →
                nextFlags = oldCohortFlags ++
                  [((none : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) ≠ some w,
                    AffineChannelLaw.affineHash (tr r).sample w = 1)]) ∧
              (AffineBatchDecoder.eligible (tr r) →
                bank.pending.length + 1 = AffineBatchDecoder.quota p →
                nextFlags = [])
    | _ => True := by
  classical
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          simp only [hpref]
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
          let next := (ReferencePrelaunchFollower.step i x.row a r own state).downBatch
          let decoded := ReferencePrelaunchFollower.decodeAt i x.row a r own bank
          let current := source_prelaunch_down_current_test rate rewards C_star C_h z i r
          let tests := source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r
          have hoperation := source_prelaunch_down_active_operation
            rate rewards C_star C_h z i r
          simp only [hpref] at hoperation
          rcases hoperation with
            ⟨hcurrent, hstatus, _, _, hnextDecode, hbuffer, hfailure⟩
          have htransition := source_prelaunch_down_active_batch_transition
            rate rewards C_star C_h z i r
          simp only [hpref] at htransition
          have hcensus := source_prelaunch_down_prefix_census
            rate rewards C_star C_h z i r
          simp only [hpref] at hcensus
          rcases hcensus with ⟨hmap, hdrop, hcompleted, hshort⟩
          change current = ReferenceGeneratedPrelaunchDownCohort.prelaunchTest
            i x.row a r own at hcurrent
          have hreward : (tr r).roundedReward = own.2.val.val := rfl
          have hsample : (tr r).sample = (x.row.2 r).2 (0, i) := rfl
          have hcondition :
              ((ReferencePrelaunchFollower.downInput i x.row a r own).selected = true ∧
                0 < own.2.val.val) ↔ AffineBatchDecoder.eligible (tr r) := by
            simp [AffineBatchDecoder.eligible, tr,
              ReferencePrelaunchFollower.traceAt,
              ReferencePrelaunchFollower.downInput, hreward]
          have hcurrentShape : current =
              (if AffineBatchDecoder.eligible (tr r) then
                some ⟨r, (tr r).sample, none⟩ else none) := by
            rw [hcurrent]
            unfold ReferenceGeneratedPrelaunchDownCohort.prelaunchTest
            by_cases heligible : AffineBatchDecoder.eligible (tr r)
            · have hyes := hcondition.mpr heligible
              rw [if_pos hyes, if_pos heligible]
              simp [tr, ReferencePrelaunchFollower.traceAt,
                ReferencePrelaunchFollower.downInput, hsample]
            · have hno :
                  ¬((ReferencePrelaunchFollower.downInput i x.row a r own).selected = true ∧
                    0 < own.2.val.val) := fun h => heligible (hcondition.mp h)
              rw [if_neg hno, if_neg heligible]
          have hentryTest : current.toList.map
              ReferenceGeneratedPrelaunchDownCohort.testEntry =
                AffineBatchDecoder.positiveAt p tr r := by
            rw [hcurrentShape]
            by_cases heligible : AffineBatchDecoder.eligible (tr r)
            · simp [heligible, ReferenceGeneratedPrelaunchDownCohort.testEntry,
                AffineBatchDecoder.positiveAt, AffineBatchDecoder.entry]
            · simp [heligible, ReferenceGeneratedPrelaunchDownCohort.testEntry,
                AffineBatchDecoder.positiveAt]
          let extendedWithEntry := bank.pending ++
            [AffineBatchDecoder.entry p tr r]
          have hordinalCases : AffineBatchDecoder.eligible (tr r) →
              bank.pending.length + 1 < AffineBatchDecoder.quota p ∨
                bank.pending.length + 1 = AffineBatchDecoder.quota p := by
            intro heligible
            have hshortBank : bank.pending.length < AffineBatchDecoder.quota p := by
              simpa [bank, state] using hshort
            omega
          refine ⟨hstatus, hshort, hcompleted, hdrop, ?_, hbuffer, hfailure,
            hcurrentShape, hentryTest, ?_, hordinalCases, ?_, ?_, ?_⟩
          · exact hnextDecode
          · intro hgap
            rcases htransition.2.2 hgap with ⟨hbank, hout⟩
            exact ⟨hbank, by simpa [hbank], hout, by simp [hbank]⟩
          · intro heligible hsubquota
            have hpositive : AffineBatchDecoder.positiveAt p tr r =
                [AffineBatchDecoder.entry p tr r] := by
              unfold AffineBatchDecoder.positiveAt
              rw [if_pos heligible]
            have hlen :
                (bank.pending ++ AffineBatchDecoder.positiveAt p tr r).length <
                  AffineBatchDecoder.quota p := by
              rw [hpositive, List.length_append, List.length_singleton]
              exact hsubquota
            rcases htransition.1 heligible hlen with ⟨hbank, hout⟩
            have hnextSub : next =
                (⟨extendedWithEntry, bank.completed⟩ :
                  AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) := by
              simpa [next, decoded, extendedWithEntry, hpositive, x, a, state,
                own, tr, bank] using hbank
            have hbirth : bankBirth a next = bankBirth a bank := by
              simp [bankBirth, hnextSub]
            refine ⟨?_, ?_, ?_, hbirth, hout⟩
            · simpa [extendedWithEntry] using congrArg
                AffineBatchDecoder.State.pending hnextSub
            · simpa using congrArg AffineBatchDecoder.State.completed hnextSub
            · simpa using congrArg
                (fun s : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) =>
                  s.completed.length) hnextSub
          · intro heligible hquota
            have hpositive : AffineBatchDecoder.positiveAt p tr r =
                [AffineBatchDecoder.entry p tr r] := by
              unfold AffineBatchDecoder.positiveAt
              rw [if_pos heligible]
            have hlen : AffineBatchDecoder.quota p ≤
                (bank.pending ++ AffineBatchDecoder.positiveAt p tr r).length := by
              rw [hpositive, List.length_append, List.length_singleton]
              exact Nat.le_of_eq hquota.symm
            rcases htransition.2.1 heligible hlen with ⟨hbank, hout⟩
            have hnextQuota : next =
                (⟨[], bank.completed ++ [extendedWithEntry]⟩ :
                  AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) := by
              simpa [next, decoded, extendedWithEntry, hpositive, x, a, state,
                own, tr, bank] using hbank
            have hbirth : bankBirth a next = some (r.val + 1) := by
              rw [hnextQuota]
              simp [bankBirth, extendedWithEntry, AffineBatchDecoder.entry,
                List.getLast?_append_of_ne_nil]
            have hout' : decoded.2 =
                AffineBatchDecoder.batchOutput extendedWithEntry := by
              simpa [decoded, extendedWithEntry, hpositive, x, a, state,
                own, tr, bank] using hout
            refine ⟨?_, ?_, ?_, hbirth, hout'⟩
            · simpa using congrArg AffineBatchDecoder.State.pending hnextQuota
            · simpa using congrArg AffineBatchDecoder.State.completed hnextQuota
            · have hcompletedNext := congrArg
                AffineBatchDecoder.State.completed hnextQuota
              simpa using congrArg List.length hcompletedNext
          · intro w
            let flag := fun test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p =>
              (test.sent ≠ some w,
                AffineChannelLaw.affineHash test.sample w = 1)
            let oldFlags := source_prelaunch_down_prefix_flags
              rate rewards C_star C_h z i r w
            let oldCohortFlags := source_prelaunch_down_current_cohort_flags
              rate rewards C_star C_h z i r w
            let appendedFlags := current.toList.map flag
            let nextFlags := (tests ++ current.toList).map flag |>.drop
              (AffineBatchDecoder.quota p * next.completed.length)
            have hcohort : oldCohortFlags = oldFlags.drop
                (AffineBatchDecoder.quota p * bank.completed.length) := by
              dsimp only [oldCohortFlags, oldFlags,
                source_prelaunch_down_current_cohort_flags,
                source_prelaunch_down_prefix_flags]
              simp only [hpref]
              rfl
            have hfull : oldFlags ++ appendedFlags =
                (tests ++ current.toList).map flag := by
              change (tests.map flag) ++ current.toList.map flag =
                (tests ++ current.toList).map flag
              rw [List.map_append]
            have hflagsLen : oldFlags.length = tests.length := by
              change (tests.map flag).length = tests.length
              simp only [List.length_map]
            have htestLength : tests.length =
                AffineBatchDecoder.quota p * bank.completed.length + bank.pending.length := by
              calc
                tests.length = (tests.map
                    ReferenceGeneratedPrelaunchDownCohort.testEntry).length := by simp
                _ = (AffineBatchDecoder.collected bank).length := by rw [hmap]
                _ = AffineBatchDecoder.quota p * bank.completed.length + bank.pending.length := by
                  simp only [AffineBatchDecoder.collected, List.length_append]
                  rw [completed_flatten_length (AffineBatchDecoder.quota p)
                    bank.completed hcompleted]
            have hlenFlags : oldFlags.length =
                AffineBatchDecoder.quota p * bank.completed.length + bank.pending.length :=
              hflagsLen.trans htestLength
            have hdropLen : (oldFlags.drop
                (AffineBatchDecoder.quota p * bank.completed.length)).length =
                  bank.pending.length := by
              rw [List.length_drop, hlenFlags]
              exact Nat.add_sub_cancel_left _ _
            have hcohortLength : oldCohortFlags.length = bank.pending.length := by
              rw [hcohort]
              exact hdropLen
            have hoffset : AffineBatchDecoder.quota p * bank.completed.length ≤
                oldFlags.length := by
              rw [hlenFlags]
              exact Nat.le_add_right _ _
            have hdropAppend (tail : List (Prop × Prop)) :
                (oldFlags ++ tail).drop
                  (AffineBatchDecoder.quota p * bank.completed.length) =
                oldFlags.drop (AffineBatchDecoder.quota p * bank.completed.length) ++ tail := by
              rw [List.drop_append_of_le_length hoffset]
            refine ⟨hcohort, hcohortLength, hfull, ?_, ?_, ?_⟩
            · intro hgap
              have hcur : current = none := by
                rw [hcurrentShape, if_neg hgap]
              have hnextBank : next = bank := (htransition.2.2 hgap).1
              have hnextCompleted : next.completed.length = bank.completed.length := by
                simpa [hnextBank]
              have hfullGap : (tests ++ current.toList).map flag = oldFlags := by
                calc
                  (tests ++ current.toList).map flag = oldFlags ++ appendedFlags := hfull.symm
                  _ = oldFlags := by simp [appendedFlags, hcur]
              change ((tests ++ current.toList).map flag).drop
                (AffineBatchDecoder.quota p * next.completed.length) = oldCohortFlags
              rw [hnextCompleted, hfullGap, hcohort]
            · intro heligible hsubquota
              have hcur : current = some ⟨r, (tr r).sample, none⟩ := by
                rw [hcurrentShape, if_pos heligible]
              have hpositive : AffineBatchDecoder.positiveAt p tr r =
                  [AffineBatchDecoder.entry p tr r] := by
                unfold AffineBatchDecoder.positiveAt
                rw [if_pos heligible]
              have hlen :
                  (bank.pending ++ AffineBatchDecoder.positiveAt p tr r).length <
                    AffineBatchDecoder.quota p := by
                rw [hpositive, List.length_append, List.length_singleton]
                exact hsubquota
              rcases htransition.1 heligible hlen with ⟨hbank, _⟩
              have hnextSub : next =
                  (⟨bank.pending ++ [AffineBatchDecoder.entry p tr r], bank.completed⟩ :
                    AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) := by
                simpa [next, decoded, AffineBatchDecoder.positiveAt, heligible] using hbank
              have hnextCompleted : next.completed.length = bank.completed.length := by
                simpa using congrArg
                  (fun s : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) =>
                    s.completed.length) hnextSub
              have hfullSub : (tests ++ current.toList).map flag =
                  oldFlags ++ [flag ⟨r, (tr r).sample, none⟩] := by
                calc
                  (tests ++ current.toList).map flag = oldFlags ++ appendedFlags := hfull.symm
                  _ = oldFlags ++ [flag ⟨r, (tr r).sample, none⟩] := by
                    simp [appendedFlags, hcur]
              change ((tests ++ current.toList).map flag).drop
                (AffineBatchDecoder.quota p * next.completed.length) =
                  oldCohortFlags ++ [flag ⟨r, (tr r).sample, none⟩]
              rw [hnextCompleted, hfullSub, hdropAppend]
              rw [← hcohort]
            · intro heligible hquota
              have hcur : current = some ⟨r, (tr r).sample, none⟩ := by
                rw [hcurrentShape, if_pos heligible]
              have hpositive : AffineBatchDecoder.positiveAt p tr r =
                  [AffineBatchDecoder.entry p tr r] := by
                unfold AffineBatchDecoder.positiveAt
                rw [if_pos heligible]
              have hlen : AffineBatchDecoder.quota p ≤
                  (bank.pending ++ AffineBatchDecoder.positiveAt p tr r).length := by
                rw [hpositive, List.length_append, List.length_singleton]
                exact Nat.le_of_eq hquota.symm
              rcases htransition.2.1 heligible hlen with ⟨hbank, _⟩
              have hnextQuota : next =
                  (⟨[], bank.completed ++
                    [bank.pending ++ [AffineBatchDecoder.entry p tr r]]⟩ :
                    AffineBatchDecoder.State p.T (AffineBatchDecoder.width p)) := by
                simpa [next, decoded, AffineBatchDecoder.positiveAt, heligible,
                  List.append_assoc] using hbank
              have hnextCompleted : next.completed.length = bank.completed.length + 1 := by
                simpa using congrArg
                  (fun s : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) =>
                    s.completed.length) hnextQuota
              have holdPlusOne : oldFlags.length + 1 =
                  AffineBatchDecoder.quota p * (bank.completed.length + 1) := by
                rw [hlenFlags, Nat.mul_succ, Nat.add_assoc, hquota]
              have hfullLength : ((tests ++ current.toList).map flag).length =
                  oldFlags.length + 1 := by
                calc
                  _ = tests.length + current.toList.length := by simp
                  _ = tests.length + 1 := by simp [hcur]
                  _ = oldFlags.length + 1 := by rw [← hflagsLen]
              have hnextLength : ((tests ++ current.toList).map flag).length =
                  AffineBatchDecoder.quota p * next.completed.length := by
                calc
                  _ = oldFlags.length + 1 := hfullLength
                  _ = AffineBatchDecoder.quota p * (bank.completed.length + 1) := holdPlusOne
                  _ = AffineBatchDecoder.quota p * next.completed.length := by
                    rw [hnextCompleted]
              have hdropEmpty := List.drop_eq_nil_of_le
                (show ((tests ++ current.toList).map flag).length ≤
                  AffineBatchDecoder.quota p * next.completed.length by omega)
              change nextFlags = []
              exact hdropEmpty
      | inr _ => simp only [hpref]
  | inr _ => simp only [hpref]

end Bandits.Support.ReferenceGeneratedPrelaunchDownCohortStep
