/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceSourceReleaseWaitingReadouts
public import Bandits.Support.ReferenceGeneratedCompleteCalendarObservation

import Lean.Elab.Tactic.Omega

/-!
# Strict-past locality of the complete reference own history

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,293-345`,
`sources/zip4/manuscript/06_interruptions.tex:376-426,459-490`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The theorem compares the actual initialization history and actual active
physical suffix on the canonical complete source. It uses no common-launch,
ordinary-path, or no-failure condition, and asserts no equality of raw records
whose future source rows differ.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceGeneratedPrefixSuffixInvariance
open Bandits.Support.ReferenceCompletePhysicalHistory
open scoped Classical

namespace Bandits.Support.ReferenceCompleteOwnHistoryPrefixLocality

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

private theorem run_completed_step (x : ReferenceInitializationRun.Input p)
    (r : ℕ) :
    (ReferenceInitializationRun.run x r).completed ≤
      (ReferenceInitializationRun.run x (r + 1)).completed := by
  let b := ReferenceInitializationRun.run x r
  by_cases hc : b.crossing.isSome = true
  · rw [ReferenceInitializationRun.run_succ,
      ReferenceInitializationRun.advance_of_crossing x b hc]
  · have hcross : b.crossing = none := by
      cases h : b.crossing <;> simp_all
    by_cases h : b.completed < BootstrapDimensions.n_boot p
    · rw [ReferenceInitializationRun.run_succ,
        ReferenceInitializationRun.advance_of_no_crossing x b hcross h]
      change (ReferenceInitializationRun.run x r).completed ≤
        (ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x r) h).completed
      rw [(ReferenceInitializationRun.finishBlock_equations x
        (ReferenceInitializationRun.run x r) h).1]
      exact Nat.le_succ _
    · rw [ReferenceInitializationRun.run_succ,
        ReferenceInitializationRun.advance_of_exhausted x b (Nat.le_of_not_gt h)]

private theorem run_completed_mono (x : ReferenceInitializationRun.Input p)
    {q r : ℕ} (hqr : q ≤ r) :
    (ReferenceInitializationRun.run x q).completed ≤
      (ReferenceInitializationRun.run x r).completed := by
  induction r generalizing q with
  | zero =>
      have hq : q = 0 := by omega
      subst q
      exact le_rfl
  | succ r ih =>
      by_cases hq : q ≤ r
      · exact (ih hq).trans (run_completed_step x r)
      · have hq' : q = r + 1 := by omega
        subst q
        exact le_rfl

private def boundaryHistoryEntry (b : ReferenceInitializationRun.Boundary p)
    (player : Fin p.m) (v : ℕ) :
    Option (Fin p.K × ReferencePrelaunchFollower.Observation p) :=
  if h : v < ReferenceInitializationRun.elapsed p b.completed then
    some (b.history player ⟨v, h⟩)
  else none

private theorem run_history_step (x : ReferenceInitializationRun.Input p)
    (r : ℕ) (player : Fin p.m) (v : ℕ)
    (hv : v < ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.run x r).completed) :
    (ReferenceInitializationRun.run x (r + 1)).history player
        ⟨v, Nat.lt_of_lt_of_le hv
          (ReferenceInitializationRun.elapsed_mono p (run_completed_step x r))⟩ =
      (ReferenceInitializationRun.run x r).history player ⟨v, hv⟩ := by
  let b := ReferenceInitializationRun.run x r
  by_cases hc : b.crossing.isSome = true
  · have hrun : ReferenceInitializationRun.run x (r + 1) =
        ReferenceInitializationRun.run x r :=
      (ReferenceInitializationRun.run_succ x r).trans
        (ReferenceInitializationRun.advance_of_crossing x b hc)
    have hlookup := congrArg (fun z => boundaryHistoryEntry z player v) hrun
    have hnew : boundaryHistoryEntry (ReferenceInitializationRun.run x (r + 1)) player v =
        some ((ReferenceInitializationRun.run x (r + 1)).history player
          ⟨v, Nat.lt_of_lt_of_le hv
            (ReferenceInitializationRun.elapsed_mono p (run_completed_step x r))⟩) := by
      simp [boundaryHistoryEntry, Nat.lt_of_lt_of_le hv
        (ReferenceInitializationRun.elapsed_mono p (run_completed_step x r))]
    have hprev : boundaryHistoryEntry (ReferenceInitializationRun.run x r) player v =
        some ((ReferenceInitializationRun.run x r).history player ⟨v, hv⟩) := by
      simp [boundaryHistoryEntry, hv]
    exact Option.some.inj (hnew.symm.trans (hlookup.trans hprev))
  · have hcross : b.crossing = none := by
      cases h : b.crossing <;> simp_all
    by_cases h : b.completed < BootstrapDimensions.n_boot p
    · have hrun : ReferenceInitializationRun.run x (r + 1) =
          ReferenceInitializationRun.finishBlock x b h :=
        (ReferenceInitializationRun.run_succ x r).trans
          (ReferenceInitializationRun.advance_of_no_crossing x b hcross h)
      have hlookup := congrArg (fun z => boundaryHistoryEntry z player v) hrun
      have hnext : boundaryHistoryEntry (ReferenceInitializationRun.run x (r + 1)) player v =
          some ((ReferenceInitializationRun.run x (r + 1)).history player
            ⟨v, Nat.lt_of_lt_of_le hv
              (ReferenceInitializationRun.elapsed_mono p (run_completed_step x r))⟩) := by
        simp [boundaryHistoryEntry, Nat.lt_of_lt_of_le hv
          (ReferenceInitializationRun.elapsed_mono p (run_completed_step x r))]
      have hfinish : boundaryHistoryEntry (ReferenceInitializationRun.finishBlock x b h) player v =
          some (b.history player ⟨v, hv⟩) := by
        have hnew : v < ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.finishBlock x b h).completed := by
          rw [(ReferenceInitializationRun.finishBlock_equations x b h).1]
          exact Nat.lt_of_lt_of_le hv
            (ReferenceInitializationRun.elapsed_mono p (Nat.le_succ b.completed))
        unfold boundaryHistoryEntry
        rw [dite_eq_left hnew]
        apply congrArg some
        rw [(ReferenceInitializationRun.finishBlock_equations x b h).2.1]
        exact ReferenceInitializationRun.extendedHistory_prefix x b h player ⟨v, hv⟩
      exact Option.some.inj
        (hnext.symm.trans (hlookup.trans hfinish))
    · have hrun : ReferenceInitializationRun.run x (r + 1) = b :=
        (ReferenceInitializationRun.run_succ x r).trans
          (ReferenceInitializationRun.advance_of_exhausted x b (Nat.le_of_not_gt h))
      have hlookup := congrArg (fun z => boundaryHistoryEntry z player v) hrun
      have hnext : boundaryHistoryEntry (ReferenceInitializationRun.run x (r + 1)) player v =
          some ((ReferenceInitializationRun.run x (r + 1)).history player
            ⟨v, Nat.lt_of_lt_of_le hv
              (ReferenceInitializationRun.elapsed_mono p (run_completed_step x r))⟩) := by
        simp [boundaryHistoryEntry, Nat.lt_of_lt_of_le hv
          (ReferenceInitializationRun.elapsed_mono p (run_completed_step x r))]
      have hprev : boundaryHistoryEntry (ReferenceInitializationRun.run x r) player v =
          some (b.history player ⟨v, hv⟩) := by simp [boundaryHistoryEntry, b, hv]
      exact Option.some.inj (hnext.symm.trans (hlookup.trans hprev))

private theorem run_history_prefix (x : ReferenceInitializationRun.Input p)
    {q r : ℕ} (hqr : q ≤ r) (player : Fin p.m) (v : ℕ)
    (hv : v < ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.run x q).completed) :
    (ReferenceInitializationRun.run x r).history player
        ⟨v, Nat.lt_of_lt_of_le hv
          (ReferenceInitializationRun.elapsed_mono p
            (run_completed_mono x hqr))⟩ =
      (ReferenceInitializationRun.run x q).history player ⟨v, hv⟩ := by
  induction r generalizing q with
  | zero =>
      have hq : q = 0 := by omega
      subst q
      rfl
  | succ r ih =>
      by_cases hq : q ≤ r
      · have hv' : v < ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.run x r).completed :=
          hv.trans_le (ReferenceInitializationRun.elapsed_mono p
            (run_completed_mono x hq))
        have hstep := run_history_step x r player v hv'
        have hprev := ih (q := q) (hv := hv) hq
        exact hstep.trans hprev
      · have hq' : q = r + 1 := by omega
        subst q
        rfl

-- The actual horizon fold appends records. Its old entries therefore remain
-- available when a short causal comparison is embedded in the complete run.
private theorem foldCalendar_records_take
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin intervalStart count : ℕ) (horigin : origin ≤ intervalStart)
    (hspan : intervalStart + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial origin)
    (acc : ReferenceActivePhysicalHorizon.Run initial) :
    (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards
      origin intervalStart count horigin hspan hmode acc).records.take acc.records.length =
      acc.records := by
  unfold ReferenceActivePhysicalHorizon.foldCalendar
  induction ReferenceActivePhysicalHorizon.calendarEntries origin intervalStart count
      horigin hspan generalizing acc with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      let next := ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards
        origin hmode acc entry
      have hnextLen : acc.records.length ≤ next.records.length := by
        simp [next, ReferenceActivePhysicalHorizon.foldRound]
      have htail := ih next
      calc
        (rest.foldl (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards
          origin hmode) next).records.take acc.records.length =
            ((rest.foldl (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards
              origin hmode) next).records.take next.records.length).take acc.records.length := by
                rw [List.take_take, Nat.min_eq_left hnextLen]
        _ = next.records.take acc.records.length := by rw [htail]
        _ = acc.records := by simp [next, ReferenceActivePhysicalHorizon.foldRound]

private theorem activeRun_records_take
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start pref total : ℕ) (hprefix : pref ≤ total)
    (hspan : start + total ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan hmode).records.take
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start pref
        (by omega) hmode).records.length =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start pref
        (by omega) hmode).records := by
  have hsplit : pref + (total - pref) = total := Nat.add_sub_of_le hprefix
  have happend := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards
    start pref (total - pref) (by omega) hmode
  have hrun : ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
      hspan hmode =
      ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards start
        (start + pref) (total - pref) (by omega) (by omega) hmode
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start pref (by omega) hmode) := by
    simpa [hsplit] using happend
  rw [hrun]
  exact foldCalendar_records_take initial rows selected rewards start (start + pref)
    (total - pref) (by omega) (by omega) hmode
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start pref (by omega) hmode)

private theorem source_initializer_own_entry_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T)
    (v : Fin p.T) (hvt : v.val < t.val)
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hforward : ∀ q : Fin p.T, q.val < t.val →
      ∀ u : Fin (BootstrapDimensions.A_id p),
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u q =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u q)
    (hcontrol : ∀ q : Fin p.T, q.val < t.val →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 q =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 q)
    (boundary : ReferenceInitializationRun.Boundary p)
    (hcompleted : boundary.completed = (BootstrapDimensions.roundBlockIndex p v).val)
    (player : Fin p.m) :
    ReferenceInitializationRun.ownEntry
      (ReferenceInitializationRun.physical
        (ReferenceCompletePhysicalHistory.generatedInput rate source rewards C_star C_h)
        boundary (by rw [hcompleted]; exact (BootstrapDimensions.roundBlockIndex p v).isLt)) player v =
    ReferenceInitializationRun.ownEntry
      (ReferenceInitializationRun.physical
        (ReferenceCompletePhysicalHistory.generatedInput rate source' rewards C_star C_h)
        boundary (by rw [hcompleted]; exact (BootstrapDimensions.roundBlockIndex p v).isLt)) player v := by
  let block := BootstrapDimensions.roundBlockIndex p v
  let x := ReferenceCompletePhysicalHistory.generatedInput rate source rewards C_star C_h
  let y := ReferenceCompletePhysicalHistory.generatedInput rate source' rewards C_star C_h
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source' =
      ActualInitializationPhysicalStep.selectedRowIndex p source := by
    change PrivateSourceStreams.coordinatorIndex p source'.2.1.2 =
      PrivateSourceStreams.coordinatorIndex p source.2.1.2
    exact (congrArg (fun z : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      PrivateSourceStreams.coordinatorIndex p z.1.2) hprivate).symm
  have hcoordinates : x.coordinates = y.coordinates := by
    simp [x, y, ReferenceCompletePhysicalHistory.generatedInput,
      ActualReferenceInitializationBlock.referenceInput, hprivate]
  have hrow : ∀ u : Fin (BootstrapDimensions.A_id p), ∀ q : Fin p.T, q.val < v.val →
      x.row.1 u q = y.row.1 u q := by
    intro u q hq
    change (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u q =
      (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source')).1 u q
    rw [hselected]
    exact hforward q (by omega) u
  have hlearning : ∀ q : Fin p.T, q.val < v.val → x.row.2 q = y.row.2 q := by
    intro q hq
    change (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 q =
      (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source')).2 q
    rw [hselected]
    exact hcontrol q (by omega)
  have hdraw : ∀ j : Fin (p.m - 1),
      x.coordinates.1.1 (ReferenceInitializationRun.nextBlock boundary
        (by rw [hcompleted]; exact block.isLt)) j =
      y.coordinates.1.1 (ReferenceInitializationRun.nextBlock boundary
        (by rw [hcompleted]; exact block.isLt)) j := by
    intro j
    exact congrArg (fun z : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      z.1.1 (ReferenceInitializationRun.nextBlock boundary
        (by rw [hcompleted]; exact block.isLt)) j) hprivate
  have htarget : x.coordinates.2.2 (ReferenceInitializationRun.nextBlock boundary
        (by rw [hcompleted]; exact block.isLt)) =
      y.coordinates.2.2 (ReferenceInitializationRun.nextBlock boundary
        (by rw [hcompleted]; exact block.isLt)) := by
    exact congrArg (fun z : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      z.2.2 (ReferenceInitializationRun.nextBlock boundary
        (by rw [hcompleted]; exact block.isLt))) hprivate
  have hround : ∀ i : Fin p.m, ∀ q : Fin p.T,
      x.coordinates.2.1 (i, q) = y.coordinates.2.1 (i, q) := by
    intro i q
    exact congrArg (fun z : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      z.2.1 (i, q)) hprivate
  have hroundPast : ∀ i : Fin p.m, ∀ q : Fin p.T, q.val < v.val →
      x.coordinates.2.1 (i, q) = y.coordinates.2.1 (i, q) := by
    intro i q _
    exact hround i q
  have hstate := ReferenceInitializationCausality.physical_prechoice_eq_of_actual_past
    x y boundary (by rw [hcompleted]; exact block.isLt) hids rfl hdraw htarget v hrow
    hlearning hroundPast
  let vx := ReferenceInitializationRun.physical x boundary (by rw [hcompleted]; exact block.isLt)
  let vy := ReferenceInitializationRun.physical y boundary (by rw [hcompleted]; exact block.isLt)
  have hprofile : ∀ j : {j // j ∈ ReferenceInitializationRun.uninformed boundary},
      (vx.active j, vx.held j, vx.privateId j) =
        (vy.active j, vy.held j, vy.privateId j) := by
    intro j
    rw [ReferenceInitializationRun.physical_own_block_draw x boundary
      (by rw [hcompleted]; exact block.isLt) j,
      ReferenceInitializationRun.physical_own_block_draw y boundary
        (by rw [hcompleted]; exact block.isLt) j, hcoordinates]
  have hactive : vx.active = vy.active := by
    funext j
    exact congrArg Prod.fst (hprofile j)
  have hheld : vx.held = vy.held := by
    funext j
    exact congrArg (fun z => z.2.1) (hprofile j)
  have hprivateId : vx.privateId = vy.privateId := by
    funext j
    exact congrArg (fun z => z.2.2) (hprofile j)
  have htargetArm : vx.target = vy.target := by
    change BootstrapPhysicalInput.targetArmMap p
        (ReferenceInitializationRun.nextBlock boundary (by rw [hcompleted]; exact block.isLt))
        x.coordinates =
      BootstrapPhysicalInput.targetArmMap p
        (ReferenceInitializationRun.nextBlock boundary (by rw [hcompleted]; exact block.isLt))
        y.coordinates
    rw [hcoordinates]
  let w : BootstrapBlockCausality.LocalCoordinates p (ReferenceInitializationRun.uninformed boundary)
      vx.held vx.target :=
    (y.row, (vy.uniform,
      (fun q => ⟨(vy.coordinatorAvoid q).val, by
          simpa only [htargetArm] using (vy.coordinatorAvoid q).property⟩,
        fun j q => ⟨(vy.followerAvoid j q).val, by
          simpa only [congrFun hheld j] using (vy.followerAvoid j q).property⟩)))
  have hcoords : ∀ q : Fin p.T, q.val ≤ v.val →
      BootstrapBlockCausality.roundCoordinatesEq (ReferenceInitializationRun.uninformed boundary)
        vx.held vx.target (ReferenceInitializationRun.localCoordinates x boundary
          (by rw [hcompleted]; exact block.isLt)) w q := by
    intro q hq
    dsimp only [BootstrapBlockCausality.roundCoordinatesEq,
      ReferenceInitializationRun.localCoordinates, w]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro u
      change (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u q =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source')).1 u q
      rw [hselected]
      exact hforward q (Nat.lt_of_le_of_lt hq hvt) u
    · change (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 q =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source')).2 q
      rw [hselected]
      exact hcontrol q (Nat.lt_of_le_of_lt hq hvt)
    · intro i
      rw [ReferenceInitializationRun.physical_own_uniform x boundary
        (by rw [hcompleted]; exact block.isLt) i q,
        ReferenceInitializationRun.physical_own_uniform y boundary
          (by rw [hcompleted]; exact block.isLt) i q]
      exact congrArg (BootstrapPrivateRoundStreams.fullArmScalarDraw p)
        (hround i q)
    · apply Subtype.ext
      change BootstrapPhysicalInput.coordinatorAvoidArmValueMap p
          (ReferenceInitializationRun.nextBlock boundary
            (by rw [hcompleted]; exact block.isLt)) x.coordinates q =
        BootstrapPhysicalInput.coordinatorAvoidArmValueMap p
          (ReferenceInitializationRun.nextBlock boundary
            (by rw [hcompleted]; exact block.isLt)) y.coordinates q
      rcases BootstrapPhysicalInput.coordinator_roundDraws_eq_of_own_coordinates_eq
          p (ReferenceInitializationRun.nextBlock boundary
            (by rw [hcompleted]; exact block.isLt)) x.coordinates y.coordinates q htarget
          (hround (Bandits.Support.ActiveRoundActions.coordinator p.two_le_m) q)
        with ⟨_, _, havoid⟩
      exact havoid
    · intro j
      apply Subtype.ext
      change BootstrapPhysicalInput.followerAvoidArmValueMap p
          (ReferenceInitializationRun.nextBlock boundary
            (by rw [hcompleted]; exact block.isLt))
          (ReferenceInitializationRun.uninformed boundary) boundary.numerators
          boundary.weight_ge_one x.coordinates j q =
        BootstrapPhysicalInput.followerAvoidArmValueMap p
          (ReferenceInitializationRun.nextBlock boundary
            (by rw [hcompleted]; exact block.isLt))
          (ReferenceInitializationRun.uninformed boundary) boundary.numerators
          boundary.weight_ge_one y.coordinates j q
      have htriple : x.coordinates.1.1
          (ReferenceInitializationRun.nextBlock boundary
            (by rw [hcompleted]; exact block.isLt))
          (BootstrapPhysicalInput.sourceFollowerIndex p j.1) =
        y.coordinates.1.1
          (ReferenceInitializationRun.nextBlock boundary
            (by rw [hcompleted]; exact block.isLt))
          (BootstrapPhysicalInput.sourceFollowerIndex p j.1) :=
        hdraw (BootstrapPhysicalInput.sourceFollowerIndex p j.1)
      rcases BootstrapPhysicalInput.follower_roundDraws_eq_of_own_coordinates_eq
          p (ReferenceInitializationRun.nextBlock boundary
            (by rw [hcompleted]; exact block.isLt))
          (ReferenceInitializationRun.uninformed boundary) boundary.numerators
          boundary.weight_ge_one x.coordinates y.coordinates j q htriple
          (hround (Bandits.Support.PublicDiscreteDraws.followerPlayer p.two_le_m j.1)
            q) with
        ⟨_, havoid⟩
      exact havoid
  -- Pre-choice causality alone does not contain round v's observation. Compare
  -- its actual actions and feedback using the unchanged current coordinates.
  have hcoordV := hcoords v le_rfl
  have hactLocal := BootstrapBlockCausality.actions_eq_of_roundCoordinatesEq
    (s := ReferenceInitializationRun.nextBlock boundary (by rw [hcompleted]; exact block.isLt))
    (ReferenceInitializationRun.uninformed boundary) vx.active vx.held vx.privateId x.ids vx.target
    x.rewards (ReferenceInitializationRun.localCoordinates x boundary
      (by rw [hcompleted]; exact block.isLt)) w (BootstrapPhysicalBlock.run vx v.val) v hcoordV
  have hinputWbase : BootstrapBlockCausality.blockInput
      (s := ReferenceInitializationRun.nextBlock boundary
        (by rw [hcompleted]; exact block.isLt))
      (ReferenceInitializationRun.uninformed boundary) vx.active vx.held vx.privateId
      vx.ids vx.target vx.rewards w = vy := by
    simp only [vy, ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput,
      BootstrapBlockCausality.blockInput, BootstrapBlockCausality.inputOf]
    congr 1
    all_goals try simp [w]
    case e_11 =>
      apply Function.hfunext rfl
      intro q q' hq
      cases hq
      exact (Subtype.heq_iff_coe_eq (by
        intro a
        exact (congrArg (fun z => a ≠ z) htargetArm).to_iff)).2 rfl
    case e_12 =>
      apply Function.hfunext rfl
      intro j j' hj
      cases hj
      apply Function.hfunext rfl
      intro q q' hq
      cases hq
      exact (Subtype.heq_iff_coe_eq (by
        intro a
        exact (congrArg (fun z => a ≠ z) (congrFun hheld j)).to_iff)).2 rfl
  have hinputW : BootstrapBlockCausality.blockInput
      (s := ReferenceInitializationRun.nextBlock boundary
        (by rw [hcompleted]; exact block.isLt))
      (ReferenceInitializationRun.uninformed boundary) vx.active vx.held vx.privateId
      x.ids vx.target x.rewards w = vy := by
    change BootstrapBlockCausality.blockInput
      (s := ReferenceInitializationRun.nextBlock boundary
        (by rw [hcompleted]; exact block.isLt))
      (ReferenceInitializationRun.uninformed boundary) vx.active vx.held vx.privateId
      vx.ids vx.target vx.rewards w = vy
    exact hinputWbase
  have hact : BootstrapPhysicalBlock.actions vx (BootstrapPhysicalBlock.run vx v.val) v player =
      BootstrapPhysicalBlock.actions vy (BootstrapPhysicalBlock.run vy v.val) v player := by
    calc
      _ = BootstrapPhysicalBlock.actions
          (BootstrapBlockCausality.blockInput
            (s := ReferenceInitializationRun.nextBlock boundary (by rw [hcompleted]; exact block.isLt))
            (ReferenceInitializationRun.uninformed boundary) vx.active vx.held vx.privateId x.ids vx.target
            x.rewards (ReferenceInitializationRun.localCoordinates x boundary
              (by rw [hcompleted]; exact block.isLt)))
          (BootstrapPhysicalBlock.run vx v.val) v player := rfl
      _ = BootstrapPhysicalBlock.actions
          (BootstrapBlockCausality.blockInput
            (s := ReferenceInitializationRun.nextBlock boundary (by rw [hcompleted]; exact block.isLt))
            (ReferenceInitializationRun.uninformed boundary) vx.active vx.held vx.privateId x.ids vx.target
            x.rewards w)
          (BootstrapPhysicalBlock.run vx v.val) v player := congrFun hactLocal player
      _ = BootstrapPhysicalBlock.actions vy (BootstrapPhysicalBlock.run vy v.val) v player := by
        rw [hinputW, hstate]
  have hfeedbackLocal := BootstrapBlockCausality.feedback_eq_of_roundCoordinatesEq
    (s := ReferenceInitializationRun.nextBlock boundary (by rw [hcompleted]; exact block.isLt))
    (ReferenceInitializationRun.uninformed boundary) vx.active vx.held vx.privateId x.ids vx.target
    x.rewards (ReferenceInitializationRun.localCoordinates x boundary
      (by rw [hcompleted]; exact block.isLt)) w (BootstrapPhysicalBlock.run vx v.val) v player hcoordV
  have hfeedback : BootstrapPhysicalBlock.feedback vx (BootstrapPhysicalBlock.run vx v.val) v player =
      BootstrapPhysicalBlock.feedback vy (BootstrapPhysicalBlock.run vy v.val) v player := by
    calc
      _ = BootstrapPhysicalBlock.feedback
          (BootstrapBlockCausality.blockInput
            (s := ReferenceInitializationRun.nextBlock boundary (by rw [hcompleted]; exact block.isLt))
            (ReferenceInitializationRun.uninformed boundary) vx.active vx.held vx.privateId x.ids vx.target
            x.rewards (ReferenceInitializationRun.localCoordinates x boundary
              (by rw [hcompleted]; exact block.isLt)))
          (BootstrapPhysicalBlock.run vx v.val) v player := rfl
      _ = BootstrapPhysicalBlock.feedback
          (BootstrapBlockCausality.blockInput
            (s := ReferenceInitializationRun.nextBlock boundary (by rw [hcompleted]; exact block.isLt))
            (ReferenceInitializationRun.uninformed boundary) vx.active vx.held vx.privateId x.ids vx.target
            x.rewards w)
          (BootstrapPhysicalBlock.run vx v.val) v player := hfeedbackLocal
      _ = BootstrapPhysicalBlock.feedback vy (BootstrapPhysicalBlock.run vy v.val) v player := by
        rw [hinputW, hstate]
  unfold ReferenceInitializationRun.ownEntry ReferenceInitializationRun.ownObservation
  exact Prod.ext hact (by
    apply Subtype.ext
    apply Subtype.ext
    exact hfeedback)

private theorem run_completed_at_round_block
    (x : ReferenceInitializationRun.Input p) (v : Fin p.T)
    (hstart : v.val < ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output x).completed) :
    (ReferenceInitializationRun.run x (BootstrapDimensions.roundBlockIndex p v).val).completed =
      (BootstrapDimensions.roundBlockIndex p v).val := by
  let block := BootstrapDimensions.roundBlockIndex p v
  have hmem := BootstrapDimensions.round_mem_quotient_block p v
  have hbounds := (BootstrapDimensions.mem_calendarBlock_iff p block v).mp hmem
  have hblockStart : ReferenceInitializationRun.elapsed p block.val ≤ v.val := by
    change min p.T (block.val * BootstrapDimensions.B_boot p) ≤ v.val
    exact (Nat.min_le_right _ _).trans hbounds.1
  have hnot : (ReferenceInitializationRun.run x block.val).crossing.isSome ≠ true := by
    intro hc
    have hout := ReferenceInitializationRun.output_eq_of_crossing x block.val
      block.isLt.le hc
    have hle := ReferenceInitializationRun.elapsed_mono p
      (ReferenceInitializationPrefixInvariance.run_completed_le x block.val)
    rw [hout] at hstart
    omega
  exact (ReferenceInitializationRun.run_progress x block.val block.isLt.le).resolve_left hnot

private theorem initializer_history_eq_before
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T)
    (v : Fin p.T) (hvt : v.val < t.val)
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hforward : ∀ q : Fin p.T, q.val < t.val →
      ∀ u : Fin (BootstrapDimensions.A_id p),
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u q =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u q)
    (hcontrol : ∀ q : Fin p.T, q.val < t.val →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 q =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 q)
    (hleft : v.val < ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h)
    (hright : v.val < ReferenceCompletePhysicalHistory.physicalStart
      rate source' rewards C_star C_h)
    (player : Fin p.m) :
    ReferenceCompletePhysicalHistory.completeOwnHistory rate source rewards C_star C_h player v =
      ReferenceCompletePhysicalHistory.completeOwnHistory rate source' rewards C_star C_h player v := by
  let block := BootstrapDimensions.roundBlockIndex p v
  let x := ReferenceCompletePhysicalHistory.generatedInput rate source rewards C_star C_h
  let y := ReferenceCompletePhysicalHistory.generatedInput rate source' rewards C_star C_h
  have hstartX : v.val < ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output x).completed := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput, x] using hleft
  have hstartY : v.val < ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output y).completed := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput, y] using hright
  have hmem := BootstrapDimensions.round_mem_quotient_block p v
  have hbounds := (BootstrapDimensions.mem_calendarBlock_iff p block v).mp hmem
  have hstartBlock : ReferenceInitializationRun.elapsed p block.val ≤ v.val := by
    change min p.T (block.val * BootstrapDimensions.B_boot p) ≤ v.val
    exact (Nat.min_le_right _ _).trans hbounds.1
  have hendBlock : v.val < ReferenceInitializationRun.elapsed p (block.val + 1) := by
    change v.val < min p.T ((block.val + 1) * BootstrapDimensions.B_boot p)
    exact hbounds.2
  have hcompleteX := run_completed_at_round_block x v hstartX
  have hcompleteY := run_completed_at_round_block y v hstartY
  have hids' : source.1.1 = source'.1.1 := hids
  have hprivate' : source.2 = source'.2 := hprivate
  have hcommon := ReferenceInitializationOriginLocality.source_run_boundary_eq
    rate rewards C_star C_h source source' block.val hids' hprivate'
    (by
      intro q hq u
      exact hforward q (Nat.lt_trans (Nat.lt_of_lt_of_le hq hstartBlock) hvt) u)
    (by intro q hq; exact hcontrol q (Nat.lt_trans (Nat.lt_of_lt_of_le hq hstartBlock) hvt))
  let boundary := ReferenceInitializationRun.run x block.val
  have hcompleted : boundary.completed = block.val := hcompleteX
  have hboundaryY : ReferenceInitializationRun.run y block.val = boundary := hcommon.symm
  have hcrossX : boundary.crossing = none := by
    have hnot : boundary.crossing.isSome ≠ true := by
      intro hc
      have hout := ReferenceInitializationRun.output_eq_of_crossing x block.val
        block.isLt.le hc
      have hle := ReferenceInitializationRun.elapsed_mono p
        (ReferenceInitializationPrefixInvariance.run_completed_le x block.val)
      rw [hout] at hstartX
      omega
    cases hc : boundary.crossing with
    | none => rfl
    | some c => exact False.elim (hnot (by simp [hc]))
  have hblockBound : boundary.completed < BootstrapDimensions.n_boot p := by
    rw [hcompleted]
    exact block.isLt
  have hfinishX : ReferenceInitializationRun.run x (block.val + 1) =
      ReferenceInitializationRun.finishBlock x boundary hblockBound := by
    rw [ReferenceInitializationRun.run_succ,
      ReferenceInitializationRun.advance_of_no_crossing x boundary hcrossX hblockBound]
  have hcrossY : boundary.crossing = none := hcrossX
  have hfinishY : ReferenceInitializationRun.run y (block.val + 1) =
      ReferenceInitializationRun.finishBlock y boundary hblockBound := by
    rw [ReferenceInitializationRun.run_succ, hboundaryY,
      ReferenceInitializationRun.advance_of_no_crossing y boundary hcrossY hblockBound]
  have hentry := source_initializer_own_entry_eq rate rewards C_star C_h source source'
    t v hvt hids hprivate hforward hcontrol boundary hcompleted player
  obtain ⟨u, hu⟩ := ReferencePrelaunchPhysicalReplay.exists_blockRound p block v hmem
  have hnextBlock : ReferenceInitializationRun.nextBlock boundary hblockBound = block := by
    apply Fin.ext
    exact hcompleted
  let u' : Fin (ReferencePrelaunchPhysicalReplay.blockLength p
      (ReferenceInitializationRun.nextBlock boundary hblockBound)) :=
    Fin.cast (congrArg (ReferencePrelaunchPhysicalReplay.blockLength p) hnextBlock.symm) u
  have hu' : ReferencePrelaunchPhysicalReplay.blockRound p
      (ReferenceInitializationRun.nextBlock boundary hblockBound) u' = v := by
    apply Fin.ext
    have huval := congrArg Fin.val hu
    simpa [u', hnextBlock, ReferencePrelaunchPhysicalReplay.blockRound_val] using huval
  have hcompletedNextX :
      (ReferenceInitializationRun.run x (block.val + 1)).completed = block.val + 1 := by
    calc
      _ = (ReferenceInitializationRun.finishBlock x boundary hblockBound).completed :=
        congrArg ReferenceInitializationRun.Boundary.completed hfinishX
      _ = boundary.completed + 1 := (ReferenceInitializationRun.finishBlock_equations
        x boundary hblockBound).1
      _ = block.val + 1 := by rw [hcompleted]
  have hcompletedNextY :
      (ReferenceInitializationRun.run y (block.val + 1)).completed = block.val + 1 := by
    calc
      _ = (ReferenceInitializationRun.finishBlock y boundary hblockBound).completed :=
        congrArg ReferenceInitializationRun.Boundary.completed hfinishY
      _ = boundary.completed + 1 := (ReferenceInitializationRun.finishBlock_equations
        y boundary hblockBound).1
      _ = block.val + 1 := by rw [hcompleted]
  have hmidX : v.val < ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.run x (block.val + 1)).completed := by
    rw [hcompletedNextX]
    exact hendBlock
  have hmidY : v.val < ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.run y (block.val + 1)).completed := by
    rw [hcompletedNextY]
    exact hendBlock
  have hmidBoundary : v.val < ReferenceInitializationRun.elapsed p (boundary.completed + 1) := by
    rw [hcompleted]
    exact hendBlock
  have hindexBlock :
      (⟨v.val, hmidBoundary⟩ : Fin
        (ReferenceInitializationRun.elapsed p (boundary.completed + 1))) =
      ReferencePrelaunchPhysicalReplay.blockEmbed u' := by
    apply Fin.ext
    simp only [ReferencePrelaunchPhysicalReplay.blockEmbed]
    rw [← ReferencePrelaunchPhysicalReplay.blockRound_val]
    exact (congrArg Fin.val hu').symm
  have hcurX : (ReferenceInitializationRun.run x (block.val + 1)).history player
      ⟨v.val, hmidX⟩ = ReferenceInitializationRun.ownEntry
        (ReferenceInitializationRun.physical x boundary hblockBound) player v := by
    have hfinishEntry : boundaryHistoryEntry
        (ReferenceInitializationRun.finishBlock x boundary hblockBound) player v =
        some (ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical x boundary hblockBound) player v) := by
      have hcond : v.val < ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.finishBlock x boundary hblockBound).completed := by
        rw [(ReferenceInitializationRun.finishBlock_equations x boundary hblockBound).1]
        exact hmidBoundary
      unfold boundaryHistoryEntry
      rw [dite_eq_left hcond]
      apply congrArg some
      rw [(ReferenceInitializationRun.finishBlock_equations x boundary hblockBound).2.1]
      have hindexFinish :
          (⟨v.val, hcond⟩ : Fin (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.finishBlock x boundary hblockBound).completed)) =
          ReferencePrelaunchPhysicalReplay.blockEmbed u' := by
        change (⟨v.val, hcond⟩ : Fin
          (ReferenceInitializationRun.elapsed p (boundary.completed + 1))) =
          ReferencePrelaunchPhysicalReplay.blockEmbed u'
        apply Fin.ext
        simp only [ReferencePrelaunchPhysicalReplay.blockEmbed]
        rw [← ReferencePrelaunchPhysicalReplay.blockRound_val]
        exact (congrArg Fin.val hu').symm
      rw [hindexFinish, ReferenceInitializationRun.extendedHistory_block, hu']
    have hrunEntry : boundaryHistoryEntry
        (ReferenceInitializationRun.run x (block.val + 1)) player v =
        some ((ReferenceInitializationRun.run x (block.val + 1)).history player
          ⟨v.val, hmidX⟩) := by
      simp [boundaryHistoryEntry, hmidX]
    have hlookup := congrArg (fun b => boundaryHistoryEntry b player v) hfinishX
    exact Option.some.inj (hrunEntry.symm.trans (hlookup.trans hfinishEntry))
  have hcurY : (ReferenceInitializationRun.run y (block.val + 1)).history player
      ⟨v.val, hmidY⟩ = ReferenceInitializationRun.ownEntry
        (ReferenceInitializationRun.physical y boundary hblockBound) player v := by
    have hfinishEntry : boundaryHistoryEntry
        (ReferenceInitializationRun.finishBlock y boundary hblockBound) player v =
        some (ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical y boundary hblockBound) player v) := by
      have hcond : v.val < ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.finishBlock y boundary hblockBound).completed := by
        rw [(ReferenceInitializationRun.finishBlock_equations y boundary hblockBound).1]
        exact hmidBoundary
      unfold boundaryHistoryEntry
      rw [dite_eq_left hcond]
      apply congrArg some
      rw [(ReferenceInitializationRun.finishBlock_equations y boundary hblockBound).2.1]
      have hindexFinish :
          (⟨v.val, hcond⟩ : Fin (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.finishBlock y boundary hblockBound).completed)) =
          ReferencePrelaunchPhysicalReplay.blockEmbed u' := by
        change (⟨v.val, hcond⟩ : Fin
          (ReferenceInitializationRun.elapsed p (boundary.completed + 1))) =
          ReferencePrelaunchPhysicalReplay.blockEmbed u'
        apply Fin.ext
        simp only [ReferencePrelaunchPhysicalReplay.blockEmbed]
        rw [← ReferencePrelaunchPhysicalReplay.blockRound_val]
        exact (congrArg Fin.val hu').symm
      rw [hindexFinish, ReferenceInitializationRun.extendedHistory_block, hu']
    have hrunEntry : boundaryHistoryEntry
        (ReferenceInitializationRun.run y (block.val + 1)) player v =
        some ((ReferenceInitializationRun.run y (block.val + 1)).history player
          ⟨v.val, hmidY⟩) := by
      simp [boundaryHistoryEntry, hmidY]
    have hlookup := congrArg (fun b => boundaryHistoryEntry b player v) hfinishY
    exact Option.some.inj (hrunEntry.symm.trans (hlookup.trans hfinishEntry))
  have hprefixX := run_history_prefix (x := x) (q := block.val + 1) (r := BootstrapDimensions.n_boot p)
    (by omega) player v.val hmidX
  have hprefixY := run_history_prefix (x := y) (q := block.val + 1) (r := BootstrapDimensions.n_boot p)
    (by omega) player v.val hmidY
  have hboundary :
      (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).history
          player ⟨v.val, by simpa [ReferenceCompletePhysicalHistory.physicalStart,
            ReferenceCompletePhysicalHistory.generatedBoundary,
            ReferenceCompletePhysicalHistory.generatedInput] using hleft⟩ =
      (ReferenceCompletePhysicalHistory.generatedBoundary rate source' rewards C_star C_h).history
          player ⟨v.val, by simpa [ReferenceCompletePhysicalHistory.physicalStart,
            ReferenceCompletePhysicalHistory.generatedBoundary,
            ReferenceCompletePhysicalHistory.generatedInput] using hright⟩ := by
    simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput, ReferenceInitializationRun.output, x, y] using
      hprefixX.trans (hcurX.trans (hentry.trans (hcurY.symm.trans hprefixY.symm)))
  rw [ReferenceCompletePhysicalHistory.completeOwnHistory_prefix rate source rewards C_star C_h
      player v hleft]
  rw [ReferenceCompletePhysicalHistory.completeOwnHistory_prefix rate source' rewards C_star C_h
      player v hright]
  exact hboundary

private theorem source_active_own_entry_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (v : Fin p.T) (hvt : v.val < t.val)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
      some active)
    (s : ℕ) (hs : s ≤ t.val) (hsv : s ≤ v.val)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s)
    (player : Fin p.m) :
    ReferenceCompletePhysicalHistory.completeOwnHistory rate source rewards C_star C_h player v =
    ReferenceCompletePhysicalHistory.completeOwnHistory rate
      (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix source t suffix)
      rewards C_star C_h player v := by
  let source' := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix source t suffix
  let q := ActualInitializationPhysicalStep.selectedRowIndex p source
  let control0 := (source.1.2 q).2 t
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q := rfl
  have hcross : (ReferenceInitializationRun.output
      (ReferenceCompletePhysicalHistory.generatedInput rate source rewards C_star C_h)).crossing.isSome = true := by
    have hsome := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
    simpa [ReferenceCompletePhysicalHistory.generatedInput] using hsome
  have hElapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ReferenceCompletePhysicalHistory.generatedInput rate source rewards C_star C_h)).completed = s := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hstart
  let x : ReferenceRetainedAssignmentReleaseHistory.RetainedLaunchStartInput
      (p := p) rate rewards C_star C_h q t s hs control0 :=
    ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 source hselected hcross hElapsed
  have hS := ReferenceGeneratedPrefixSuffixInvariance.retainedGeneratedPrefix_suffix_invariant
    rewards C_star C_h q t s hs control0 x
    suffix
  obtain ⟨x', hxval, hseed, hprefix⟩ := hS
  have hselected' : ActualInitializationPhysicalStep.selectedRowIndex p source' = q := by
    rw [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_selected, hselected]
  have hcross' : (ReferenceInitializationRun.output
      (ReferenceCompletePhysicalHistory.generatedInput rate source' rewards C_star C_h)).crossing.isSome = true := by
    have hpres := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_preserves_actual_launch
      rewards C_star C_h q t s hs source hselected suffix hcross hElapsed
    rcases hpres with ⟨_, hcross', _, _⟩
    simpa [ReferenceCompletePhysicalHistory.generatedInput, source'] using hcross'
  have hElapsed' : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ReferenceCompletePhysicalHistory.generatedInput rate source' rewards C_star C_h)).completed = s := by
    have hpres := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_preserves_actual_launch
      rewards C_star C_h q t s hs source hselected suffix hcross hElapsed
    rcases hpres with ⟨_, _, hElapsed', _⟩
    simpa [ReferenceCompletePhysicalHistory.generatedInput, source'] using hElapsed'
  have hlaunch' : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source' rewards C_star C_h =
      some active := by
    have hpres := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_preserves_actual_launch
      rewards C_star C_h q t s hs source hselected suffix hcross hElapsed
    rcases hpres with ⟨_, _, _, hlaunchEq⟩
    exact hlaunchEq.symm.trans hlaunch
  have hstart' : ReferenceCompletePhysicalHistory.physicalStart rate source' rewards C_star C_h = s := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hElapsed'
  have hsplit : ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source =
      (control0, x.val) := by
    apply Prod.ext
    · exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control p q t source
    · exact ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_val
        rate rewards C_star C_h q t s hs control0 source hselected hcross hElapsed
  have hsource : ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val = source := by
    dsimp [ReferenceGeneratedActivePrefixFactor.splitSource]
    rw [← hsplit]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_reconstruct p q t source
  have hsplit' : ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source' =
      (suffix t, x'.val) := by
    apply Prod.ext
    · calc
        _ = (source'.1.2 q).2 t :=
          ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control p q t source'
        _ = suffix t := by
          change ((ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
            source t suffix).1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source')).2 t = suffix t
          rw [hselected']
          exact ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_from
            source t t suffix (by omega)
    · have hreconstruct :
          ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
              (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val) t suffix =
            ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix source t suffix :=
          congrArg (fun z =>
            ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t suffix) hsource
      change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
        (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix source t suffix)).2 = x'.val
      rw [← hreconstruct]
      exact hxval.symm
  have hsource' : ReferenceGeneratedActivePrefixFactor.splitSource q t
        (suffix t) x'.val = source' := by
    dsimp [ReferenceGeneratedActivePrefixFactor.splitSource]
    rw [← hsplit']
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_reconstruct p q t source'
  have hxparts : x.val ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∧
      x.val ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control0 := by
    change x.val ∈ ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
      rate rewards C_star C_h q t s control0
    change x.val ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∩
      ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control0
    exact x.property
  have hx'parts : x'.val ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∧
      x'.val ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s (suffix t) := by
    change x'.val ∈ ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
      rate rewards C_star C_h q t s (suffix t)
    change x'.val ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∩
      ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s (suffix t)
    exact x'.property
  let activeL := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
    q t control0 x.val hxparts.1 s hs hxparts.2
  let activeR := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
    q t (suffix t) x'.val hx'parts.1 s hs hx'parts.2
  have hspecL := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards
    C_star C_h q t control0 x.val hxparts.1 s hs hxparts.2
  have hspecR := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards
    C_star C_h q t (suffix t) x'.val hx'parts.1 s hs hx'parts.2
  have hlaunchL : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
      some activeL := by
    simpa [activeL, hsource] using hspecL.1
  have hlaunchR : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source' rewards C_star C_h =
      some activeR := by
    simpa [activeR, hsource'] using hspecR.1
  have hactiveL : active = activeL := Option.some.inj (hlaunch.symm.trans hlaunchL)
  have hactiveR : active = activeR := Option.some.inj (hlaunch'.symm.trans hlaunchR)
  have hactive : activeL = activeR := by
    calc
      activeL = active := hactiveL.symm
      _ = activeR := hactiveR
  have hmodeL : ReferenceActivePhysicalHorizon.allActiveAtStart active s := by
    exact hactiveL.symm ▸ hspecL.2.1
  have hmodeR : ReferenceActivePhysicalHorizon.allActiveAtStart active s := by
    exact hactiveR.symm ▸ hspecR.2.1
  have hcount : s + (v.val - s + 1) ≤ t.val := by omega
  let count := v.val - s + 1
  let prefixIndex : Fin (t.val - s + 1) := ⟨count, by omega⟩
  have hprefixEv := hprefix prefixIndex
  have hspanCount : s + count ≤ p.T := by omega
  have hspanTotal : s + (p.T - s) ≤ p.T := by omega
  have hleftPrefix :
      (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor rate rewards C_star C_h
        q t control0 x.val hxparts.1 s count hs hxparts.2 hcount).records.map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      (ReferenceActivePhysicalHorizon.run activeL source.1.2 q rewards s count hspanCount
        hspecL.2.1).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
    change (ReferenceActivePhysicalHorizon.run activeL
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val).1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val))
        rewards s count (by omega) hspecL.2.1).records.map _ = _
    simp only [hsource, hselected]
  have hrightPrefix :
      (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor rate rewards C_star C_h
        q t (suffix t) x'.val hx'parts.1 s count hs hx'parts.2 hcount).records.map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      (ReferenceActivePhysicalHorizon.run activeR source'.1.2 q rewards s count hspanCount
        hspecR.2.1).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
    change (ReferenceActivePhysicalHorizon.run activeR
        (ReferenceGeneratedActivePrefixFactor.splitSource q t (suffix t) x'.val).1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceGeneratedActivePrefixFactor.splitSource q t (suffix t) x'.val))
        rewards s count (by omega) hspecR.2.1).records.map _ = _
    simp only [hsource', hselected']
  let ModeAtStart := {z : ReferenceActivePhysicalHorizon.State p rate //
    ReferenceActivePhysicalHorizon.allActiveAtStart z s}
  have hmodePairL : (⟨active, hmodeL⟩ : ModeAtStart) = ⟨activeL, hspecL.2.1⟩ := by
    apply Subtype.ext
    exact hactiveL
  have hmodePairR : (⟨active, hmodeR⟩ : ModeAtStart) = ⟨activeR, hspecR.2.1⟩ := by
    apply Subtype.ext
    exact hactiveR
  have hrunModeEvidenceL := congrArg (fun z : ModeAtStart =>
      (ReferenceActivePhysicalHorizon.run z.val source.1.2 q rewards s count hspanCount
        z.property).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) hmodePairL
  have hrunModeEvidenceR := congrArg (fun z : ModeAtStart =>
      (ReferenceActivePhysicalHorizon.run z.val source'.1.2 q rewards s count hspanCount
        z.property).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) hmodePairR
  have hrunPrefix :
      (ReferenceActivePhysicalHorizon.run active source.1.2 q rewards s count (by omega)
        hmodeL).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      (ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s count (by omega)
        hmodeR).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
    calc
      _ = (ReferenceActivePhysicalHorizon.run activeL source.1.2 q rewards s count hspanCount
          hspecL.2.1).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := hrunModeEvidenceL
      _ = _ := hleftPrefix.symm.trans (hprefixEv.2.trans hrightPrefix)
      _ = (ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s count hspanCount
          hmodeR).records.map
            ReferenceActivePhysicalHorizon.RoundRecord.evidence := hrunModeEvidenceR.symm
  have hprefixFullL := activeRun_records_take active source.1.2 q rewards s count
    (p.T - s) (by omega) hspanTotal hmodeL
  have hprefixFullR := activeRun_records_take active source'.1.2 q rewards s count
    (p.T - s) (by omega) hspanTotal hmodeR
  have hprefixEvidenceL :
      ((ReferenceActivePhysicalHorizon.run active source.1.2 q rewards s (p.T-s) hspanTotal
        hmodeL).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence).take count =
      (ReferenceActivePhysicalHorizon.run active source.1.2 q rewards s count hspanCount
        hmodeL).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
    calc
      _ = ((ReferenceActivePhysicalHorizon.run active source.1.2 q rewards s (p.T-s) hspanTotal
          hmodeL).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence).take
            (ReferenceActivePhysicalHorizon.run active source.1.2 q rewards s count hspanCount
              hmodeL).records.length := by
          rw [ReferenceActivePhysicalHorizon.run_record_count]
      _ = ((ReferenceActivePhysicalHorizon.run active source.1.2 q rewards s (p.T-s) hspanTotal
          hmodeL).records.take
            (ReferenceActivePhysicalHorizon.run active source.1.2 q rewards s count hspanCount
              hmodeL).records.length).map
                ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
          rw [← List.map_take]
      _ = _ := congrArg (List.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) hprefixFullL
  have hprefixEvidenceR :
      ((ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s (p.T-s) hspanTotal
        hmodeR).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence).take count =
      (ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s count hspanCount
        hmodeR).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
    calc
      _ = ((ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s (p.T-s) hspanTotal
          hmodeR).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence).take
            (ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s count hspanCount
              hmodeR).records.length := by
          rw [ReferenceActivePhysicalHorizon.run_record_count]
      _ = ((ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s (p.T-s) hspanTotal
          hmodeR).records.take
            (ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s count hspanCount
              hmodeR).records.length).map
                ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
          rw [← List.map_take]
      _ = _ := congrArg (List.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) hprefixFullR
  have hownEvidence :
      ((ReferenceActivePhysicalHorizon.run active source.1.2 q rewards s (p.T-s) hspanTotal
        hmodeL).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence).take count =
      ((ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s (p.T-s) hspanTotal
        hmodeR).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence).take count := by
    calc
      _ = _ := hprefixEvidenceL
      _ = _ := hrunPrefix
      _ = _ := hprefixEvidenceR.symm
  have hidx : v.val - s < count := by dsimp [count]; omega
  let fullL := ReferenceActivePhysicalHorizon.run active source.1.2 q rewards s
    (p.T-s) hspanTotal hmodeL
  let fullR := ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s
    (p.T-s) hspanTotal hmodeR
  have hlenL : fullL.records.length = p.T - s := by
    dsimp [fullL]
    exact ReferenceActivePhysicalHorizon.run_record_count active source.1.2 q rewards s
      (p.T-s) hspanTotal hmodeL
  have hlenR : fullR.records.length = p.T - s := by
    dsimp [fullR]
    exact ReferenceActivePhysicalHorizon.run_record_count active source'.1.2 q rewards s
      (p.T-s) hspanTotal hmodeR
  let indexL : Fin fullL.records.length := ⟨v.val-s, by rw [hlenL]; omega⟩
  let indexR : Fin fullR.records.length := ⟨v.val-s, by rw [hlenR]; omega⟩
  have hget := congrArg (fun entries => entries[v.val-s]?) hownEvidence
  have hidxLNat : v.val - s < fullL.records.length := by rw [hlenL]; omega
  have hidxRNat : v.val - s < fullR.records.length := by rw [hlenR]; omega
  have hgetEvidence : (fullL.records.get indexL).evidence =
      (fullR.records.get indexR).evidence := by
    have hgetMapped :
        Option.map ReferenceActivePhysicalHorizon.RoundRecord.evidence
            (fullL.records[v.val-s]?) =
          Option.map ReferenceActivePhysicalHorizon.RoundRecord.evidence
            (fullR.records[v.val-s]?) := by
      simpa [List.getElem?_take, List.getElem?_map, hidx] using hget
    have hgetL : fullL.records[v.val-s]? = some (fullL.records.get indexL) := by
      rw [List.getElem?_eq_getElem hidxLNat]
      simp [indexL]
    have hgetR : fullR.records[v.val-s]? = some (fullR.records.get indexR) := by
      rw [List.getElem?_eq_getElem hidxRNat]
      simp [indexR]
    rw [hgetL, hgetR] at hgetMapped
    exact Option.some.inj (by simpa using hgetMapped)
  -- Equality is projected from the evidence of literal actual RoundRecords;
  -- no equality of their row-bearing inputs is asserted across the sources.
  have hentryEvidence : (fullL.records.get indexL).evidence.ownEntries player =
      (fullR.records.get indexR).evidence.ownEntries player :=
    congrArg (fun evidence => evidence.ownEntries player) hgetEvidence
  have hentry : (fullL.records.get indexL).ownEntries player =
      (fullR.records.get indexR).ownEntries player := by
    simpa [ReferenceActivePhysicalHorizon.RoundRecord.evidence] using hentryEvidence
  have htime : v = ⟨s + (v.val - s), by omega⟩ := by
    apply Fin.ext
    exact (Nat.add_sub_of_le hsv).symm
  have hnoneL : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h ≠ none := by
    rw [hlaunch]; simp
  have hnoneR : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source' rewards C_star C_h ≠ none := by
    rw [hlaunch']; simp
  let suffixL := ReferenceCompletePhysicalHistory.correctedSuffixRun rate source rewards C_star C_h hnoneL
  let suffixR := ReferenceCompletePhysicalHistory.correctedSuffixRun rate source' rewards C_star C_h hnoneR
  have hrecordsL : suffixL.records = fullL.records := by
    calc
      suffixL.records = ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h := by
            simp [suffixL, ReferenceCompletePhysicalHistory.completeSuffixRecords, hnoneL]
      _ = (ReferenceActivePhysicalHorizon.run active source.1.2 q rewards
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          (by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h
              omega)
          (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some rate source rewards C_star C_h
            active hlaunch)).records :=
          ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch rate source rewards
            C_star C_h active hlaunch
      _ = fullL.records := by simp [fullL, hstart]
  have hrecordsR : suffixR.records = fullR.records := by
    calc
      suffixR.records = ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source' rewards C_star C_h := by
            simp [suffixR, ReferenceCompletePhysicalHistory.completeSuffixRecords, hnoneR]
      _ = (ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards
          (ReferenceCompletePhysicalHistory.physicalStart rate source' rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source' rewards C_star C_h)
          (by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate source' rewards C_star C_h
              omega)
          (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some rate source' rewards C_star C_h
            active hlaunch')).records :=
          ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch rate source' rewards
            C_star C_h active hlaunch'
      _ = fullR.records := by simp [fullR, hstart']
  have hlenSuffixL : suffixL.records.length = p.T - s := by
    simpa [suffixL, hstart] using
      ReferenceCompletePhysicalHistory.correctedSuffixRun_record_count rate source rewards
        C_star C_h hnoneL
  have hlenSuffixR : suffixR.records.length = p.T - s := by
    simpa [suffixR, hstart'] using
      ReferenceCompletePhysicalHistory.correctedSuffixRun_record_count rate source' rewards
        C_star C_h hnoneR
  let suffixIndexL : Fin suffixL.records.length := ⟨v.val-s, by rw [hlenSuffixL]; omega⟩
  let suffixIndexR : Fin suffixR.records.length := ⟨v.val-s, by rw [hlenSuffixR]; omega⟩
  have hrawIndexL : (⟨v.val-s, by
      rw [hlenSuffixL]
      omega⟩ : Fin suffixL.records.length) = suffixIndexL := by
    apply Fin.ext
    rfl
  have hrawIndexR : (⟨v.val-s, by
      rw [hlenSuffixR]
      omega⟩ : Fin suffixR.records.length) = suffixIndexR := by
    apply Fin.ext
    rfl
  have hidxSuffixL : v.val-s < suffixL.records.length := by rw [hlenSuffixL]; omega
  have hidxSuffixR : v.val-s < suffixR.records.length := by rw [hlenSuffixR]; omega
  have hsGetL : suffixL.records[v.val-s]? = some (suffixL.records.get suffixIndexL) := by
    rw [List.getElem?_eq_getElem hidxSuffixL]
    simp [suffixIndexL]
  have hfGetL : fullL.records[v.val-s]? = some (fullL.records.get indexL) := by
    rw [List.getElem?_eq_getElem hidxLNat]
    simp [indexL]
  have hsGetR : suffixR.records[v.val-s]? = some (suffixR.records.get suffixIndexR) := by
    rw [List.getElem?_eq_getElem hidxSuffixR]
    simp [suffixIndexR]
  have hfGetR : fullR.records[v.val-s]? = some (fullR.records.get indexR) := by
    rw [List.getElem?_eq_getElem hidxRNat]
    simp [indexR]
  have hentryRecordsL : (suffixL.records.get suffixIndexL).ownEntries player =
      (fullL.records.get indexL).ownEntries player := by
    have hown := congrArg (fun records =>
      (records[v.val-s]?).map (fun record => record.ownEntries player)) hrecordsL
    rw [hsGetL, hfGetL] at hown
    exact Option.some.inj (by simpa using hown)
  have hentryRecordsR : (suffixR.records.get suffixIndexR).ownEntries player =
      (fullR.records.get indexR).ownEntries player := by
    have hown := congrArg (fun records =>
      (records[v.val-s]?).map (fun record => record.ownEntries player)) hrecordsR
    rw [hsGetR, hfGetR] at hown
    exact Option.some.inj (by simpa using hown)
  rw [htime]
  have hleftSuffix := ReferenceCompletePhysicalHistory.completeOwnHistory_suffix rate source
    rewards C_star C_h player active hlaunch ⟨v.val-s, by rw [hstart]; omega⟩
  have hrightSuffix := ReferenceCompletePhysicalHistory.completeOwnHistory_suffix rate source'
    rewards C_star C_h player active hlaunch' ⟨v.val-s, by rw [hstart']; omega⟩
  have hleftFull :
      ReferenceCompletePhysicalHistory.completeOwnHistory rate source rewards C_star C_h player
        ⟨s + (v.val-s), by omega⟩ = (fullL.records.get indexL).ownEntries player := by
    calc
      _ = (suffixL.records.get (⟨v.val-s, by
            rw [ReferenceCompletePhysicalHistory.correctedSuffixRun_record_count rate source
              rewards C_star C_h hnoneL, hstart]
            omega⟩ : Fin suffixL.records.length)).ownEntries player := by
          simpa [suffixL, hstart] using hleftSuffix
      _ = (suffixL.records.get suffixIndexL).ownEntries player := by rw [hrawIndexL]
      _ = (fullL.records.get indexL).ownEntries player := hentryRecordsL
  have hrightFull :
      ReferenceCompletePhysicalHistory.completeOwnHistory rate source' rewards C_star C_h player
        ⟨s + (v.val-s), by omega⟩ = (fullR.records.get indexR).ownEntries player := by
    calc
      _ = (suffixR.records.get (⟨v.val-s, by
            rw [ReferenceCompletePhysicalHistory.correctedSuffixRun_record_count rate source'
              rewards C_star C_h hnoneR, hstart']
            omega⟩ : Fin suffixR.records.length)).ownEntries player := by
          simpa [suffixR, hstart'] using hrightSuffix
      _ = (suffixR.records.get suffixIndexR).ownEntries player := by rw [hrawIndexR]
      _ = (fullR.records.get indexR).ownEntries player := hentryRecordsR
  exact hleftFull.trans (hentry.trans hrightFull.symm)

/-- Complete actual own histories agree strictly before a replacement of the
selected row's whole continuous-control suffix. -/
theorem completeOwnHistory_eq_of_replaceSelectedControlSuffix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (player : Fin p.m) (v : Fin p.T) (hvt : v.val < t.val) :
    ReferenceCompletePhysicalHistory.completeOwnHistory rate source rewards C_star C_h player v =
      ReferenceCompletePhysicalHistory.completeOwnHistory rate
        (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix source t suffix)
        rewards C_star C_h player v := by
  let source' := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix source t suffix
  have hids : source.1.1 = source'.1.1 :=
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_id source t suffix
  have hprivate : source.2 = source'.2 :=
    ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_private source t suffix
  have hforward : ∀ q : Fin p.T, q.val < t.val →
      ∀ u : Fin (BootstrapDimensions.A_id p),
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u q =
          (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u q := by
    intro q hq u
    exact congrArg (fun row : CompletePublicTable.ForwardRow p => row u q)
      (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_forward source t suffix).symm
  have hcontrol : ∀ q : Fin p.T, q.val < t.val →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 q =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 q := by
    intro q hq
    exact (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_before
      source t q suffix hq).symm
  have hstopped := ReferenceInitializationStoppedLocality.source_calendar_stopped_event_iff
    rate rewards C_star C_h source source' t.val (Nat.le_of_lt t.isLt)
    hids hprivate hforward hcontrol
  let x := ReferenceCompletePhysicalHistory.generatedInput rate source rewards C_star C_h
  let y := ReferenceCompletePhysicalHistory.generatedInput rate source' rewards C_star C_h
  by_cases hby : (ReferenceInitializationRun.output x).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed ≤ t.val
  · have hbyRef :
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true ∧
        ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed ≤ t.val := by
      simpa [x, ReferenceCompletePhysicalHistory.generatedInput] using hby
    have hby' := hstopped.mp hbyRef
    have hcalendar := ReferenceInitializationStoppedLocality.source_calendar_stopped_output_eq_of_event
      rate rewards C_star C_h source source' t.val (Nat.le_of_lt t.isLt)
      hids hprivate hforward hcontrol (Or.inl hbyRef)
    have houtputEq := hcalendar.2.1
    change ReferenceInitializationRun.output x = ReferenceInitializationRun.output y at houtputEq
    let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed
    have hcrossLaunch : (ReferenceInitializationRun.output x).crossing.isSome = true := hby.1
    have hcrossActual : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true := by
      simpa [x, ReferenceCompletePhysicalHistory.generatedInput] using hcrossLaunch
    have hElapsedActual : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s := by
      rfl
    have hlaunchSome := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).mpr hcrossLaunch
    have hactiveExists : ∃ active,
        ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
          some active := by
      cases hopt : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h with
      | none => simp [hopt] at hlaunchSome
      | some active => exact ⟨active, rfl⟩
    rcases hactiveExists with ⟨active, hlaunchActive⟩
    have hpres := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_preserves_actual_launch
      rewards C_star C_h (ActualInitializationPhysicalStep.selectedRowIndex p source) t s
      (by
        simpa [s, x, ReferenceCompletePhysicalHistory.generatedInput] using hby.2)
      source rfl suffix
      hcrossActual hElapsedActual
    rcases hpres with ⟨_, _, hElapsed', hlaunchEq⟩
    have hlaunch' : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source' rewards C_star C_h =
        some active := by
      exact hlaunchEq.symm.trans hlaunchActive
    have hstart : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s := by
      rfl
    have hElapsedEq : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output y).completed = s := by
      change ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output y).completed =
          ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed
      exact (congrArg (fun b : ReferenceInitializationRun.Boundary p =>
        ReferenceInitializationRun.elapsed p b.completed) houtputEq).symm
    by_cases hvs : v.val < s
    · have hstart' : ReferenceCompletePhysicalHistory.physicalStart rate source' rewards C_star C_h = s := by
        simpa [ReferenceCompletePhysicalHistory.physicalStart,
          ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput, y] using hElapsedEq
      have hleft : v.val < ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
        rw [hstart]
        exact hvs
      have hright : v.val < ReferenceCompletePhysicalHistory.physicalStart rate source' rewards C_star C_h := by
        rw [hstart']
        exact hvs
      exact initializer_history_eq_before rate rewards C_star C_h source source' t v hvt
        hids hprivate hforward hcontrol hleft hright player
    · have hsv : s ≤ v.val := by omega
      exact source_active_own_entry_eq rate rewards C_star C_h source t suffix v hvt active
        hlaunchActive s (by dsimp [s]; exact hby.2) hsv hstart player
  · have hnotBy : ¬ ((ReferenceInitializationRun.output y).crossing.isSome = true ∧
        ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output y).completed ≤ t.val) := by
      intro hy
      have hyRef :
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)).crossing.isSome = true ∧
          ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)).completed ≤ t.val := by
        simpa [y, ReferenceCompletePhysicalHistory.generatedInput] using hy
      exact hby (by
        have := hstopped.mpr hyRef
        simpa [x, ReferenceCompletePhysicalHistory.generatedInput] using this)
    have hstartX : v.val < ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
      by_cases hc : (ReferenceInitializationRun.output x).crossing.isSome = true
      · have hs : t.val < ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed := by
          by_contra hle
          exact hby ⟨hc, Nat.le_of_not_gt hle⟩
        change v.val < ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output x).completed
        exact Nat.lt_trans hvt hs
      · have hnone : (ReferenceInitializationRun.output x).crossing = none := by
          cases hh : (ReferenceInitializationRun.output x).crossing <;> simp_all
        have hT := ReferenceInitializationRun.output_elapsed_of_no_crossing x hnone
        change v.val < ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output x).completed
        rw [hT]
        exact v.isLt
    have hstartY : v.val < ReferenceCompletePhysicalHistory.physicalStart rate source' rewards C_star C_h := by
      by_cases hc : (ReferenceInitializationRun.output y).crossing.isSome = true
      · have hs : t.val < ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output y).completed := by
          by_contra hle
          exact hnotBy ⟨hc, Nat.le_of_not_gt hle⟩
        change v.val < ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output y).completed
        exact Nat.lt_trans hvt hs
      · have hnone : (ReferenceInitializationRun.output y).crossing = none := by
          cases hh : (ReferenceInitializationRun.output y).crossing <;> simp_all
        have hT := ReferenceInitializationRun.output_elapsed_of_no_crossing y hnone
        change v.val < ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output y).completed
        rw [hT]
        exact v.isLt
    exact initializer_history_eq_before rate rewards C_star C_h source source' t v hvt
      hids hprivate hforward hcontrol hstartX hstartY player

/-- Restriction to the natural strict-past history `Fin t.val`, cast into the
actual `Fin T` carrier. Every coordinate remains the actual own action and
quantized own observation from the complete reference execution. -/
theorem completeOwnHistory_restrict_eq_of_replaceSelectedControlSuffix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (player : Fin p.m) :
    (fun k : Fin t.val => ReferenceCompletePhysicalHistory.completeOwnHistory
      rate source rewards C_star C_h player (Fin.castLE (Nat.le_of_lt t.isLt) k)) =
    (fun k : Fin t.val => ReferenceCompletePhysicalHistory.completeOwnHistory rate
      (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix source t suffix)
      rewards C_star C_h player (Fin.castLE (Nat.le_of_lt t.isLt) k)) := by
  funext k
  exact completeOwnHistory_eq_of_replaceSelectedControlSuffix rate rewards C_star C_h
    source t suffix player (Fin.castLE (Nat.le_of_lt t.isLt) k) k.isLt

end Bandits.Support.ReferenceCompleteOwnHistoryPrefixLocality

end
