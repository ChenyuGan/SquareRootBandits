/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationSourceObservation

/-!
# Actual initialization physical rewards

The observable below is the sum of the finite-grid feedback actually produced
by the source-initialized physical records.  It keeps the original complete
public table, all private coordinates, the private coordinator index, the
whole denominator-`D` reward table, and the common run constants.

Mathematical evidence: `sources/zip4/manuscript/01_introduction.tex:18-36`,
`sources/zip4/manuscript/07_public_setup.tex:55-114,144-164`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131,160-165`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-48,67-75`.

This module proves internal physical-reward, Borel-section and integrability
facts for the actual initialization only.  It makes no selected-row locality,
coupling, probability estimate, postlaunch, reference, or regret claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.CompletePublicTable
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationHorizon
open Bandits.Support.ActualInitializationHorizonObservation
open Bandits.Support.ActualInitializationHorizonMeasurability
open Bandits.Support.ActualInitializationBlockFoldMeasurability
open Bandits.Support.ActualInitializationStepMeasurability
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.BootstrapObservedFollower

namespace Bandits.Support.ActualInitializationPhysicalRewards

abbrev Parameters := ActualInitializationHorizon.Parameters
abbrev RateInput := ActualInitializationHorizonMeasurability.RateInput
abbrev GridRewardTable := ActualInitializationHorizonMeasurability.GridRewardTable

variable {p : Parameters} {rate : RateInput p}
  {C_star C_h : ℝ} {rewards : GridRewardTable p}

/-- The observed real reward in one actual initialization record.  Feedback is
the existing collision-filtered finite-grid value, divided by the original
denominator `D`. -/
def physicalRoundRecordObservedReward
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards) : ℝ :=
  ∑ player : Fin p.m,
    ((record.result.feedback player).val : ℝ) / (D p : ℝ)

/-- Actual source-initialization reward: sum the literal per-round rewards of
the records produced by `H.sourceInitializedRun`. -/
def sourceInitializationReward
    (source : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).records.map
    (physicalRoundRecordObservedReward (p := p) (rate := rate) (rewards := rewards))).sum

/-- The feedback of every actual physical record is the collision-filtered
original grid reward at that record's time and simultaneous action profile. -/
theorem physicalRoundRecordObservedReward_feedback
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (player : Fin p.m)
    [Decidable (FiniteBanditModel.collisionFreeFor record.result.actions player)] :
    ((record.result.feedback player).val : ℝ) / (D p : ℝ) =
      (if FiniteBanditModel.collisionFreeFor record.result.actions player then
        ((rewards record.time (record.result.actions player)).val : ℝ) / (D p : ℝ)
       else 0) := by
  classical
  have hactual := ActualInitializationHorizon.physicalRoundRecord_actual record
  rcases hactual with ⟨_, hsource, hrew, hactions, hfeedback⟩
  by_cases hfree : FiniteBanditModel.collisionFreeFor record.result.actions player
  · simp [hfeedback, ActualInitializationPhysicalStep.physicalFeedback,
      ActualInitializationPhysicalStep.gridFeedback, ← hactions, hrew,
      record.result_time, hfree]
  · simp [hfeedback, ActualInitializationPhysicalStep.physicalFeedback,
      ActualInitializationPhysicalStep.gridFeedback, ← hactions, hfree]

private def partialOwnEntryRealReward (entry :
    ActualInitializationStepMeasurability.PartialPhysicalOwnEntryCode p) : ℝ :=
  Sum.elim (fun _ => 0) (fun actionFeedback =>
    ((actionFeedback.2.val : ℝ) / (D p : ℝ))) entry

private def fullRoundCodeObservedReward
    (code : ActualInitializationHorizonMeasurability.FullPhysicalRoundCode
      (p := p) (rate := rate)) : ℝ :=
  ∑ player : Fin p.m,
    partialOwnEntryRealReward (ActualInitializationHorizonObservation.fullOwnEntry
      (p := p) (rate := rate) player code)

private def roundCodeSlotObservedReward {α : Type*} (f : α → ℝ)
    (code : Unit ⊕ α) : ℝ :=
  Sum.elim (fun _ => 0) f code

private def sourceInitializationRewardCodeSum
    (source : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ∑ block : Fin (n_boot p), ∑ cursor : Fin p.T,
    roundCodeSlotObservedReward (fullRoundCodeObservedReward (p := p) (rate := rate))
      (((roundCodeListCoordinates
        (((ActualInitializationHorizon.sourceInitializedRun p rate source rewards
            C_star C_h).records.filter (fun record => record.block == block)).map
          (fullRecordCode (C_star := C_star) (C_h := C_h)))).2 cursor.val))

private theorem measurable_sigma_elim {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) : Measurable f := by
  intro s hs
  change MeasurableSet[
      (⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

private theorem measurable_partialOwnEntryRealReward :
    Measurable (partialOwnEntryRealReward (p := p)) := by
  change Measurable (Sum.elim (fun _ : Unit => (0 : ℝ))
    (fun actionFeedback : ActualInitializationStepMeasurability.PhysicalOwnEntryCode p =>
      ((actionFeedback.2.val : ℝ) / (D p : ℝ))))
  exact Measurable.sumElim measurable_const (measurable_of_finite _)

private theorem measurable_fullRoundCodeObservedReward :
    Measurable (fullRoundCodeObservedReward (p := p) (rate := rate)) := by
  apply measurable_sigma_elim
  intro block
  change Measurable (fun code : ActualInitializationStepMeasurability.ActualRoundOutputCode
      p rate block =>
    ∑ player : Fin p.m, partialOwnEntryRealReward
      (ActualInitializationStepMeasurability.physicalOwnEntryFromActualRoundOutput
        rate block code player))
  exact Finset.univ.measurable_fun_sum fun player _ =>
    measurable_partialOwnEntryRealReward.comp
      (ActualInitializationStepMeasurability.measurable_physicalOwnEntryFromActualRoundOutput
        rate block player)

private theorem measurable_roundCodeSlotObservedReward {α : Type*}
    [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) :
    Measurable (roundCodeSlotObservedReward f) :=
  Measurable.sumElim measurable_const hf

private theorem measurable_sourceInitializationRewardCodeSum :
    Measurable (sourceInitializationRewardCodeSum (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  unfold sourceInitializationRewardCodeSum
  apply Finset.univ.measurable_fun_sum
  intro block _
  apply Finset.univ.measurable_fun_sum
  intro cursor _
  exact (measurable_roundCodeSlotObservedReward
    measurable_fullRoundCodeObservedReward).comp
      (ActualInitializationSourceObservation.measurable_sourceInitializedRun_round_stream
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) block cursor.val)

private theorem list_map_sum_congr_of_mem {α : Type*} (l : List α)
    (f g : α → ℝ) (hfg : ∀ x ∈ l, f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx := hfg x (by simp)
      have htail := ih (fun y hy => hfg y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, hx, htail]

private theorem list_map_pointwise_of_eq {α β : Type*}
    (l : List α) (f g : α → β) (h : l.map f = l.map g)
    (x : α) (hx : x ∈ l) : f x = g x := by
  induction l with
  | nil => simp at hx
  | cons head tail ih =>
      injection h with hhead htail
      rcases List.mem_cons.mp hx with hEq | hmem
      · simpa [hEq] using hhead
      · exact ih htail hmem

private theorem list_map_sum_eq_sum_filters {α β : Type*} [Fintype β]
    [DecidableEq β] (l : List α) (key : α → β) (f : α → ℝ) :
    (l.map f).sum = ∑ b : β, ((l.filter (fun x => key x == b)).map f).sum := by
  classical
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hsum : (∑ b : β, if key x == b then f x else 0) = f x := by
        simp
      have hfilterSum (b : β) :
          (((x :: xs).filter (fun y => key y == b)).map f).sum =
            if key x == b then f x + ((xs.filter (fun y => key y == b)).map f).sum
            else ((xs.filter (fun y => key y == b)).map f).sum := by
        by_cases h : key x == b <;> simp [h]
      rw [List.map_cons, List.sum_cons, ih]
      calc
        f x + (∑ b : β, ((xs.filter (fun y => key y == b)).map f).sum) =
            (∑ b : β, if key x == b then f x else 0) +
              ∑ b : β, ((xs.filter (fun y => key y == b)).map f).sum := by rw [hsum]
        _ = ∑ b : β,
            ((if key x == b then f x else 0) +
              ((xs.filter (fun y => key y == b)).map f).sum) := by
                rw [← Finset.sum_add_distrib]
        _ = ∑ b : β,
            if key x == b then f x + ((xs.filter (fun y => key y == b)).map f).sum
            else ((xs.filter (fun y => key y == b)).map f).sum := by
              apply Finset.sum_congr rfl
              intro b _
              by_cases h : key x == b <;> simp [h]
        _ = ∑ b : β, (((x :: xs).filter (fun y => key y == b)).map f).sum := by
              apply Finset.sum_congr rfl
              intro b _
              exact (hfilterSum b).symm

private theorem list_map_sum_eq_roundCodeStream_sum {α : Type*}
    (l : List α) (f : α → ℝ) (n : ℕ) (hlen : l.length ≤ n) :
    (l.map f).sum = ∑ cursor : Fin n,
      roundCodeSlotObservedReward f ((roundCodeListCoordinates l).2 cursor.val) := by
  classical
  induction n generalizing l with
  | zero =>
      cases l with
      | nil => simp [roundCodeSlotObservedReward, roundCodeListCoordinates]
      | cons head tail => simp at hlen
  | succ n ih =>
      cases l with
      | nil => simp [roundCodeSlotObservedReward, roundCodeListCoordinates]
      | cons head tail =>
          have htail : tail.length ≤ n := by simp at hlen; omega
          rw [Fin.sum_univ_succ]
          simp only [List.map_cons, List.sum_cons, roundCodeSlotObservedReward,
            roundCodeListCoordinates]
          simp [List.getElem?_cons_succ, Fin.val_succ]
          exact ih tail htail

private theorem sourceInitializedRun_recordOwnEntry_code
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (hrecord : record ∈
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).records)
    (player : Fin p.m) :
    ActualInitializationHorizonObservation.fullOwnEntry (p := p) (rate := rate) player
        (ActualInitializationHorizonObservation.fullRecordCode
          (C_star := C_star) (C_h := C_h) record) =
      Sum.inr (record.result.actions player, record.result.feedback player) := by
  let observation := ActualInitializationSourceObservation.sourceInitializedRunObservation
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  have hcodes := Bandits.Support.ActualInitializationSourceObservation.sourceInitializedRunObservation_chronologicalRoundCodes
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source
  have hhistory := Bandits.Support.ActualInitializationSourceObservation.sourceInitializedRunObservation_ownHistory
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source player
  have hmaps :
      run.records.map (fun r =>
        ActualInitializationHorizonObservation.fullOwnEntry (p := p) (rate := rate)
          player (ActualInitializationHorizonObservation.fullRecordCode
            (C_star := C_star) (C_h := C_h) r)) =
      run.records.map (fun r => Sum.inr (r.result.actions player, r.result.feedback player)) := by
    change (ActualInitializationHorizonObservation.chronologicalRoundCodes
        (ActualInitializationRun.firstBlock p) observation.suffix).map
          (ActualInitializationHorizonObservation.fullOwnEntry player) = _ at hhistory
    rw [hcodes] at hhistory
    simpa only [List.map_map, Function.comp_def] using hhistory
  have hpoint := list_map_pointwise_of_eq run.records _ _ hmaps record hrecord
  exact hpoint

private theorem fullRoundCodeObservedReward_eq_record
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (hrecord : record ∈
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).records) :
    fullRoundCodeObservedReward (p := p) (rate := rate)
        (ActualInitializationHorizonObservation.fullRecordCode
          (C_star := C_star) (C_h := C_h) record) =
      physicalRoundRecordObservedReward record := by
  have hown := fun player => sourceInitializedRun_recordOwnEntry_code
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (rewards := rewards) source record hrecord player
  unfold fullRoundCodeObservedReward physicalRoundRecordObservedReward
  apply Finset.sum_congr rfl
  intro player _
  rw [hown player]
  rfl

private theorem sourceInitializationReward_eq_codeSum
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    sourceInitializationReward (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) (rewards := rewards) source =
      sourceInitializationRewardCodeSum (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source := by
  classical
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  have hcount : run.records.length = BootstrapObservedFollower.blockStop p run.terminalBlock := by
    simpa [run, ActualInitializationRun.PhysicalRoundRecord.actions] using
      (ActualInitializationHorizon.sourceInitializedRun_history_lengths
        p rate source rewards C_star C_h).1
  have hstop : BootstrapObservedFollower.blockStop p run.terminalBlock ≤ p.T :=
    Nat.min_le_left _ _
  unfold sourceInitializationReward sourceInitializationRewardCodeSum
  have hpartition := list_map_sum_eq_sum_filters
    (l := run.records)
    (key := fun record => record.block)
    (f := physicalRoundRecordObservedReward (p := p) (rate := rate)
      (rewards := rewards))
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro block _
  let blockRecords := run.records.filter (fun record => record.block == block)
  have hlen : blockRecords.length ≤ p.T := by
    have hfilter : blockRecords.length ≤ run.records.length := by
      exact List.length_filter_le _ _
    omega
  have hmap : (blockRecords.map
      (physicalRoundRecordObservedReward (p := p) (rate := rate) (rewards := rewards))).sum =
      (blockRecords.map (fun record => fullRoundCodeObservedReward
        (p := p) (rate := rate)
        (ActualInitializationHorizonObservation.fullRecordCode
          (C_star := C_star) (C_h := C_h) record))).sum := by
    apply list_map_sum_congr_of_mem
    intro record hmem
    exact (fullRoundCodeObservedReward_eq_record (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source record
      (List.mem_of_mem_filter hmem)).symm
  rw [hmap]
  simpa only [List.map_map, Function.comp_def, blockRecords,
    ActualInitializationHorizonObservation.fullRecordCode] using
    (list_map_sum_eq_roundCodeStream_sum
      (blockRecords.map (fullRecordCode (C_star := C_star) (C_h := C_h)))
      (fullRoundCodeObservedReward (p := p) (rate := rate)) p.T (by
        simpa only [List.length_map] using hlen))

/-- The total actual reward is nonnegative and bounded by the actual clipped
terminal boundary, hence by the full horizon.  Record count comes from H's
chronological producer, including shortened final blocks. -/
theorem sourceInitializationReward_bounds
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    0 ≤ sourceInitializationReward (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) (rewards := rewards) source ∧
      sourceInitializationReward (p := p) (rate := rate) (C_star := C_star)
        (C_h := C_h) (rewards := rewards) source ≤
        (p.m : ℝ) * (BootstrapObservedFollower.blockStop p
          (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
            C_star C_h).terminalBlock : ℝ) ∧
      (p.m : ℝ) * (BootstrapObservedFollower.blockStop p
          (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
            C_star C_h).terminalBlock : ℝ) ≤ (p.m : ℝ) * (p.T : ℝ) := by
  have hD : (0 : ℝ) < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
  have hrecord : ∀ record : ActualInitializationRun.PhysicalRoundRecord
      p rate source rewards,
      0 ≤ physicalRoundRecordObservedReward record ∧
      physicalRoundRecordObservedReward record ≤ (p.m : ℝ) := by
    intro record
    constructor
    · unfold physicalRoundRecordObservedReward
      apply Finset.sum_nonneg
      intro player _
      exact div_nonneg (Nat.cast_nonneg _) hD.le
    · unfold physicalRoundRecordObservedReward
      calc
        (∑ player : Fin p.m,
            ((record.result.feedback player).val : ℝ) / (D p : ℝ)) ≤
          ∑ _player : Fin p.m, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro player _
            have hval : (record.result.feedback player).val ≤ D p := by
              have := (record.result.feedback player).isLt
              omega
            calc
              ((record.result.feedback player).val : ℝ) / (D p : ℝ) ≤
                  (D p : ℝ) / (D p : ℝ) := div_le_div_of_nonneg_right
                    (by exact_mod_cast hval) hD.le
              _ = 1 := div_self (ne_of_gt hD)
        _ = (p.m : ℝ) := by simp
  have hplayers : (0 : ℝ) ≤ (p.m : ℝ) := Nat.cast_nonneg _
  have hsum :
      0 ≤ ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards
          C_star C_h).records.map
            (physicalRoundRecordObservedReward (p := p) (rate := rate)
              (rewards := rewards))).sum ∧
      ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards
          C_star C_h).records.map
            (physicalRoundRecordObservedReward (p := p) (rate := rate)
              (rewards := rewards))).sum ≤
        ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards
            C_star C_h).records.length : ℝ) * (p.m : ℝ) := by
    let rec boundList : ∀ l : List (ActualInitializationRun.PhysicalRoundRecord
        p rate source rewards),
        0 ≤ (l.map physicalRoundRecordObservedReward).sum ∧
          (l.map physicalRoundRecordObservedReward).sum ≤ (l.length : ℝ) * (p.m : ℝ) := by
      intro l
      induction l with
      | nil => simp
      | cons record records ih =>
          rcases hrecord record with ⟨hnonneg, hle⟩
          simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
          constructor <;> nlinarith
    simpa only [sourceInitializationReward, List.length_map] using
      boundList (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).records
  have hcount :
      ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).records).length =
        BootstrapObservedFollower.blockStop p
          (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
            C_star C_h).terminalBlock := by
    simpa [ActualInitializationRun.PhysicalRoundRecord.actions] using
      (ActualInitializationHorizon.sourceInitializedRun_history_lengths
        p rate source rewards C_star C_h).1
  have hstop : BootstrapObservedFollower.blockStop p
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).terminalBlock ≤ p.T := Nat.min_le_left _ _
  refine ⟨?_, ?_, ?_⟩
  · simpa [sourceInitializationReward] using hsum.1
  · calc
      sourceInitializationReward (p := p) (rate := rate) (C_star := C_star)
          (C_h := C_h) (rewards := rewards) source ≤
        ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards
          C_star C_h).records.length : ℝ) * (p.m : ℝ) := by
            simpa [sourceInitializationReward] using hsum.2
      _ = (p.m : ℝ) * (BootstrapObservedFollower.blockStop p
          (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
            C_star C_h).terminalBlock : ℝ) := by rw [hcount]; ring
  · exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hstop) hplayers

/-- The source-initialized record list has exactly the number of rounds through
its actual clipped terminal boundary. -/
theorem sourceInitializationReward_record_count
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).records.length =
      BootstrapObservedFollower.blockStop p
        (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
          C_star C_h).terminalBlock := by
  simpa [ActualInitializationRun.PhysicalRoundRecord.actions] using
    (ActualInitializationHorizon.sourceInitializedRun_history_lengths
      p rate source rewards C_star C_h).1

/-- On no-crossing exhaustion, all `T` physical records are retained and the
no-crossing monitor tag remains distinct. -/
theorem sourceInitializationReward_exhaustion_records
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hexhausted :
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).terminalDisposition = .exhausted live) :
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).records.length = p.T ∧
      live.monitor.1.crossingBlock = none ∧ live.monitor.1.launchPosition = p.T ∧
      (ActualInitializationRun.PhysicalRoundRecord.times
        (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
          C_star C_h).records).map Fin.val = consecutiveNat 0 p.T := by
  have hterminal := Bandits.Support.ActualInitializationHorizon.sourceInitializedRun_exhaustion_reaches_horizon
      p rate source rewards C_star C_h live hexhausted
  have hcount := sourceInitializationReward_record_count (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards) source
  have hchron := ActualInitializationHorizon.sourceInitializedRun_chronological
    p rate source rewards C_star C_h
  rw [hterminal.1] at hcount hchron
  exact ⟨hcount, hterminal.2.1, hterminal.2.2, hchron⟩

/-- A terminal launch at elapsed time `T` still has all `T` actual physical
records.  Its strict trigger remains a launch, with numerical next-round value
`T+1`; the record chronology itself ends at `T`. -/
theorem sourceInitializationReward_terminalLaunch_at_horizon
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched :
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hposition : launch.monitor.launchPosition = p.T) :
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).records.length = p.T ∧
      launch.monitor.crossingBlock =
        some (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
          C_star C_h).terminalBlock ∧
      BootstrapLaunchMonitor.monitorValue p launch.monitor.counters >
        4 * BootstrapStartupCostScale.Q launch.data.C_star launch.data.C_h p ∧
      launch.monitor.launchPosition + 1 = p.T + 1 ∧
      (ActualInitializationRun.PhysicalRoundRecord.times
        (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
          C_star C_h).records).map Fin.val = consecutiveNat 0 p.T := by
  have hstrict := ActualInitializationHorizon.sourceInitializedRun_terminal_launch_strict
    p rate source rewards C_star C_h launch learnerSeed hlaunched
  have hstop : BootstrapObservedFollower.blockStop p
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).terminalBlock = p.T := by omega
  have hcount := sourceInitializationReward_record_count (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards) source
  have hchron := ActualInitializationHorizon.sourceInitializedRun_chronological
    p rate source rewards C_star C_h
  rw [hstop] at hcount hchron
  exact ⟨hcount, hstrict.2.1, hstrict.2.2.1, by omega, hchron⟩

/-- The literal actual reward is Borel on the whole original source input.  Its
proof uses the admitted indexed actual record stream and the exact identity
between that stream and the record-sum definition above. -/
theorem measurable_sourceInitializationReward :
    Measurable (sourceInitializationReward (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  have hcode := measurable_sourceInitializationRewardCodeSum
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)
  have hEq : sourceInitializationReward (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) =
    sourceInitializationRewardCodeSum (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) := by
    funext source
    exact sourceInitializationReward_eq_codeSum (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source
  rw [hEq]
  exact hcode

/-- Fixing a complete public output leaves every original private coordinate,
including the coordinator's private `J`, variable. -/
def fixedPublicSourceInitializationReward
    (published : CompletePublicTable.PublishedOutput p)
    (privateCoordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) : ℝ :=
  sourceInitializationReward (p := p) (rate := rate) (C_star := C_star)
    (C_h := C_h) (rewards := rewards) (published, privateCoordinates)

/-- Every fixed-public, full-private section of the actual reward is Borel. -/
theorem measurable_fixedPublicSourceInitializationReward
    (published : CompletePublicTable.PublishedOutput p) :
    Measurable (fixedPublicSourceInitializationReward (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) published) :=
  (measurable_sourceInitializationReward (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards)).comp
      (measurable_const.prodMk measurable_id)

private theorem integrable_of_nonneg_bounded {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) {B : ℝ}
    (hnonneg : ∀ x, 0 ≤ f x) (hbound : ∀ x, f x ≤ B) : Integrable f μ := by
  refine (integrable_const B).mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
  exact hbound x

/-- The full-source reward is integrable under the original source input law. -/
theorem integrable_sourceInitializationReward :
    Integrable (sourceInitializationReward (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards))
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  refine integrable_of_nonneg_bounded
    (measurable_sourceInitializationReward (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards))
    (B := (p.m : ℝ) * (p.T : ℝ)) ?_ ?_
  · intro source
    exact (sourceInitializationReward_bounds (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source).1
  · intro source
    exact ((sourceInitializationReward_bounds (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source).2.1).trans
        (sourceInitializationReward_bounds (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards) source).2.2

/-- Every fixed-public full-private reward section is integrable under the
original extended private law. -/
theorem integrable_fixedPublicSourceInitializationReward
    (published : CompletePublicTable.PublishedOutput p) :
    Integrable (fixedPublicSourceInitializationReward (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) published)
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
  refine integrable_of_nonneg_bounded
    (measurable_fixedPublicSourceInitializationReward (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) published)
    (B := (p.m : ℝ) * (p.T : ℝ)) ?_ ?_
  · intro privateCoordinates
    exact (sourceInitializationReward_bounds (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)
      (published, privateCoordinates)).1
  · intro privateCoordinates
    exact ((sourceInitializationReward_bounds (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)
      (published, privateCoordinates)).2.1).trans
        (sourceInitializationReward_bounds (p := p) (rate := rate)
          (C_star := C_star) (C_h := C_h) (rewards := rewards)
          (published, privateCoordinates)).2.2

def variableRowSourceInput
    (ids : CompletePublicTable.IDArray p)
    (rows : CompletePublicTable.CompleteRows p) (j0 : Fin (M p))
    (pair : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    BootstrapPrivateRoundStreams.SourceInput p :=
  (ActualInitializationSourceObservation.variableRowPublishedOutput
    (p := p) ids rows j0 pair.1, pair.2)

/-- Joint section in one replaced whole continuous row and all original
private coordinates.  The private tuple, including `J`, is unchanged. -/
def variableRowPrivateSourceInitializationReward
    (ids : CompletePublicTable.IDArray p)
    (rows : CompletePublicTable.CompleteRows p) (j0 : Fin (M p))
    (pair : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) : ℝ :=
  sourceInitializationReward (p := p) (rate := rate) (C_star := C_star)
    (C_h := C_h) (rewards := rewards) (variableRowSourceInput ids rows j0 pair)

private theorem measurable_variableRowSourceInput
    (ids : CompletePublicTable.IDArray p)
    (rows : CompletePublicTable.CompleteRows p) (j0 : Fin (M p)) :
    Measurable (variableRowSourceInput (p := p) ids rows j0) := by
  have hrows : Measurable (fun pair : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        fun j : Fin (M p) => if j = j0 then pair.1 else rows j) := by
    apply measurable_pi_iff.mpr
    intro j
    by_cases h : j = j0
    · subst j
      simpa using (measurable_fst : Measurable
        (fun pair : CompletePublicTable.CompleteRow p ×
          BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p => pair.1))
    · simp [h]
  have hpublished : Measurable (fun pair : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        ActualInitializationSourceObservation.variableRowPublishedOutput
          (p := p) ids rows j0 pair.1) := by
    change Measurable (fun pair : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
        (ids, fun j : Fin (M p) => if j = j0 then pair.1 else rows j))
    exact measurable_const.prodMk hrows
  change Measurable (fun pair : CompletePublicTable.CompleteRow p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      (ActualInitializationSourceObservation.variableRowPublishedOutput
        (p := p) ids rows j0 pair.1, pair.2))
  exact hpublished.prodMk measurable_snd

/-- Replacing one whole complete row jointly with the full original private
tuple gives a Borel section of the actual source-initialization reward. -/
theorem measurable_variableRowPrivateSourceInitializationReward
    (ids : CompletePublicTable.IDArray p)
    (rows : CompletePublicTable.CompleteRows p) (j0 : Fin (M p)) :
    Measurable (variableRowPrivateSourceInitializationReward (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) ids rows j0) :=
  (measurable_sourceInitializationReward (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards)).comp
      (measurable_variableRowSourceInput (p := p) ids rows j0)

end Bandits.Support.ActualInitializationPhysicalRewards

end
