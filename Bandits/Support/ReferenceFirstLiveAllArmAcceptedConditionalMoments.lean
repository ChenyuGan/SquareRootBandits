/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveAllArmConditionalMoments
public import Bandits.Support.ReferenceFirstLiveChronologicalRetainedUpdate

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic

/-!
# Accepted all-arm arrivals, chronological queue service, and the current endpoint

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-168,256-264`,
`sources/zip4/manuscript/05_binary_transport.tex:354-396`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This internal consumer uses the existing continuing first-live `SourcePlus`
carrier, unnormalized branch measure, and strict-past field from
`ReferenceFirstLiveAllArmConditionalMoments`. Its accepted estimate is the
literal accepted record projection from the existing chronological queue run.
The first and square conditional laws therefore apply to the accepted record
itself. Queue identities use the current inclusive update; the physical current
round remains unconditional even when the numerical queue has already stopped.
The physical endpoint comparison is stated only before the first overflow.
These results do not identify the field with manuscript history or close a
source-facing regret statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveAllArmAcceptedConditionalMoments

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Zplus" =>
  ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
    rate rewards C_star C_h q t s hs control0
local notation "muPlus" =>
  ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
local notation "Fplus" =>
  ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
    rate rewards C_star C_h q t s hs control0
local notation "G" =>
  ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
    rate rewards C_star C_h q t s hs control0
local notation "currentOffset" => t.val - s
local notation "cellListAtPoint" =>
  ReferenceFirstLiveSourceCellReadout.cells rate rewards C_star C_h q t s hs control0
local notation "cell" =>
  ReferenceFirstLiveSourceCellReadout.cell rate rewards C_star C_h q t s hs control0
local notation "queue" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "past" => fun z : Zplus =>
  RecordedQueueRun.run queue (List.take currentOffset (cellListAtPoint z))
local notation "post" => fun z : Zplus =>
  RecordedQueueRun.run queue (List.take (currentOffset + 1) (cellListAtPoint z))
local notation "firstOverflow" => fun z : Zplus =>
  UnstoppedRecordedQueueComparison.firstOverflowPrefix queue (cellListAtPoint z)

local notation "scale" => rate.eta.val * (ConstructorDimensions.D p : ℝ)

/-- The actual accepted-record projection, normalized by the source's
`eta * D` scale. It is not a retained indicator or a separately sampled
estimate. -/
def acceptedA (j : Fin p.K) (z : Zplus) : ℝ :=
  (RecordedQueueRun.acceptedArrival
    (RecordedQueueRun.acceptedRecord queue (past z) (cell z).input j) : ℝ) / scale

/-- The normalized backlog in the chronological run before the current cell. -/
def backlogBefore (j : Fin p.K) (z : Zplus) : ℝ :=
  (((past z).registers j).2 : ℝ) / scale

/-- The normalized backlog in the chronological run after the current cell. -/
def backlogAfter (j : Fin p.K) (z : Zplus) : ℝ :=
  (((post z).registers j).2 : ℝ) / scale

/-- The normalized current score increment from the same past and post runs. -/
def service (j : Fin p.K) (z : Zplus) : ℝ :=
  (((((post z).registers j).1 - ((past z).registers j).1 : ℕ) : ℝ) / scale)

/-- The literal strict-past overflow event is equivalent to the current offset
being strictly before the first overflowing prefix. -/
theorem mem_strictPast_iff_offset_lt_firstOverflow (z : Zplus) :
    z ∈ G ↔ currentOffset < firstOverflow z := by
  change (past z).overflow = false ↔ currentOffset < firstOverflow z
  exact
    (ReferenceFirstLiveChronologicalRetainedUpdate.actual_current_stopped_update
      rate rewards C_star C_h q t s hs control0 z).1

/-- The current source cell is enabled on the existing `Zplus` carrier. -/
theorem currentCell_enabled (z : Zplus) : (cell z).input.enabled = true := by
  exact
    (ReferenceFirstLiveChronologicalRetainedUpdate.actual_current_stopped_update
      rate rewards C_star C_h q t s hs control0 z).2.2.1

/-- The incoming queue's actual accepted pair is `(true, quantizedArrival)`
on the strict-past event and `(false, 0)` after an earlier overflow. -/
theorem acceptedRecord_eq_if_strictPast (j : Fin p.K) (z : Zplus) :
    RecordedQueueRun.acceptedRecord queue (past z) (cell z).input j =
      if z ∈ G then
        (true, RecordedQueueRun.quantizedArrival queue (cell z).input j)
      else (false, 0) := by
  have hU :=
    ReferenceFirstLiveChronologicalRetainedUpdate.actual_current_stopped_update
      rate rewards C_star C_h q t s hs control0 z
  rcases hU with ⟨hpast, _, henabled, _, _, _, _, _, _, _⟩
  have hG := mem_strictPast_iff_offset_lt_firstOverflow
    rate rewards C_star C_h q t s hs control0 z
  by_cases hz : z ∈ G
  · have hflag : (past z).overflow = false := hpast.mpr (hG.mp hz)
    simp [RecordedQueueRun.acceptedRecord, hz, hflag, henabled]
  · have hn : ¬ currentOffset < firstOverflow z := fun hn => hz (hG.mpr hn)
    cases hflag : (past z).overflow with
    | false => exact (hn (hpast.mp hflag)).elim
    | true =>
      simp [RecordedQueueRun.acceptedRecord, hz, hflag]

/-- On the retained branch the literal accepted real equals the actual
quantized arrival divided by the source scale. -/
theorem acceptedA_eq_quantizedArrival_of_mem_G (j : Fin p.K) (z : Zplus)
    (hz : z ∈ G) :
    acceptedA rate rewards C_star C_h q t s hs control0 j z =
      (RecordedQueueRun.quantizedArrival queue (cell z).input j : ℝ) / scale := by
  rw [acceptedA]
  have hpair := acceptedRecord_eq_if_strictPast
    rate rewards C_star C_h q t s hs control0 j z
  rw [ite_eq_left hz] at hpair
  rw [hpair]
  rfl

/-- Off the retained branch the literal accepted record has zero arrival. -/
theorem acceptedA_eq_zero_of_not_mem_G (j : Fin p.K) (z : Zplus)
    (hz : z ∉ G) :
    acceptedA rate rewards C_star C_h q t s hs control0 j z = 0 := by
  rw [acceptedA]
  have hpair := acceptedRecord_eq_if_strictPast
    rate rewards C_star C_h q t s hs control0 j z
  rw [ite_eq_right hz] at hpair
  rw [hpair]
  simp [RecordedQueueRun.acceptedArrival]

/-- The actual accepted-record projection is pointwise L's strict-past
retained arrival on the same source point. -/
theorem acceptedA_eq_retainedA (j : Fin p.K) (z : Zplus) :
    acceptedA rate rewards C_star C_h q t s hs control0 j z =
      ReferenceFirstLiveAllArmConditionalMoments.retainedA
        rate rewards C_star C_h q t s hs control0 j z := by
  by_cases hz : z ∈ G
  · rw [acceptedA_eq_quantizedArrival_of_mem_G
      rate rewards C_star C_h q t s hs control0 j z hz]
    simp [ReferenceFirstLiveAllArmConditionalMoments.retainedA,
      ReferenceFirstLiveAllArmSourceMoments.a, hz]
  · rw [acceptedA_eq_zero_of_not_mem_G
      rate rewards C_star C_h q t s hs control0 j z hz]
    simp [ReferenceFirstLiveAllArmConditionalMoments.retainedA, hz]

/-- The accepted projection has the same literal pointwise envelope as the
retained source arrival, including the zero branch. -/
theorem acceptedA_pointwise_bounds (j : Fin p.K) (z : Zplus) :
    0 ≤ acceptedA rate rewards C_star C_h q t s hs control0 j z ∧
      acceptedA rate rewards C_star C_h q t s hs control0 j z ≤
        1 / ReferenceFirstLiveSourceSavedMoments.beta rate := by
  rw [acceptedA_eq_retainedA rate rewards C_star C_h q t s hs control0 j z]
  exact ReferenceFirstLiveAllArmConditionalMoments.retainedA_pointwise_bounds
    rate rewards C_star C_h q t s hs control0 j z

/-- Ambient Borel measurability of the literal accepted-record projection. -/
theorem measurable_acceptedA (j : Fin p.K) :
    Measurable (fun z : Zplus =>
      acceptedA rate rewards C_star C_h q t s hs control0 j z) := by
  have hfun : (fun z : Zplus =>
      acceptedA rate rewards C_star C_h q t s hs control0 j z) =
      ReferenceFirstLiveAllArmConditionalMoments.retainedA
        rate rewards C_star C_h q t s hs control0 j :=
    funext fun z => acceptedA_eq_retainedA rate rewards C_star C_h q t s hs control0 j z
  rw [hfun]
  exact ReferenceFirstLiveAllArmConditionalMoments.measurable_retainedA
    rate rewards C_star C_h q t s hs control0 j

/-- Ambient Borel measurability of the square of the literal accepted
projection. -/
theorem measurable_acceptedA_sq (j : Fin p.K) :
    Measurable (fun z : Zplus =>
      (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) := by
  have hfun : (fun z : Zplus =>
      (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) =
      (fun z : Zplus =>
        (ReferenceFirstLiveAllArmConditionalMoments.retainedA
          rate rewards C_star C_h q t s hs control0 j z) ^ 2) := by
    funext z
    rw [acceptedA_eq_retainedA rate rewards C_star C_h q t s hs control0 j z]
  rw [hfun]
  exact ReferenceFirstLiveAllArmConditionalMoments.measurable_retainedA_sq
    rate rewards C_star C_h q t s hs control0 j

/-- Integrability of the actual accepted-record projection under the same
finite, unnormalized `muPlus` measure. -/
theorem integrable_acceptedA (j : Fin p.K) :
    Integrable (fun z : Zplus =>
      acceptedA rate rewards C_star C_h q t s hs control0 j z) muPlus := by
  have hfun : (fun z : Zplus =>
      acceptedA rate rewards C_star C_h q t s hs control0 j z) =
      ReferenceFirstLiveAllArmConditionalMoments.retainedA
        rate rewards C_star C_h q t s hs control0 j :=
    funext fun z => acceptedA_eq_retainedA rate rewards C_star C_h q t s hs control0 j z
  rw [hfun]
  exact ReferenceFirstLiveAllArmConditionalMoments.integrable_retainedA
    rate rewards C_star C_h q t s hs control0 j

/-- Integrability of the square of the actual accepted-record projection. -/
theorem integrable_acceptedA_sq (j : Fin p.K) :
    Integrable (fun z : Zplus =>
      (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) muPlus := by
  have hfun : (fun z : Zplus =>
      (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) =
      (fun z : Zplus =>
        (ReferenceFirstLiveAllArmConditionalMoments.retainedA
          rate rewards C_star C_h q t s hs control0 j z) ^ 2) := by
    funext z
    rw [acceptedA_eq_retainedA rate rewards C_star C_h q t s hs control0 j z]
  rw [hfun]
  exact ReferenceFirstLiveAllArmConditionalMoments.integrable_retainedA_sq
    rate rewards C_star C_h q t s hs control0 j

/-- First conditional moment of the actual accepted arrival, with L's masked
first coefficient and the original `muPlus`/`Fplus`. -/
theorem acceptedA_condExp_firstMoment (j : Fin p.K) :
    muPlus[(fun z : Zplus =>
      acceptedA rate rewards C_star C_h q t s hs control0 j z) | Fplus] =ᵐ[muPlus]
      Set.indicator G (fun z : Zplus =>
        ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus
          rate rewards C_star C_h q t s hs control0 j z) := by
  have hfun : (fun z : Zplus =>
      acceptedA rate rewards C_star C_h q t s hs control0 j z) =
      ReferenceFirstLiveAllArmConditionalMoments.retainedA
        rate rewards C_star C_h q t s hs control0 j :=
    funext fun z => acceptedA_eq_retainedA rate rewards C_star C_h q t s hs control0 j z
  rw [hfun]
  exact ReferenceFirstLiveAllArmConditionalMoments.retainedA_condExp_firstMoment
    rate rewards C_star C_h q t s hs control0 j

/-- Square conditional moment of the actual accepted arrival. Its coefficient
is `xi * v^2`, as inherited from L, not a square of the first coefficient. -/
theorem acceptedA_condExp_secondMoment (j : Fin p.K) :
    muPlus[(fun z : Zplus =>
      (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) | Fplus] =ᵐ[muPlus]
      Set.indicator G (fun z : Zplus =>
        ReferenceFirstLiveAllArmPrefixAdaptation.secondCoefficientPlus
          rate rewards C_star C_h q t s hs control0 j z) := by
  have hfun : (fun z : Zplus =>
      (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) =
      (fun z : Zplus =>
        (ReferenceFirstLiveAllArmConditionalMoments.retainedA
          rate rewards C_star C_h q t s hs control0 j z) ^ 2) := by
    funext z
    rw [acceptedA_eq_retainedA rate rewards C_star C_h q t s hs control0 j z]
  rw [hfun]
  exact ReferenceFirstLiveAllArmConditionalMoments.retainedA_condExp_secondMoment
    rate rewards C_star C_h q t s hs control0 j

/-- The first conditional moment is nonnegative almost everywhere. -/
theorem acceptedA_condExp_first_nonneg (j : Fin p.K) :
    0 ≤ᵐ[muPlus]
      muPlus[(fun z : Zplus =>
        acceptedA rate rewards C_star C_h q t s hs control0 j z) | Fplus] := by
  have hce :
      muPlus[(fun z : Zplus =>
        acceptedA rate rewards C_star C_h q t s hs control0 j z) | Fplus] =ᵐ[muPlus]
      muPlus[ReferenceFirstLiveAllArmConditionalMoments.retainedA
        rate rewards C_star C_h q t s hs control0 j | Fplus] := by
    exact (acceptedA_condExp_firstMoment rate rewards C_star C_h q t s hs control0 j).trans
      (ReferenceFirstLiveAllArmConditionalMoments.retainedA_condExp_firstMoment
        rate rewards C_star C_h q t s hs control0 j).symm
  filter_upwards [hce,
    ReferenceFirstLiveAllArmConditionalMoments.retainedA_condExp_first_nonneg
      rate rewards C_star C_h q t s hs control0 j] with z hEq hNonneg
  rw [hEq]
  exact hNonneg

/-- The retained first conditional envelope transfers verbatim to the actual
accepted-record projection, including the signed `rho - xi/(eta*D)` lower
bound and the reward/unit upper bounds. -/
theorem acceptedA_condExp_first_bounds (j : Fin p.K) :
    Set.indicator G (fun z : Zplus =>
      ReferenceFirstLiveAllArmPrefixAdaptation.roundedRewardPlus rewards t j -
        ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus
          rate rewards C_star C_h q t s hs control0 j z / scale) ≤ᵐ[muPlus]
        muPlus[(fun z : Zplus =>
          acceptedA rate rewards C_star C_h q t s hs control0 j z) | Fplus] ∧
    muPlus[(fun z : Zplus =>
      acceptedA rate rewards C_star C_h q t s hs control0 j z) | Fplus] ≤ᵐ[muPlus]
      Set.indicator G (fun _ : Zplus =>
        ReferenceFirstLiveAllArmPrefixAdaptation.roundedRewardPlus rewards t j) ∧
    Set.indicator G (fun _ : Zplus =>
      ReferenceFirstLiveAllArmPrefixAdaptation.roundedRewardPlus rewards t j) ≤ᵐ[muPlus]
        (fun _ : Zplus => 1) := by
  have hce :
      muPlus[(fun z : Zplus =>
        acceptedA rate rewards C_star C_h q t s hs control0 j z) | Fplus] =ᵐ[muPlus]
      muPlus[ReferenceFirstLiveAllArmConditionalMoments.retainedA
        rate rewards C_star C_h q t s hs control0 j | Fplus] := by
    exact (acceptedA_condExp_firstMoment rate rewards C_star C_h q t s hs control0 j).trans
      (ReferenceFirstLiveAllArmConditionalMoments.retainedA_condExp_firstMoment
        rate rewards C_star C_h q t s hs control0 j).symm
  have hL :=
    ReferenceFirstLiveAllArmConditionalMoments.retainedA_condExp_first_bounds
      rate rewards C_star C_h q t s hs control0 j
  refine ⟨?_, ?_, hL.2.2⟩
  · filter_upwards [hce, hL.1] with z hEq hBound
    rw [hEq]
    exact hBound
  · filter_upwards [hce, hL.2.1] with z hEq hBound
    rw [hEq]
    exact hBound

/-- The second conditional moment's nonnegative, `rho^2/xi`, `1/xi`, and
`1/beta` envelopes transfer to the actual accepted-record projection. -/
theorem acceptedA_condExp_second_bounds (j : Fin p.K) :
    0 ≤ᵐ[muPlus]
      muPlus[(fun z : Zplus =>
        (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) | Fplus] ∧
    muPlus[(fun z : Zplus =>
      (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) | Fplus] ≤ᵐ[muPlus]
      Set.indicator G (fun z : Zplus =>
        ReferenceFirstLiveAllArmPrefixAdaptation.rhoSquaredDivRatePlus
          rate rewards C_star C_h q t s hs control0 j z) ∧
    Set.indicator G (fun z : Zplus =>
      ReferenceFirstLiveAllArmPrefixAdaptation.rhoSquaredDivRatePlus
        rate rewards C_star C_h q t s hs control0 j z) ≤ᵐ[muPlus]
      Set.indicator G (fun z : Zplus =>
        1 / ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus
          rate rewards C_star C_h q t s hs control0 j z) ∧
    Set.indicator G (fun z : Zplus =>
      1 / ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus
        rate rewards C_star C_h q t s hs control0 j z) ≤ᵐ[muPlus]
      (fun _ : Zplus =>
        1 / ReferenceFirstLiveSourceSavedMoments.beta rate) := by
  have hce :
      muPlus[(fun z : Zplus =>
        (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) | Fplus] =ᵐ[muPlus]
      muPlus[(fun z : Zplus =>
        (ReferenceFirstLiveAllArmConditionalMoments.retainedA
          rate rewards C_star C_h q t s hs control0 j z) ^ 2) | Fplus] := by
    exact (acceptedA_condExp_secondMoment rate rewards C_star C_h q t s hs control0 j).trans
      (ReferenceFirstLiveAllArmConditionalMoments.retainedA_condExp_secondMoment
        rate rewards C_star C_h q t s hs control0 j).symm
  have hL :=
    ReferenceFirstLiveAllArmConditionalMoments.retainedA_condExp_second_bounds
      rate rewards C_star C_h q t s hs control0 j
  refine ⟨?_, ?_, hL.2.2.1, hL.2.2.2⟩
  · filter_upwards [hce, hL.1] with z hEq hBound
    rw [hEq]
    exact hBound
  · filter_upwards [hce, hL.2.1] with z hEq hBound
    rw [hEq]
    exact hBound

/-- The source normalization denominator is strictly positive. -/
theorem scale_pos : 0 < scale := by
  have hD : (0 : ℝ) < (ConstructorDimensions.D p : ℝ) := by
    exact_mod_cast ConstructorDimensions.D_pos p
  exact mul_pos rate.eta.property hD

/-- On `G`, the integer registers use the exact source capacity and current
quantized arrival supplied by U's actual current update. -/
theorem integer_registers_update_on_G (j : Fin p.K) (z : Zplus)
    (hz : z ∈ G) :
    ((post z).registers j).1 = ((past z).registers j).1 +
        min (4 * rate.n)
          (((past z).registers j).2 +
            RecordedQueueRun.quantizedArrival queue (cell z).input j) ∧
    ((post z).registers j).2 =
      ((past z).registers j).2 +
        RecordedQueueRun.quantizedArrival queue (cell z).input j -
          min (4 * rate.n)
            (((past z).registers j).2 +
              RecordedQueueRun.quantizedArrival queue (cell z).input j) := by
  have hU :=
    ReferenceFirstLiveChronologicalRetainedUpdate.actual_current_stopped_update
      rate rewards C_star C_h q t s hs control0 z
  rcases hU with ⟨_, _, _, _, _, _, hservice, _, _, _⟩
  exact ⟨congrArg Prod.fst (hservice j
      (mem_strictPast_iff_offset_lt_firstOverflow
        rate rewards C_star C_h q t s hs control0 z |>.mp hz)),
    congrArg Prod.snd (hservice j
      (mem_strictPast_iff_offset_lt_firstOverflow
        rate rewards C_star C_h q t s hs control0 z |>.mp hz))⟩

/-- Once the strict-past run has stopped, the actual numerical post-registers
are unchanged and the accepted pair is exactly `(false, 0)`. -/
theorem integer_registers_unchanged_off_G (j : Fin p.K) (z : Zplus)
    (hz : z ∉ G) :
    (post z).registers j = (past z).registers j ∧
      RecordedQueueRun.acceptedRecord queue (past z) (cell z).input j = (false, 0) := by
  have hU :=
    ReferenceFirstLiveChronologicalRetainedUpdate.actual_current_stopped_update
      rate rewards C_star C_h q t s hs control0 z
  rcases hU with ⟨_, _, _, _, _, _, _, _, _, hoff⟩
  have hG := mem_strictPast_iff_offset_lt_firstOverflow
    rate rewards C_star C_h q t s hs control0 z
  have hn : firstOverflow z ≤ currentOffset :=
    Nat.le_of_not_gt (fun hn => hz (hG.mpr hn))
  exact hoff hn j

/-- The chronological score is monotone across the current enabled update,
including the absorbing no-op branch. -/
theorem score_monotone (j : Fin p.K) (z : Zplus) :
    ((past z).registers j).1 ≤ ((post z).registers j).1 := by
  by_cases hz : z ∈ G
  · rw [(integer_registers_update_on_G rate rewards C_star C_h q t s hs control0
      j z hz).1]
    exact Nat.le_add_right _ _
  · rw [(integer_registers_unchanged_off_G
      rate rewards C_star C_h q t s hs control0 j z hz).1]

/-- Exact integer score service on `G`; the increment is capped at `4*n`.
The zero-arrival case is retained by the existing transition formula. -/
theorem integer_score_service_on_G (j : Fin p.K) (z : Zplus)
    (hz : z ∈ G) :
    ((post z).registers j).1 - ((past z).registers j).1 =
      min (4 * rate.n)
        (((past z).registers j).2 +
          RecordedQueueRun.quantizedArrival queue (cell z).input j) := by
  rw [(integer_registers_update_on_G
    rate rewards C_star C_h q t s hs control0 j z hz).1]
  exact Nat.add_sub_cancel_left _ _

/-- Exact integer total conservation at the actual current record, using the
existing `RecordedQueueRun.transition_total` API and U's update identity. -/
theorem integer_total_conservation (j : Fin p.K) (z : Zplus) :
    ((post z).registers j).1 + ((post z).registers j).2 =
      ((past z).registers j).1 + ((past z).registers j).2 +
        RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord queue (past z) (cell z).input j) := by
  by_cases hz : z ∈ G
  · have hU :=
      ReferenceFirstLiveChronologicalRetainedUpdate.actual_current_stopped_update
        rate rewards C_star C_h q t s hs control0 z
    rcases hU with ⟨_, _, _, _, htransition, _, _, _, _, _⟩
    have htotal :
        (QueueReplay.transition (4 * rate.n) ((past z).registers j)
          (RecordedQueueRun.acceptedRecord queue (past z) (cell z).input j)).1 +
        (QueueReplay.transition (4 * rate.n) ((past z).registers j)
          (RecordedQueueRun.acceptedRecord queue (past z) (cell z).input j)).2 =
          ((past z).registers j).1 + ((past z).registers j).2 +
            RecordedQueueRun.acceptedArrival
              (RecordedQueueRun.acceptedRecord queue (past z) (cell z).input j) := by
      simpa only using RecordedQueueRun.transition_total (4 * rate.n)
        ((past z).registers j)
        (RecordedQueueRun.acceptedRecord queue (past z) (cell z).input j)
    rw [htransition]
    exact htotal
  · have hsame := integer_registers_unchanged_off_G
      rate rewards C_star C_h q t s hs control0 j z hz
    rw [hsame.1, hsame.2]
    rfl

private theorem normalized_conservation_of_nat
    (score₀ score₁ backlog₀ backlog₁ arrival : ℕ) (den : ℝ)
    (hscore : score₀ ≤ score₁)
    (htotal : score₁ + backlog₁ = score₀ + backlog₀ + arrival) :
    (backlog₁ : ℝ) / den =
      (backlog₀ : ℝ) / den + (arrival : ℝ) / den -
        ((score₁ - score₀ : ℕ) : ℝ) / den := by
  have htotalR : (score₁ : ℝ) + (backlog₁ : ℝ) =
      (score₀ : ℝ) + (backlog₀ : ℝ) + (arrival : ℝ) := by
    exact_mod_cast htotal
  have hscoreR : ((score₁ - score₀ : ℕ) : ℝ) =
      (score₁ : ℝ) - (score₀ : ℝ) := Nat.cast_sub hscore
  have hbacklogR : (backlog₁ : ℝ) =
      (backlog₀ : ℝ) + (arrival : ℝ) - ((score₁ - score₀ : ℕ) : ℝ) := by
    rw [hscoreR]
    linarith
  calc
    (backlog₁ : ℝ) / den =
        ((backlog₀ : ℝ) + (arrival : ℝ) -
          ((score₁ - score₀ : ℕ) : ℝ)) / den := by rw [hbacklogR]
    _ = (backlog₀ : ℝ) / den + (arrival : ℝ) / den -
          ((score₁ - score₀ : ℕ) : ℝ) / den := by
      rw [sub_div, add_div]

/-- The real queue conservation identity for the actual accepted-record
projection and the normalized chronological service. -/
theorem normalized_queue_conservation (j : Fin p.K) (z : Zplus) :
    backlogAfter rate rewards C_star C_h q t s hs control0 j z =
      backlogBefore rate rewards C_star C_h q t s hs control0 j z +
        acceptedA rate rewards C_star C_h q t s hs control0 j z -
          service rate rewards C_star C_h q t s hs control0 j z := by
  exact normalized_conservation_of_nat
    (((past z).registers j).1) (((post z).registers j).1)
    (((past z).registers j).2) (((post z).registers j).2)
    (RecordedQueueRun.acceptedArrival
      (RecordedQueueRun.acceptedRecord queue (past z) (cell z).input j)) scale
    (score_monotone rate rewards C_star C_h q t s hs control0 j z)
    (integer_total_conservation rate rewards C_star C_h q t s hs control0 j z)

/-- The natural residual queue after capped service is the positive part of
the excess over capacity, expressed with `max`. -/
private theorem capped_residual_eq_max (x : ℝ) :
    x - min 4 x = max (x - 4) 0 := by
  by_cases h : x ≤ 4
  · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · have h4 : 4 ≤ x := le_of_not_ge h
    rw [min_eq_left h4, max_eq_left (sub_nonneg.mpr h4)]

private theorem capacity_div_scale :
    ((4 * rate.n : ℕ) : ℝ) / scale = 4 := by
  have hscale : (rate.n : ℝ) = scale := rate.n_scale
  have hden : scale ≠ 0 :=
    (scale_pos rate).ne'
  rw [Nat.cast_mul, Nat.cast_ofNat, hscale]
  exact mul_div_cancel_right₀ 4 hden

private theorem currentTotal_div_scale (j : Fin p.K) (z : Zplus)
    (hz : z ∈ G) :
    ((((past z).registers j).2 +
      RecordedQueueRun.quantizedArrival queue (cell z).input j : ℕ) : ℝ) / scale =
      backlogBefore rate rewards C_star C_h q t s hs control0 j z +
        acceptedA rate rewards C_star C_h q t s hs control0 j z := by
  calc
    _ = ((past z).registers j).2 / scale +
        (RecordedQueueRun.quantizedArrival queue (cell z).input j : ℝ) / scale := by
      rw [Nat.cast_add, add_div]
    _ = backlogBefore rate rewards C_star C_h q t s hs control0 j z +
        acceptedA rate rewards C_star C_h q t s hs control0 j z := by
      rw [← acceptedA_eq_quantizedArrival_of_mem_G
        rate rewards C_star C_h q t s hs control0 j z hz]
      rfl

/-- On `G`, normalized service is the usual capped service. -/
theorem service_eq_min_on_G (j : Fin p.K) (z : Zplus) (hz : z ∈ G) :
    service rate rewards C_star C_h q t s hs control0 j z =
      min 4 (backlogBefore rate rewards C_star C_h q t s hs control0 j z +
        acceptedA rate rewards C_star C_h q t s hs control0 j z) := by
  have hserved := integer_score_service_on_G
    rate rewards C_star C_h q t s hs control0 j z hz
  calc
    service rate rewards C_star C_h q t s hs control0 j z =
        ((min (4 * rate.n)
          (((past z).registers j).2 +
            RecordedQueueRun.quantizedArrival queue (cell z).input j) : ℕ) : ℝ) /
          scale := by
      rw [service, hserved]
    _ = min (((4 * rate.n : ℕ) : ℝ) / scale)
          (((((past z).registers j).2 +
            RecordedQueueRun.quantizedArrival queue (cell z).input j : ℕ) : ℝ) /
            scale) := by
      simpa only [Nat.cast_min] using
        (min_div_div_right (scale_pos rate).le
          ((4 * rate.n : ℕ) : ℝ)
          ((((past z).registers j).2 +
            RecordedQueueRun.quantizedArrival queue (cell z).input j : ℕ) : ℝ)).symm
    _ = min 4 (backlogBefore rate rewards C_star C_h q t s hs control0 j z +
          acceptedA rate rewards C_star C_h q t s hs control0 j z) := by
      rw [capacity_div_scale rate,
        currentTotal_div_scale rate rewards C_star C_h q t s hs control0 j z hz]

/-- Off `G`, the stopped analytical registers and the accepted record are
unchanged/false-zero. In particular, this theorem makes no queue recurrence
claim on an already-stopped state. -/
theorem stopped_queue_noop_off_G (j : Fin p.K) (z : Zplus) (hz : z ∉ G) :
    (post z).registers j = (past z).registers j ∧
      service rate rewards C_star C_h q t s hs control0 j z = 0 ∧
      backlogAfter rate rewards C_star C_h q t s hs control0 j z =
        backlogBefore rate rewards C_star C_h q t s hs control0 j z ∧
      RecordedQueueRun.acceptedRecord queue (past z) (cell z).input j = (false, 0) := by
  obtain ⟨hregs, hrecord⟩ := integer_registers_unchanged_off_G
    rate rewards C_star C_h q t s hs control0 j z hz
  refine ⟨hregs, ?_, ?_, hrecord⟩
  · simp [service, hregs]
  · simp [backlogAfter, backlogBefore, hregs]

/-- The normalized service always lies in `[0,4]`; on an enabled zero-arrival
cell it may still be positive because existing backlog is served. -/
theorem service_bounds (j : Fin p.K) (z : Zplus) :
    0 ≤ service rate rewards C_star C_h q t s hs control0 j z ∧
      service rate rewards C_star C_h q t s hs control0 j z ≤ 4 := by
  by_cases hz : z ∈ G
  · rw [service_eq_min_on_G rate rewards C_star C_h q t s hs control0 j z hz]
    have hback : 0 ≤ backlogBefore rate rewards C_star C_h q t s hs control0 j z := by
      dsimp [backlogBefore]
      exact div_nonneg (Nat.cast_nonneg _) (scale_pos rate).le
    have happ : 0 ≤ acceptedA rate rewards C_star C_h q t s hs control0 j z :=
      (acceptedA_pointwise_bounds rate rewards C_star C_h q t s hs control0 j z).1
    refine ⟨le_min (by norm_num) (add_nonneg hback happ), ?_⟩
    exact min_le_left _ _
  · rw [(stopped_queue_noop_off_G rate rewards C_star C_h q t s hs control0 j z hz).2.1]
    norm_num

/-- Zero accepted arrivals do not suppress service of an existing backlog. -/
theorem service_pos_on_G_of_zero_acceptedA (j : Fin p.K) (z : Zplus)
    (hz : z ∈ G)
    (hzero : acceptedA rate rewards C_star C_h q t s hs control0 j z = 0)
    (hback : 0 < backlogBefore rate rewards C_star C_h q t s hs control0 j z) :
    0 < service rate rewards C_star C_h q t s hs control0 j z := by
  rw [service_eq_min_on_G rate rewards C_star C_h q t s hs control0 j z hz,
    hzero, add_zero]
  exact lt_min (by norm_num) hback

/-- The normalized backlog after the current retained update is the positive
part of the accepted total above capacity. -/
theorem backlogAfter_eq_max_on_G (j : Fin p.K) (z : Zplus) (hz : z ∈ G) :
    backlogAfter rate rewards C_star C_h q t s hs control0 j z =
      max (backlogBefore rate rewards C_star C_h q t s hs control0 j z +
        acceptedA rate rewards C_star C_h q t s hs control0 j z - 4) 0 := by
  rw [normalized_queue_conservation rate rewards C_star C_h q t s hs control0 j z,
    service_eq_min_on_G rate rewards C_star C_h q t s hs control0 j z hz]
  apply capped_residual_eq_max

/-- Normalized score increment on the actual enabled cell is the literal
integer service divided by `eta * D`. -/
theorem service_eq_score_difference (j : Fin p.K) (z : Zplus) :
    service rate rewards C_star C_h q t s hs control0 j z =
      (((post z).registers j).1 - ((past z).registers j).1 : ℕ) / scale := rfl

/-- The physical numerical run still executes the original current record
after the analytical queue has stopped. This endpoint is unconditional in
the numerical overflow comparison. -/
theorem actual_current_run_endpoint (z : Zplus) :
    (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate z.val.val rewards C_star C_h z.val.property.2.1
      (ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s)
      (ReferenceFirstLiveSourceCellReadout.source_current_span
        rate rewards C_star C_h q t s hs control0 z)).finalState =
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val).output.next :=
  ReferenceFirstLiveChronologicalRetainedUpdate.actual_current_run_endpoint
    rate rewards C_star C_h q t s hs control0 z

/-- Before the first overflow, the actual post queue and normalized service
join to the same original current record's physical endpoint. The existential
physical witnesses, selected payload, initial zero base, installation birth,
occupied follower fields, inherited buffer emissions, and unoccupied virtual
replay are all produced by U on this exact source point. The physical run's
current endpoint remains an unconditional conjunct. -/
theorem actual_current_physical_endpoint_service_join (z : Zplus) :
    let n := t.val - s
    let count := ReferenceFirstLiveSourceCellReadout.sourceCurrentCount t s
    let span := ReferenceFirstLiveSourceCellReadout.source_current_span
      rate rewards C_star C_h q t s hs control0 z
    let source := z.val.val
    let κ := UnstoppedRecordedQueueComparison.firstOverflowPrefix
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (ReferenceFirstLiveSourceCellReadout.cells
        rate rewards C_star C_h q t s hs control0 z)
    let cells := ReferenceFirstLiveSourceCellReadout.cells
      rate rewards C_star C_h q t s hs control0 z
    let pastRun := RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) (cells.take n)
    let postRun := RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) (cells.take (n + 1))
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h z.val.property.2.1 count span
    E.finalState =
        (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z.val).output.next ∧
    (n < κ →
      ∃ hprefix : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
          + (n + 1) ≤ p.T,
      ∃ boundary : ReferenceActivePhysicalHorizon.Run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h
          z.val.property.2.1),
      boundary = ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h
          z.val.property.2.1)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
        (n + 1) hprefix
        (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h
          z.val.property.2.1).activeAtStart ∧
      ∃ r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
      ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters r,
      ∃ base : Fin (p.m - 1) → ℕ,
        E.finalState = boundary.finalState ∧
        boundary.finalState.coordinator = .live r owned base ∧
        r.payload.sigma.val = s ∧ r.payload.n = rate.n ∧
        (∀ i, base i = 0) ∧
        (ReferenceFirstLiveSourceCellReadout.cell
          rate rewards C_star C_h q t s hs control0 z).selected.view.payload = r.payload ∧
        (∃ birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          birth ∈ E.records ∧
          ReferenceAssignmentPayloadPersistence.InstallationBirth birth r.payload ∧
          birth.input.time.val = s) ∧
        (∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
          (r.complementScores a, owned.queue a) = postRun.registers a.1 ∧
          owned.previousService a = (postRun.registers a.1).1 - (pastRun.registers a.1).1 ∧
          ((owned.previousService a : ℝ) / scale =
            service rate rewards C_star C_h q t s hs control0 a.1 z)) ∧
        (∀ i : Fin (p.m - 1),
          ∃ sb mb, E.finalState.followers i = .ordinary sb mb ∧
            ((sb.status ≠ .unoccupied →
              sb.lastDown = some (r.payload.downRecord i) ∧
              (sb.S, sb.backlog) = postRun.registers (r.payload.assignment.assigned i) ∧
              sb.delta = (postRun.registers (r.payload.assignment.assigned i)).1 -
                (pastRun.registers (r.payload.assignment.assigned i)).1 ∧
              ∃ j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
                  rate source rewards C_star C_h z.val.property.2.1 count span).length,
                j.val < n + 1 ∧
                ReferenceAcceptedUpFollowerHistory.RetainedDown
                  (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
                    rate source rewards C_star C_h z.val.property.2.1 count span)[j.val]
                  i (r.payload.downRecord i) ∧
              (sb.delta : ℝ) / scale =
                service rate rewards C_star C_h q t s hs control0
                  (r.payload.assignment.assigned i) z) ∧
             (sb.status = .unoccupied →
              sb.lastDown = none ∧ sb.S = 0 ∧ sb.delta = 0 ∧ sb.backlog = 0 ∧
              sb.buffer =
                ((ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
                  rate source rewards C_star C_h z.val.property.2.1).followers i).buffer ++
                (E.records.take (n + 1)).flatMap
                  (ReferenceFollowerBufferProvenance.logEmission i) ∧
              ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                E.records i (n + 1) (r.payload.downRecord i) (n + 1) =
                ((cells.take (n + 1)).map fun c =>
                  (c.enabled, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
                    (r.payload.assignment.assigned i))) ∧
              QueueReplay.replay (4 * rate.n) (0, 0)
                (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                  E.records i (n + 1) (r.payload.downRecord i) (n + 1)) =
                postRun.registers (r.payload.assignment.assigned i))))) := by
  classical
  intro n count span source κ cells pastRun postRun E
  have hU :=
    ReferenceFirstLiveChronologicalRetainedUpdate.actual_current_stopped_physical_endpoint
      rate rewards C_star C_h q t s hs control0 z
  rcases hU with ⟨_, _, _, _, hphysical⟩
  refine ⟨?_, ?_⟩
  · exact actual_current_run_endpoint rate rewards C_star C_h q t s hs control0 z
  · intro hnκ
    rcases hphysical hnκ with
      ⟨hprefix, boundary, hboundary, r, owned, base, hstate, hendpoint, hLive,
        hsigma, hrate, hbase, hpayload, hbirth, hcomplement, hfollowers⟩
    refine ⟨hprefix, boundary, hboundary, r, owned, base,
      hstate, hLive, hsigma, hrate, hbase, hpayload, hbirth, ?_, ?_⟩
    · intro a
      rcases hcomplement a with ⟨hregisters, hprevious⟩
      refine ⟨hregisters, hprevious, ?_⟩
      rw [hprevious]
      rfl
    · intro i
      rcases hfollowers i with ⟨sb, mb, hordinary, hoccupied, hunoccupied⟩
      refine ⟨sb, mb, hordinary, ?_, hunoccupied⟩
      intro hstatus
      rcases hoccupied hstatus with ⟨hlast, hregisters, hdelta, hretained⟩
      rcases hretained with ⟨j, hj, hdown⟩
      refine ⟨hlast, hregisters, hdelta, j, hj, hdown, ?_⟩
      rw [hdelta]
      rfl

end Bandits.Support.ReferenceFirstLiveAllArmAcceptedConditionalMoments

end
