/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaunchRowLaw
public import Bandits.Support.FirstAssignmentLaunch

/-!
# The first assignment at the actual reference launch

For each nonterminal actual reference launch index, this module takes the
entire assignment vector from the original selected complete row at that
calendar time and evaluates the existing first-assignment constructor once.
It derives its unnormalized vector and slow-set laws from the accepted
actual-launch stopping-time factorization. The strict-past side input keeps the
entire original private array.

The source launch is the existing `ReferenceInitializationRun.launchRound`.
The `T + 1` sentinel has an empty future and no `Fin T` assignment coordinate,
so this module makes no first-start call there. These results describe the
literal first-start operation before complete row revelation. They do not
construct a chronological physical coordinator, a later adaptive start law,
or a source coupling.

Sources: `sources/zip4/manuscript/06_interruptions.tex:46-61,391-426`,
`sources/zip4/manuscript/07_public_setup.tex:123-164`, and
`sources/zip4/manuscript/appendix_b_communication.tex:786-798`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.CompleteRowStoppingLaw
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.CanonicalAssignmentVector
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceLaunchRowLaw
open scoped ENNReal

namespace Bandits.Support.ReferenceLaunchAssignmentLaw

abbrev Parameters := ConstructorDimensions.Parameters
abbrev SideInput (p : Parameters) := ReferenceLaunchRowLaw.SideInput p
abbrev LaunchIndex (p : Parameters) := Fin (p.T + 1)
abbrev AssignmentVector (p : Parameters) :=
  Fin (p.K + 1) → ContinuousControlSlice.Scalar

local instance slowSetMeasurableSpace (K m : ℕ) :
    MeasurableSpace (CanonicalOrientedSetLaw.SlowSet K m) := ⊤

/-- The calendar source coordinate at a nonterminal stopping index. -/
def launchSourceIndex (p : Parameters) (σ : LaunchIndex p) (hσ : σ.val < p.T) :
    FutureIndex p σ :=
  ⟨⟨σ.val, hσ⟩, by
    change ¬ σ.val < σ.val
    exact Nat.lt_irrefl _⟩

/-- The whole selected `TimeControl` at calendar coordinate `σ.val`, read from
the original complete row. -/
def originalTimeControlAt (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (row : CompletePublicTable.CompleteRow p) :
    ContinuousLearningRows.TimeControl p :=
  (calendarizeRow p row ⟨σ.val, hσ⟩).2

/-- The full scalar `Slice` of the original selected control at the launch
calendar coordinate. -/
def originalSliceAt (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (row : CompletePublicTable.CompleteRow p) :
    ContinuousControlSlice.Slice p.m p.K :=
  (originalTimeControlAt p σ hσ row).1

/-- All `K + 1` original assignment scalars, including the final orientation
coordinate, in the constructor's source order. -/
def originalAssignmentVectorAt (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (row : CompletePublicTable.CompleteRow p) :
    AssignmentVector p :=
  ContinuousControlSlice.assignmentVector (originalSliceAt p σ hσ row)

/-- The actual candidate first-assignment input at a fixed nonterminal
stopping index. The source cap proof and exact integer identity are explicit
inputs; no assignment coordinates are sampled or replaced here. -/
def firstInputAtSigma (p : Parameters) (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (row : CompletePublicTable.CompleteRow p) :
    FirstAssignmentLaunch.Input p eta where
  eta_le_source_cap := hcap
  n := n
  n_eq_eta_mul_D := hn
  sigma := ⟨σ.val, hσ⟩
  coordinates := originalAssignmentVectorAt p σ hσ row

/-- The existing first-assignment operation applied once to the exact
original-coordinate input at this fixed launch index. -/
noncomputable def actualStartAtSigma (p : Parameters) (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (row : CompletePublicTable.CompleteRow p) :
    FirstAssignmentLaunch.Start p eta :=
  (firstInputAtSigma p eta hcap n hn σ hσ row).start

/-- Projection of the future calendar vector to its actual `σ.val`
coordinate, then to the full assignment vector. -/
def futureAssignmentVectorAtSigma (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (future : FutureArray p σ) : AssignmentVector p :=
  ContinuousControlSlice.assignmentVector ((future (launchSourceIndex p σ hσ)).2.1)

/-- The existing unit-weight canonical slow sampler applied to the complete
future assignment vector. -/
noncomputable def futureSlowSetAtSigma (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (future : FutureArray p σ) : SlowSet p.K p.m :=
  CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
    (fun _ => 1) (fun _ => 1) (by intro i; norm_num) (by intro i; norm_num)
    (futureAssignmentVectorAtSigma p σ hσ future)

/-- The actual slow set produced by the one existing first-start call. -/
noncomputable def actualSlowSetAtSigma (p : Parameters) (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (row : CompletePublicTable.CompleteRow p) : SlowSet p.K p.m :=
  (actualStartAtSigma p eta hcap n hn σ hσ row).slowSet

/-- Measurability of the selected whole control coordinate in the original
complete row. -/
theorem measurable_originalTimeControlAt (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) :
    Measurable (originalTimeControlAt p σ hσ) := by
  change Measurable (fun row : CompletePublicTable.CompleteRow p =>
    (calendarizeRow p row ⟨σ.val, hσ⟩).2)
  exact measurable_snd.comp
    ((measurable_pi_apply (⟨σ.val, hσ⟩ : Fin p.T)).comp
      (CompleteRowStoppingLaw.calendarizeRowEquiv p).measurable)

/-- Measurability of the selected entire scalar slice. -/
theorem measurable_originalSliceAt (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) : Measurable (originalSliceAt p σ hσ) := by
  exact measurable_fst.comp (measurable_originalTimeControlAt p σ hσ)

/-- Measurability of all `K + 1` original assignment labels. -/
theorem measurable_originalAssignmentVectorAt (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T) :
    Measurable (originalAssignmentVectorAt p σ hσ) := by
  exact (ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp
    (measurable_originalSliceAt p σ hσ)

/-- The vector map on the original product of the complete private array and
the selected complete row. -/
def actualAssignmentVectorOnSource (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (z : SideInput p × CompletePublicTable.CompleteRow p) :
    AssignmentVector p :=
  originalAssignmentVectorAt p σ hσ z.2

/-- Measurability of the actual product-space assignment-vector map. -/
theorem measurable_actualAssignmentVectorOnSource (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T) :
    Measurable (actualAssignmentVectorOnSource p σ hσ) := by
  exact (measurable_originalAssignmentVectorAt p σ hσ).comp measurable_snd

/-- Every assignment label is read from the same original slice; `r = K` is
the source orientation scalar. -/
theorem originalAssignmentVectorAt_apply (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (row : CompletePublicTable.CompleteRow p)
    (r : Fin (p.K + 1)) :
    originalAssignmentVectorAt p σ hσ row r =
      (originalSliceAt p σ hσ row) (ContinuousControlSlice.Label.assign r) := rfl

/-- The full future assignment vector is measurable. -/
theorem measurable_futureAssignmentVectorAtSigma (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T) :
    Measurable (futureAssignmentVectorAtSigma p σ hσ) := by
  exact (ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp
    (measurable_fst.comp
      (measurable_snd.comp
        (measurable_pi_apply (launchSourceIndex p σ hσ))))

/-- The selected future calendar coordinate, complete control, scalar slice,
and assignment vector preserve their existing product laws. -/
theorem measurePreserving_futureAssignmentVectorAtSigma (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T) :
    MeasurePreserving (futureAssignmentVectorAtSigma p σ hσ)
      (CompleteRowStoppingLaw.futureArrayLaw p σ)
      (ContinuousControlSlice.assignmentLaw p.K) := by
  let i := launchSourceIndex p σ hσ
  have hEval : MeasurePreserving (fun f : FutureArray p σ => f i)
      (CompleteRowStoppingLaw.futureArrayLaw p σ)
      (CompleteRowStoppingLaw.calendarEntryLaw p) := by
    change MeasurePreserving (Function.eval i)
      (Measure.pi (fun _ : FutureIndex p σ => CompleteRowStoppingLaw.calendarEntryLaw p))
      (CompleteRowStoppingLaw.calendarEntryLaw p)
    exact measurePreserving_eval _ i
  have hTime : MeasurePreserving (Prod.snd :
      CompleteRowStoppingLaw.CalendarEntry p → ContinuousLearningRows.TimeControl p)
      (CompleteRowStoppingLaw.calendarEntryLaw p)
      (ContinuousLearningRows.timeControlLaw p) := by
    exact measurePreserving_snd
  change MeasurePreserving
    (fun future : FutureArray p σ =>
      ContinuousControlSlice.assignmentVector ((future i).2.1))
    (CompleteRowStoppingLaw.futureArrayLaw p σ)
    (ContinuousControlSlice.assignmentLaw p.K)
  exact (ContinuousControlSlice.measurePreserving_assignmentVector p.m p.K).comp
    ((ContinuousLearningRows.measurePreserving_slice p).comp
      (hTime.comp hEval))

/-- The vector projection of the complete future calendar has the existing
product-uniform assignment law. -/
theorem futureAssignmentVectorAtSigma_map (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T) :
    (CompleteRowStoppingLaw.futureArrayLaw p σ).map
      (futureAssignmentVectorAtSigma p σ hσ) =
      ContinuousControlSlice.assignmentLaw p.K :=
  (measurePreserving_futureAssignmentVectorAtSigma p σ hσ).map_eq

/-- The future slow-set projection is measurable. -/
theorem measurable_futureSlowSetAtSigma (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) : Measurable (futureSlowSetAtSigma p σ hσ) := by
  exact (CanonicalAssignmentVector.measurable_canonicalSlowSampler
    p.two_le_m p.m_lt_K (fun _ => 1) (fun _ => 1)
    (by intro i; norm_num) (by intro i; norm_num)).comp
      (measurable_futureAssignmentVectorAtSigma p σ hσ)

/-- The future slow-set marginal is the accepted canonical PMF at unit
current and anchor weights. -/
theorem futureSlowSetAtSigma_map (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) :
    (CompleteRowStoppingLaw.futureArrayLaw p σ).map
      (futureSlowSetAtSigma p σ hσ) =
      (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
        p.two_le_m p.m_lt_K (by intro _i; norm_num) (by intro _i; norm_num)).toMeasure := by
  let sampler := CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
    (fun _ => 1) (fun _ => 1) (by intro _i; norm_num) (by intro _i; norm_num)
  calc
    (CompleteRowStoppingLaw.futureArrayLaw p σ).map (futureSlowSetAtSigma p σ hσ) =
        ((CompleteRowStoppingLaw.futureArrayLaw p σ).map
          (futureAssignmentVectorAtSigma p σ hσ)).map sampler := by
            rw [Measure.map_map (CanonicalAssignmentVector.measurable_canonicalSlowSampler
              p.two_le_m p.m_lt_K (fun _ => 1) (fun _ => 1)
              (by intro _i; norm_num) (by intro _i; norm_num))
              (measurable_futureAssignmentVectorAtSigma p σ hσ)]
            rfl
    _ = (ContinuousControlSlice.assignmentLaw p.K).map sampler := by
          rw [measurePreserving_futureAssignmentVectorAtSigma p σ hσ |>.map_eq]
    _ = (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
        p.two_le_m p.m_lt_K (by intro _i; norm_num) (by intro _i; norm_num)).toMeasure :=
          CanonicalAssignmentVector.assignmentLaw_map_canonicalSlowSampler
            p.two_le_m p.m_lt_K (fun _ => 1) (fun _ => 1)
            (by intro i; norm_num) (by intro i; norm_num)

/-- The future projection at the accepted split is the original selected row
coordinate, including its complete `TimeControl` and scalar `Slice`. -/
theorem futureAssignmentVectorAtSigma_eq_original (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (z : SideInput p × CompletePublicTable.CompleteRow p) :
    futureAssignmentVectorAtSigma p σ hσ
        (CompleteRowStoppingLaw.sideCompleteRowSplitEquiv
          (SideInput p) p σ z).2 =
      originalAssignmentVectorAt p σ hσ z.2 := by
  rcases z with ⟨coordinates, row⟩
  change ContinuousControlSlice.assignmentVector
      (((CompleteRowStoppingLaw.calendarSplitEquiv p σ
        (calendarizeRow p row)).2 (launchSourceIndex p σ hσ)).2.1) =
    ContinuousControlSlice.assignmentVector
      ((calendarizeRow p row ⟨σ.val, hσ⟩).2.1)
  rfl

/-- On the actual stopping event, the fixed-index first-start input has the
source launch round `σ.val + 1`. -/
theorem actual_start_round_eq_of_stop (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p)
    (z : SideInput p × CompletePublicTable.CompleteRow p)
    (hstop : (ReferenceLaunchRowLaw.actualReferenceLaunchStoppingTime
      p ids rewards C_star C_h eta).stop z = σ) :
    ReferenceInitializationRun.launchRound
      (ReferenceLaunchRowLaw.actualInput p ids rewards C_star C_h eta z.1 z.2) =
      σ.val + 1 := by
  have hshift := ReferenceLaunchRowLaw.actualLaunchStop_source_shift
    p ids rewards C_star C_h eta z.1 z.2
  have hval : ReferenceInitializationRun.launchRound
      (ReferenceLaunchRowLaw.actualInput p ids rewards C_star C_h eta z.1 z.2) - 1 =
        σ.val := by
    have heq := hshift.symm.trans hstop
    exact congrArg Fin.val heq
  have hbound := ReferenceInitializationRun.launchRound_bounds
    (ReferenceLaunchRowLaw.actualInput p ids rewards C_star C_h eta z.1 z.2)
  omega

/-- The actual output slow set is the same canonical sampler applied to the
original selected assignment vector. -/
theorem actualSlowSetAtSigma_eq_canonical (p : Parameters) (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (row : CompletePublicTable.CompleteRow p) :
    actualSlowSetAtSigma p eta hcap n hn σ hσ row =
      CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
        (fun _ => 1) (fun _ => 1) (by intro _i; norm_num) (by intro _i; norm_num)
        (originalAssignmentVectorAt p σ hσ row) := rfl

/-- The actual first-start slow set agrees with the future-coordinate map
used in the stopping-event factorization. -/
theorem actualSlowSetAtSigma_eq_future (p : Parameters) (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (z : SideInput p × CompletePublicTable.CompleteRow p) :
    actualSlowSetAtSigma p eta hcap n hn σ hσ z.2 =
      futureSlowSetAtSigma p σ hσ
        (CompleteRowStoppingLaw.sideCompleteRowSplitEquiv
          (SideInput p) p σ z).2 := by
  rw [actualSlowSetAtSigma_eq_canonical]
  rw [futureSlowSetAtSigma]
  rw [← futureAssignmentVectorAtSigma_eq_original p σ hσ z]

/-- The actual slow-set map is measurable because the existing canonical
sampler is measurable on the product assignment cube. -/
theorem measurable_actualSlowSetAtSigma (p : Parameters) (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T) :
    Measurable (actualSlowSetAtSigma p eta hcap n hn σ hσ) := by
  change Measurable (fun row : CompletePublicTable.CompleteRow p =>
    CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
      (fun _ => 1) (fun _ => 1)
      (by intro i; norm_num) (by intro i; norm_num)
      (originalAssignmentVectorAt p σ hσ row))
  exact (CanonicalAssignmentVector.measurable_canonicalSlowSampler
    p.two_le_m p.m_lt_K (fun _ => 1) (fun _ => 1)
    (by intro i; norm_num) (by intro i; norm_num)).comp
      (measurable_originalAssignmentVectorAt p σ hσ)

/-- The one first-start result keeps the exact original vector and launch
index used by its input. -/
theorem actualStart_coordinates (p : Parameters) (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (row : CompletePublicTable.CompleteRow p) :
    (actualStartAtSigma p eta hcap n hn σ hσ row).coordinates =
      originalAssignmentVectorAt p σ hσ row := by
  exact (firstInputAtSigma p eta hcap n hn σ hσ row).start_coordinates

/-- The existing sorted assignment, image, injectivity, initial state, anchor,
canonical rates, and outgoing fields identify this as the genuine first-start
payload built by `Input.start`. -/
theorem actualStart_payload_facts (p : Parameters) (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (row : CompletePublicTable.CompleteRow p) :
    let s := actualStartAtSigma p eta hcap n hn σ hσ row
    s.sigma = ⟨σ.val, hσ⟩ ∧
    s.coordinates = originalAssignmentVectorAt p σ hσ row ∧
    StrictMono (fun i : Fin (p.m - 1) => s.assignment.assigned i) ∧
    Finset.univ.image s.assignment.assigned = s.slowSet.1 ∧
    Function.Injective s.assignment.assigned ∧
    (∀ i, s.baseScores i = 0) ∧ (∀ i, s.queues i = 0) ∧
    (∀ i, s.weights i = 1) ∧
    (∀ i, s.anchor i = 1) ∧
    (∀ i, s.recordingRates i =
      CanonicalRecordingRates.xi p eta.val (fun _ => 1) i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      OrdinaryMessageCodec.dyadicRate (s.outgoing i).val.h =
        s.recordingRates (s.assignment.assigned i)) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      (s.outgoing i).val =
        ⟨σ.val + 1, (s.assignment.assigned i).val + 1,
          s.assignment.auxiliary.val + 1,
          (firstInputAtSigma p eta hcap n hn σ hσ row).exponent i, 0⟩) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      (s.outgoing i).val.q = 0) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p eta)
        (some (s.outgoingWords i)) = some (s.outgoing i)) := by
  dsimp
  let input := firstInputAtSigma p eta hcap n hn σ hσ row
  refine ⟨rfl, input.start_coordinates, input.start_assignment_strictMono,
    input.start_assignment_image, input.start_assignment_injective,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact input.start_baseScores_zero i
  · intro i
    exact input.start_queues_zero i
  · intro i
    exact input.start_weights_one i
  · intro i
    exact input.start_anchor_one i
  · intro i
    exact input.start_recordingRates i
  · intro i
    exact input.start_outgoing_rate i
  · intro i
    exact input.start_outgoing_fields i
  · intro i
    exact input.start_outgoing_queue_zero i
  · intro i
    exact input.start_parseDown_outgoing i

/-- The actual launch-index event and every measurable event in the full
side/strict-past space are jointly independent of the entire assignment
vector. This is an unnormalized identity and remains valid when either event
has zero mass. -/
theorem actual_launch_assignment_vector_law (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (A : Set (SidePast (SideInput p) p σ)) (hA : MeasurableSet A)
    (B : Set (AssignmentVector p)) (hB : MeasurableSet B) :
    ((extendedPrivateLaw p).prod
      (CompletePublicTable.completeRowMeasure p))
      {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).1 ∈ A ∧
        originalAssignmentVectorAt p σ hσ z.2 ∈ B} =
      ((extendedPrivateLaw p).prod (pastArrayLaw p σ))
        (A ∩ {x | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).eventAt
          σ x = true}) * (ContinuousControlSlice.assignmentLaw p.K) B := by
  let vector := futureAssignmentVectorAtSigma p σ hσ
  have hfuture : MeasurableSet (vector ⁻¹' B) :=
    hB.preimage (measurable_futureAssignmentVectorAtSigma p σ hσ)
  have hfactor := ReferenceLaunchRowLaw.actual_launch_event_factorization
    p ids rewards C_star C_h eta σ A hA (vector ⁻¹' B) hfuture
  have hpush : (CompleteRowStoppingLaw.futureArrayLaw p σ) (vector ⁻¹' B) =
      (ContinuousControlSlice.assignmentLaw p.K) B := by
    calc
      (CompleteRowStoppingLaw.futureArrayLaw p σ) (vector ⁻¹' B) =
          ((CompleteRowStoppingLaw.futureArrayLaw p σ).map vector) B := by
            exact (Measure.map_apply_of_aemeasurable
              (measurable_futureAssignmentVectorAtSigma p σ hσ).aemeasurable hB).symm
      _ = (ContinuousControlSlice.assignmentLaw p.K) B := by
            rw [measurePreserving_futureAssignmentVectorAtSigma p σ hσ |>.map_eq]
  have hset :
      {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).1 ∈ A ∧
        originalAssignmentVectorAt p σ hσ z.2 ∈ B} =
      {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).1 ∈ A ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).2 ∈ vector ⁻¹' B} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [← futureAssignmentVectorAtSigma_eq_original p σ hσ z]
  rw [hset]
  rw [hpush] at hfactor
  exact hfactor

/-- The actual launch and a full side/strict-past event have an unnormalized
joint slow-set law equal to that event's mass times the canonical unit-weight
slow-set PMF. -/
theorem actual_launch_slowSet_law (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (A : Set (SidePast (SideInput p) p σ)) (hA : MeasurableSet A)
    (C : Set (SlowSet p.K p.m)) (hC : MeasurableSet C) :
    ((extendedPrivateLaw p).prod
      (CompletePublicTable.completeRowMeasure p))
      {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).1 ∈ A ∧
        actualSlowSetAtSigma p eta hcap n hn σ hσ z.2 ∈ C} =
      ((extendedPrivateLaw p).prod (pastArrayLaw p σ))
        (A ∩ {x | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).eventAt
          σ x = true}) *
        (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
          p.two_le_m p.m_lt_K (by intro _i; norm_num) (by intro _i; norm_num)).toMeasure C := by
  let sampler := futureSlowSetAtSigma p σ hσ
  have hfuture : MeasurableSet (sampler ⁻¹' C) :=
    hC.preimage (measurable_futureSlowSetAtSigma p σ hσ)
  have hfactor := ReferenceLaunchRowLaw.actual_launch_event_factorization
    p ids rewards C_star C_h eta σ A hA (sampler ⁻¹' C) hfuture
  have hpush : (CompleteRowStoppingLaw.futureArrayLaw p σ) (sampler ⁻¹' C) =
      (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
        p.two_le_m p.m_lt_K (by intro _i; norm_num) (by intro _i; norm_num)).toMeasure C := by
    calc
      (CompleteRowStoppingLaw.futureArrayLaw p σ) (sampler ⁻¹' C) =
          ((CompleteRowStoppingLaw.futureArrayLaw p σ).map sampler) C := by
            exact (Measure.map_apply_of_aemeasurable
              (measurable_futureSlowSetAtSigma p σ hσ).aemeasurable hC).symm
      _ = _ := by rw [futureSlowSetAtSigma_map]
  have hset :
      {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).1 ∈ A ∧
        actualSlowSetAtSigma p eta hcap n hn σ hσ z.2 ∈ C} =
      {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).1 ∈ A ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).2 ∈ sampler ⁻¹' C} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, sampler]
    rw [actualSlowSetAtSigma_eq_future p eta hcap n hn σ hσ z]
  rw [hset]
  rw [hpush] at hfactor
  exact hfactor

/-- Total mass of the actual launch-index event, obtained from the
unnormalized vector identity. -/
theorem actual_launch_index_mass (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (hσ : σ.val < p.T) :
    ((extendedPrivateLaw p).prod (CompletePublicTable.completeRowMeasure p))
      {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ} =
      ((extendedPrivateLaw p).prod (pastArrayLaw p σ))
        {x | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).eventAt
          σ x = true} := by
  simpa [Set.univ_inter] using
    (actual_launch_assignment_vector_law p ids rewards C_star C_h eta σ hσ
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ)

/-- Given positive mass for this actual conditioning event, the normalized
full assignment-vector marginal is the complete product-uniform law. -/
theorem actual_launch_normalized_assignment_vector_marginal
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (hpos : 0 < ((extendedPrivateLaw p).prod
      (CompletePublicTable.completeRowMeasure p))
      {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ})
    (B : Set (AssignmentVector p)) (hB : MeasurableSet B) :
    (Measure.map (actualAssignmentVectorOnSource p σ hσ)
      (((extendedPrivateLaw p).prod
        (CompletePublicTable.completeRowMeasure p)).restrict
          {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ})) B /
      (((extendedPrivateLaw p).prod
        (CompletePublicTable.completeRowMeasure p))
        {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ}) =
      (ContinuousControlSlice.assignmentLaw p.K) B := by
  let τ := actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta
  let μ := (extendedPrivateLaw p).prod (CompletePublicTable.completeRowMeasure p)
  let E : Set (SideInput p × CompletePublicTable.CompleteRow p) := {z | τ.stop z = σ}
  have hmap : (μ.restrict E).map (actualAssignmentVectorOnSource p σ hσ) B =
      μ {z | τ.stop z = σ ∧ originalAssignmentVectorAt p σ hσ z.2 ∈ B} := by
    rw [Measure.map_apply_of_aemeasurable
      (measurable_actualAssignmentVectorOnSource p σ hσ).aemeasurable hB,
      Measure.restrict_apply ((measurable_actualAssignmentVectorOnSource p σ hσ) hB)]
    congr 1
    ext z
    simp [actualAssignmentVectorOnSource, E, τ, Set.mem_inter_iff, and_comm]
  have hjoint : μ {z | τ.stop z = σ ∧
      originalAssignmentVectorAt p σ hσ z.2 ∈ B} =
      μ E * (ContinuousControlSlice.assignmentLaw p.K) B := by
    have hmass : μ E = ((extendedPrivateLaw p).prod (pastArrayLaw p σ))
        {x | τ.eventAt σ x = true} := by
      simpa [μ, E, τ] using actual_launch_index_mass p ids rewards C_star C_h eta σ hσ
    have hbase : μ {z | τ.stop z = σ ∧
        originalAssignmentVectorAt p σ hσ z.2 ∈ B} =
        ((extendedPrivateLaw p).prod (pastArrayLaw p σ))
          {x | τ.eventAt σ x = true} *
            (ContinuousControlSlice.assignmentLaw p.K) B := by
      simpa [μ, E, τ, Set.univ_inter] using
        (actual_launch_assignment_vector_law p ids rewards C_star C_h eta σ hσ
          Set.univ MeasurableSet.univ B hB)
    calc
      μ {z | τ.stop z = σ ∧ originalAssignmentVectorAt p σ hσ z.2 ∈ B} =
          ((extendedPrivateLaw p).prod (pastArrayLaw p σ))
            {x | τ.eventAt σ x = true} *
              (ContinuousControlSlice.assignmentLaw p.K) B := hbase
      _ = μ E * (ContinuousControlSlice.assignmentLaw p.K) B := by rw [← hmass]
  calc
      (μ.restrict E).map (actualAssignmentVectorOnSource p σ hσ) B / μ E =
          (μ E * (ContinuousControlSlice.assignmentLaw p.K) B) / μ E := by
            rw [hmap, hjoint]
      _ = (ContinuousControlSlice.assignmentLaw p.K) B := by
            rw [mul_comm (μ E)]
            exact ENNReal.mul_div_cancel_right hpos.ne' (measure_ne_top μ E)

/-- Given positive mass for this actual conditioning event, the normalized
slow-set marginal is the canonical unit-current and unit-anchor PMF. -/
theorem actual_launch_normalized_slowSet_marginal
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (hpos : 0 < ((extendedPrivateLaw p).prod
      (CompletePublicTable.completeRowMeasure p))
      {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ})
    (C : Set (SlowSet p.K p.m)) (hC : MeasurableSet C) :
    (Measure.map (fun z : SideInput p × CompletePublicTable.CompleteRow p =>
        actualSlowSetAtSigma p eta hcap n hn σ hσ z.2)
      (((extendedPrivateLaw p).prod
        (CompletePublicTable.completeRowMeasure p)).restrict
          {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ})) C /
      (((extendedPrivateLaw p).prod
        (CompletePublicTable.completeRowMeasure p))
        {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ}) =
      (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
        p.two_le_m p.m_lt_K (by intro _i; norm_num) (by intro _i; norm_num)
        ).toMeasure C := by
  let τ := actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta
  let μ := (extendedPrivateLaw p).prod (CompletePublicTable.completeRowMeasure p)
  let E : Set (SideInput p × CompletePublicTable.CompleteRow p) := {z | τ.stop z = σ}
  have hactualMeas : Measurable (fun z : SideInput p × CompletePublicTable.CompleteRow p =>
      actualSlowSetAtSigma p eta hcap n hn σ hσ z.2) :=
    (measurable_actualSlowSetAtSigma p eta hcap n hn σ hσ).comp measurable_snd
  have hmap : (μ.restrict E).map
      (fun z : SideInput p × CompletePublicTable.CompleteRow p =>
        actualSlowSetAtSigma p eta hcap n hn σ hσ z.2) C =
      μ {z | τ.stop z = σ ∧ actualSlowSetAtSigma p eta hcap n hn σ hσ z.2 ∈ C} := by
    rw [Measure.map_apply_of_aemeasurable hactualMeas.aemeasurable hC,
      Measure.restrict_apply (hactualMeas hC)]
    congr 1
    ext z
    simp [E, τ, Set.mem_inter_iff, and_comm]
  have hjoint : μ {z | τ.stop z = σ ∧
      actualSlowSetAtSigma p eta hcap n hn σ hσ z.2 ∈ C} =
      μ E * (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
        p.two_le_m p.m_lt_K (by intro _i; norm_num) (by intro _i; norm_num)
        ).toMeasure C := by
    have hmass : μ E = ((extendedPrivateLaw p).prod (pastArrayLaw p σ))
        {x | τ.eventAt σ x = true} := by
      simpa [μ, E, τ] using actual_launch_index_mass p ids rewards C_star C_h eta σ hσ
    have hbase : μ {z | τ.stop z = σ ∧
        actualSlowSetAtSigma p eta hcap n hn σ hσ z.2 ∈ C} =
        ((extendedPrivateLaw p).prod (pastArrayLaw p σ))
          {x | τ.eventAt σ x = true} *
            (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
              p.two_le_m p.m_lt_K (by intro _i; norm_num) (by intro _i; norm_num)
              ).toMeasure C := by
      simpa [μ, E, τ, Set.univ_inter] using
      (actual_launch_slowSet_law p ids rewards C_star C_h eta hcap n hn σ hσ
        Set.univ MeasurableSet.univ C hC)
    calc
      μ {z | τ.stop z = σ ∧
          actualSlowSetAtSigma p eta hcap n hn σ hσ z.2 ∈ C} =
          ((extendedPrivateLaw p).prod (pastArrayLaw p σ))
            {x | τ.eventAt σ x = true} *
              (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
                p.two_le_m p.m_lt_K (by intro _i; norm_num) (by intro _i; norm_num)
                ).toMeasure C := hbase
      _ = μ E * (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
          p.two_le_m p.m_lt_K (by intro _i; norm_num) (by intro _i; norm_num)
          ).toMeasure C := by rw [← hmass]
  calc
      (μ.restrict E).map
          (fun z : SideInput p × CompletePublicTable.CompleteRow p =>
            actualSlowSetAtSigma p eta hcap n hn σ hσ z.2) C / μ E =
          (μ E * (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
            p.two_le_m p.m_lt_K (by intro _i; norm_num) (by intro _i; norm_num)
            ).toMeasure C) / μ E := by
              rw [hmap, hjoint]
      _ = (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
          p.two_le_m p.m_lt_K (by intro _i; norm_num) (by intro _i; norm_num)
          ).toMeasure C := by
            rw [mul_comm (μ E)]
            exact ENNReal.mul_div_cancel_right hpos.ne' (measure_ne_top μ E)

/-- At the source `T + 1` sentinel the accepted stopping law has an empty
future subtype. There is no `Fin T` launch coordinate and this module defines
no first-assignment input or start at that sentinel. -/
theorem actual_launch_sentinel_has_no_future (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (z : SideInput p × CompletePublicTable.CompleteRow p)
    (hsentinel : ReferenceInitializationRun.launchRound
      (ReferenceLaunchRowLaw.actualInput p ids rewards C_star C_h eta z.1 z.2) = p.T + 1) :
    (ReferenceLaunchRowLaw.actualReferenceLaunchStoppingTime
      p ids rewards C_star C_h eta).stop z = horizonStoppingIndex p ∧
      IsEmpty (FutureIndex p (horizonStoppingIndex p)) := by
  exact ⟨ReferenceLaunchRowLaw.actualLaunchStop_sentinel p ids rewards C_star C_h eta
      z.1 z.2 hsentinel,
    ReferenceLaunchRowLaw.source_sentinel_has_empty_future p⟩

end Bandits.Support.ReferenceLaunchAssignmentLaw

end
