/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLaunchSavedSourceMoments

/-!
# First chronological common update on the original source

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:41-64,391-397`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

This module identifies the actual chronological first live cell with the
first-launch numerical cell, computes its inclusive initial queue update,
exposes actual complement storage and the occupied-or-deferred follower
branches, and transports all-arm first and second moments on the original
unnormalized source stratum. It does not identify an adapted history or close
a manuscript statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Bandits.Support.ReferenceFirstLaunchCommonUpdateSource

open ConstructorDimensions
open ContinuousControlSlice
open ContinuousLearningRows
open ReferenceFirstLaunchRecordingPhysicalMarker
open ReferenceFirstLaunchRecordingSourceLaw
open RecordedQueueRun
open RecordedRoundMoments
open CanonicalRecordingRates
open SnapshotRecordingKernel
open QuantizedRecordingMoments

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev AssignmentVector := ReferenceFirstLaunchRecordingPhysicalMarker.AssignmentVector
abbrev NonAssignmentControl := ReferenceFirstLaunchRecordingPhysicalMarker.NonAssignmentControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (control0 : ContinuousLearningRows.TimeControl p)

local notation "X" => ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart rate rewards C_star C_h q t control0
local notation "V" => ReferenceFirstLaunchRecordingPhysicalMarker.AssignmentVector p
local notation "Dctl" => ReferenceFirstLaunchRecordingPhysicalMarker.NonAssignmentControl p
local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "μZ" => ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
  (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "μC" => ReferenceRetainedSourceCoupling.retainedRemainderMeasure
  rate rewards C_star C_h q t t.val le_rfl control0
local notation "λA" => ContinuousControlSlice.assignmentLaw p.K
local notation "coords" => ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
  rate rewards C_star C_h q t control0

/-! The following are literal readouts from the actual source cell and the
existing queue machine. -/

/-- The actual first-launch numerical cell, pulled back to the original source. -/
def firstCell (z : Z) : RecordedQueueRun.RoundInput p.K :=
  let c := coords z
  ReferenceFirstLaunchRecordingPhysicalMarker.numericalCell rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2

/-- The one actual numerical queue step from the checked zero learner state. -/
def firstUpdate (z : Z) : RecordedQueueRun.RunState p.K :=
  RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (RecordedQueueRun.initialState p.K) (firstCell rate rewards C_star C_h q t control0 z)

/-- The actual all-arm integer arrival in the first cell. -/
def firstArrival (z : Z) (j : Fin p.K) : ℕ :=
  RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (firstCell rate rewards C_star C_h q t control0 z) j

/-- Conserved score plus backlog after the actual first update, in source units. -/
def firstConservedReadout (z : Z) (j : Fin p.K) : ℝ :=
  (((firstUpdate rate rewards C_star C_h q t control0 z).registers j).1 +
    ((firstUpdate rate rewards C_star C_h q t control0 z).registers j).2 : ℕ) /
      (rate.eta.val * (D p : ℝ))

/-- Every arm receives its actual enabled first record from zero state. Service
and residual backlog are the literal queue transition, and their sum keeps the
whole arrival even when this update first crosses the overflow threshold. -/
theorem source_first_update (z : Z) :
    (∀ j : Fin p.K,
      (firstUpdate rate rewards C_star C_h q t control0 z).records j =
          [(true, firstArrival rate rewards C_star C_h q t control0 z j)] ∧
        (firstUpdate rate rewards C_star C_h q t control0 z).registers j =
          (min (4 * rate.n) (firstArrival rate rewards C_star C_h q t control0 z j),
            firstArrival rate rewards C_star C_h q t control0 z j -
              min (4 * rate.n) (firstArrival rate rewards C_star C_h q t control0 z j)) ∧
        (((firstUpdate rate rewards C_star C_h q t control0 z).registers j).1 +
          ((firstUpdate rate rewards C_star C_h q t control0 z).registers j).2) =
            firstArrival rate rewards C_star C_h q t control0 z j) ∧
      ((firstUpdate rate rewards C_star C_h q t control0 z).overflow = true ↔
        ∃ j : Fin p.K,
          32 * ((firstUpdate rate rewards C_star C_h q t control0 z).registers j).2 > D p) ∧
      (∀ _ : (firstUpdate rate rewards C_star C_h q t control0 z).overflow = true,
        (∃ j : Fin p.K,
          32 * ((firstUpdate rate rewards C_star C_h q t control0 z).registers j).2 > D p) ∧
        ∀ j : Fin p.K,
          (firstUpdate rate rewards C_star C_h q t control0 z).registers j =
            QueueReplay.transition (4 * rate.n) (0, 0)
              (true, firstArrival rate rewards C_star C_h q t control0 z j)) := by
  classical
  have hreadout := ReferenceFirstLaunchRecordingPhysicalMarker.numerical_cell_readout
    rate rewards C_star C_h q t control0
    (coords z).1 (coords z).2.1 (coords z).2.2
  have henabled : (firstCell rate rewards C_star C_h q t control0 z).enabled = true := by
    simpa only [firstCell] using hreadout.1
  have haccepted (j : Fin p.K) :
      RecordedQueueRun.acceptedRecord
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.initialState p.K)
          (firstCell rate rewards C_star C_h q t control0 z) j =
        (true, firstArrival rate rewards C_star C_h q t control0 z j) := by
    change (if (RecordedQueueRun.initialState p.K).overflow then (false, 0)
      else if (firstCell rate rewards C_star C_h q t control0 z).enabled then
        (true, firstArrival rate rewards C_star C_h q t control0 z j) else (false, 0)) = _
    simp [RecordedQueueRun.initialState, henabled]
  have hregisters (j : Fin p.K) :
      (firstUpdate rate rewards C_star C_h q t control0 z).registers j =
        QueueReplay.transition (4 * rate.n) (0, 0)
          (true, firstArrival rate rewards C_star C_h q t control0 z j) := by
    change QueueReplay.transition (4 * rate.n) (0, 0)
      (RecordedQueueRun.acceptedRecord
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (RecordedQueueRun.initialState p.K)
        (firstCell rate rewards C_star C_h q t control0 z) j) = _
    rw [haccepted j]

  have hrecords (j : Fin p.K) :
      (firstUpdate rate rewards C_star C_h q t control0 z).records j =
        [(true, firstArrival rate rewards C_star C_h q t control0 z j)] := by
    change (RecordedQueueRun.initialState p.K).records j ++
      [RecordedQueueRun.acceptedRecord
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (RecordedQueueRun.initialState p.K)
        (firstCell rate rewards C_star C_h q t control0 z) j] = _
    rw [haccepted j]
    simp only [RecordedQueueRun.initialState, List.nil_append]
  have hregisters_explicit (j : Fin p.K) :
      (firstUpdate rate rewards C_star C_h q t control0 z).registers j =
        (min (4 * rate.n) (firstArrival rate rewards C_star C_h q t control0 z j),
          firstArrival rate rewards C_star C_h q t control0 z j -
            min (4 * rate.n) (firstArrival rate rewards C_star C_h q t control0 z j)) := by
    rw [hregisters]
    simp [QueueReplay.transition]
  have htotal (j : Fin p.K) :
      ((firstUpdate rate rewards C_star C_h q t control0 z).registers j).1 +
        ((firstUpdate rate rewards C_star C_h q t control0 z).registers j).2 =
          firstArrival rate rewards C_star C_h q t control0 z j := by
    rw [hregisters]
    simpa only [RecordedQueueRun.acceptedArrival, ite_true,
      Nat.zero_add] using RecordedQueueRun.transition_total
        (4 * rate.n) (0, 0) (true, firstArrival rate rewards C_star C_h q t control0 z j)
  have hoverflow :
      (firstUpdate rate rewards C_star C_h q t control0 z).overflow = true ↔
        ∃ j : Fin p.K,
          32 * ((firstUpdate rate rewards C_star C_h q t control0 z).registers j).2 > D p := by
    simp [firstUpdate, RecordedQueueRun.step, RecordedQueueRun.initialState,
      ReferenceFirstLaunchNumericalCell.queueParameters]
  refine ⟨?_, hoverflow, ?_⟩
  · intro j
    exact ⟨hrecords j, hregisters_explicit j, htotal j⟩
  · intro hcross
    have hretained := RecordedQueueRun.step_retains_first_overflow_update
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) (RecordedQueueRun.initialState p.K)
      (firstCell rate rewards C_star C_h q t control0 z) rfl (by
        simpa only [firstUpdate] using hcross)
    constructor
    · simpa only [firstUpdate, RecordedQueueRun.initialState,
        ReferenceFirstLaunchNumericalCell.queueParameters] using hretained.1
    · intro j
      have hretainedRegister := hretained.2 j
      rw [haccepted j] at hretainedRegister
      simpa [firstUpdate, RecordedQueueRun.initialState,
        ReferenceFirstLaunchNumericalCell.queueParameters] using hretainedRegister

/-- The conserved score-plus-backlog readout is the actual marker's all-arm
quantized estimator. The service split does not discard the unserved part. -/
theorem firstConservedReadout_eq_sourceMarker (z : Z) (j : Fin p.K) :
    firstConservedReadout rate rewards C_star C_h q t control0 z j =
      if ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h q t control0 z = some j then
        QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
          (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j)
          (((rewards t j).val : ℝ) / (D p : ℝ))
      else 0 := by
  classical
  let c := coords z
  let cell := firstCell rate rewards C_star C_h q t control0 z
  let qparams := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let xi := CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j
  let rho := (((rewards t j).val : ℝ) / (D p : ℝ))
  let quantized := QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val xi rho
  have hreadout := ReferenceFirstLaunchRecordingPhysicalMarker.numerical_cell_readout
    rate rewards C_star C_h q t control0
    c.1 c.2.1 c.2.2
  have hmarker : cell.recordedArm = ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
      rate rewards C_star C_h q t control0 z := by
    simpa only [cell, firstCell, c, ReferenceFirstLaunchRecordingSourceLaw.sourceMarker] using hreadout.2.1
  have hmarkerPhysical :
      ReferenceFirstLaunchRecordingPhysicalMarker.physicalMarker rate rewards C_star C_h q t control0
          c.1 c.2.1 c.2.2 =
        ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h q t control0 z :=
    hreadout.2.1.symm.trans hmarker
  have harrival : ∀ a : Fin p.K,
      RecordedQueueRun.quantizedArrival qparams cell a =
        if ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h q t control0 z = some a then
          Nat.floor ((rate.n : ℝ) * (((rewards t a).val : ℝ) / (D p : ℝ)) /
            CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) a)
        else 0 := by
    intro a
    have h := hreadout.2.2 a
    change RecordedQueueRun.quantizedArrival qparams cell a = _ at h
    rw [hmarkerPhysical] at h
    exact h
  obtain ⟨_, _, _, htime, hrewards⟩ :=
    ReferenceFirstLaunchRecordingPhysicalMarker.record_source_inputs
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2
  have hrate : cell.rate j = xi := by
    simpa only [cell, firstCell, c, ReferenceFirstLaunchRecordingPhysicalMarker.numericalCell,
      ReferenceFirstWindowNumericalStream.sourceCell, xi] using
      ReferenceFirstLaunchRecordingPhysicalMarker.payload_rate rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 j
  have hreward : cell.reward j = rho := by
    simp [cell, firstCell, c, ReferenceFirstLaunchRecordingPhysicalMarker.numericalCell,
      ReferenceFirstWindowNumericalStream.sourceCell, htime, hrewards, rho]
  have hconserved :
      firstConservedReadout rate rewards C_star C_h q t control0 z j =
        (firstArrival rate rewards C_star C_h q t control0 z j : ℝ) /
          (rate.eta.val * (D p : ℝ)) := by
    have hnat :
        ((firstUpdate rate rewards C_star C_h q t control0 z).registers j).1 +
          ((firstUpdate rate rewards C_star C_h q t control0 z).registers j).2 =
            firstArrival rate rewards C_star C_h q t control0 z j :=
      (source_first_update rate rewards C_star C_h q t control0 z).1 j |>.2.2
    have hreal :
        ((((firstUpdate rate rewards C_star C_h q t control0 z).registers j).1 +
          ((firstUpdate rate rewards C_star C_h q t control0 z).registers j).2 : ℕ) : ℝ) =
          (firstArrival rate rewards C_star C_h q t control0 z j : ℝ) := by
      exact_mod_cast hnat
    change ((((firstUpdate rate rewards C_star C_h q t control0 z).registers j).1 +
      ((firstUpdate rate rewards C_star C_h q t control0 z).registers j).2 : ℕ) : ℝ) /
        (rate.eta.val * (D p : ℝ)) = _
    rw [hreal]
  by_cases hrecorded : ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
      rate rewards C_star C_h q t control0 z = some j
  · have hcellRecorded : cell.recordedArm = some j := hmarker.trans hrecorded
    have hnormalized := RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded
      qparams cell j hcellRecorded
    have hden : (qparams.n : ℝ) = rate.eta.val * (D p : ℝ) := by
      simpa only [qparams, ReferenceFirstLaunchNumericalCell.queueParameters] using qparams.n_eq_eta_mul_D
    have hvalue :
        (firstArrival rate rewards C_star C_h q t control0 z j : ℝ) /
            (rate.eta.val * (D p : ℝ)) = quantized := by
      change (RecordedQueueRun.quantizedArrival qparams cell j : ℝ) /
          (rate.eta.val * (D p : ℝ)) = quantized
      rw [← hden]
      change RecordedRoundMoments.normalizedQuantizedArrival qparams cell j = quantized
      simpa only [qparams, ReferenceFirstLaunchNumericalCell.queueParameters,
        hrate, hreward, quantized] using hnormalized
    simp [hconserved, hrecorded, hvalue, quantized, xi, rho]
  · have hzero : firstArrival rate rewards C_star C_h q t control0 z j = 0 := by
      have hsourceNe :
          ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h q t control0 z ≠ some j :=
        hrecorded
      simpa [firstArrival, cell, firstCell, c, qparams, hsourceNe] using harrival j
    simp [hconserved, hrecorded, hzero]

/-- The all-arm first-update law on arbitrary measured retained-source and
whole-assignment cylinders. The two integrals use the original unnormalized
stratum measure, with no cylinder-mass normalization or additional selected-
index factor. -/
theorem first_update_all_arm_source_moments (j : Fin p.K)
    (Aset : Set X) (Bset : Set V) (hA : MeasurableSet Aset) (hB : MeasurableSet Bset) :
    Measurable (fun z : Z => firstConservedReadout rate rewards C_star C_h q t control0 z j) ∧
    Measurable (fun z : Z => (firstConservedReadout rate rewards C_star C_h q t control0 z j) ^ 2) ∧
    Integrable (fun z : Z => firstConservedReadout rate rewards C_star C_h q t control0 z j) μZ ∧
    Integrable (fun z : Z => (firstConservedReadout rate rewards C_star C_h q t control0 z j) ^ 2) μZ ∧
    (∫ z in {z : Z | (coords z).1 ∈ Aset ∧ (coords z).2.1 ∈ Bset},
      firstConservedReadout rate rewards C_star C_h q t control0 z j ∂μZ) =
        (μC Aset).toReal * (λA Bset).toReal *
          CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j *
          QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
            (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j)
            (((rewards t j).val : ℝ) / (D p : ℝ)) ∧
    (∫ z in {z : Z | (coords z).1 ∈ Aset ∧ (coords z).2.1 ∈ Bset},
      (firstConservedReadout rate rewards C_star C_h q t control0 z j) ^ 2 ∂μZ) =
        (μC Aset).toReal * (λA Bset).toReal *
          CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j *
          (QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
            (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j)
            (((rewards t j).val : ℝ) / (D p : ℝ))) ^ 2 := by
  classical
  let xi := CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j
  let rho := (((rewards t j).val : ℝ) / (D p : ℝ))
  let quantized := QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val xi rho
  let rates := SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
    rate.sourceCap (fun _ => 1) (by intro _; norm_num)
  let reward : Fin p.K → ℝ := fun a => (((rewards t a).val : ℝ) / (D p : ℝ))
  have hreward_mem : ∀ a : Fin p.K, reward a ∈ Set.Icc (0 : ℝ) 1 := by
    intro a
    have hD : 0 < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
    have hval : (rewards t a).val ≤ D p := Nat.le_of_lt_succ (rewards t a).isLt
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hD.le
    · apply (div_le_one hD).2
      exact_mod_cast hval
  have hxi : rates.rate j = xi := by
    rfl
  have hquantized_nonneg : 0 ≤ quantized := by
    exact QuantizedRecordingMoments.quantizedValue_nonneg (D p) rate.eta.val xi rho
      rate.eta.property
  have hbeta : 0 < CanonicalRecordingRates.beta p rate.eta.val :=
    CanonicalRecordingRates.beta_pos p rate.eta.property
  have hxi_pos : 0 < xi := by
    exact CanonicalRecordingRates.xi_pos p rate.eta.property (fun _ => 1) j
  have hbeta_xi : CanonicalRecordingRates.beta p rate.eta.val ≤ xi := by
    exact CanonicalRecordingRates.beta_le_xi p rate.eta.property (fun _ => 1) j
  have hrho_mem : rho ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [rho, reward] using hreward_mem j
  have hquantized_bound : quantized ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := by
    exact QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
      (D p) rate.eta.val xi rho (CanonicalRecordingRates.beta p rate.eta.val)
      (D_pos p) rate.eta.property hxi_pos hrho_mem hbeta hbeta_xi
  let kernel : Option (Fin p.K) → ℝ := fun o =>
    if o = some j then quantized else 0
  have hkernel_meas : Measurable kernel :=
    RecordedRoundMoments.measurable_on_recording_outcomes _
  have hkernel_sq_meas : Measurable (fun o => (kernel o) ^ 2) := hkernel_meas.pow_const 2
  have hkernel_first :
      (∫ o, kernel o ∂ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) =
        xi * quantized := by
    have hformula : ∀ o : Option (Fin p.K),
        kernel o = RecordedRoundMoments.rawEstimate (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.initialState p.K)
          (RecordedRoundMoments.fixedRoundInput (ReferenceFirstLaunchNumericalCell.queueParameters rate) rates reward
            hreward_mem true o) j := by
      intro o
      rw [RecordedRoundMoments.rawEstimate_eq_quantizedValue_of_enabled
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) (RecordedQueueRun.initialState p.K)
        rates reward hreward_mem o j rfl]
      by_cases ho : o = some j
      · simp [kernel, ho]
        rw [hxi]
        rfl
      · simp [kernel, ho]
    calc
      _ = ∫ o, RecordedRoundMoments.rawEstimate (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.initialState p.K)
          (RecordedRoundMoments.fixedRoundInput (ReferenceFirstLaunchNumericalCell.queueParameters rate) rates reward
            hreward_mem true o) j ∂ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate := by
        congr 1
        funext o
        exact hformula o
      _ = rates.rate j *
          QuantizedRecordingMoments.quantizedValue (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (rates.rate j) (reward j) := by
        rw [ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw]
        exact RecordedRoundMoments.rawEstimate_firstMoment_eq (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.initialState p.K) rates reward hreward_mem j rfl
      _ = xi * quantized := by
        rw [hxi]
        simp [reward, rho, quantized, ReferenceFirstLaunchNumericalCell.queueParameters]
  have hkernel_second :
      (∫ o, (kernel o) ^ 2 ∂ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) =
        xi * quantized ^ 2 := by
    have hformula : ∀ o : Option (Fin p.K),
        (kernel o) ^ 2 = (RecordedRoundMoments.rawEstimate (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.initialState p.K)
          (RecordedRoundMoments.fixedRoundInput (ReferenceFirstLaunchNumericalCell.queueParameters rate) rates reward
            hreward_mem true o) j) ^ 2 := by
      intro o
      rw [RecordedRoundMoments.rawEstimate_eq_quantizedValue_of_enabled
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) (RecordedQueueRun.initialState p.K)
        rates reward hreward_mem o j rfl]
      by_cases ho : o = some j
      · simp [kernel, ho]
        rw [hxi]
        rfl
      · simp [kernel, ho]
    calc
      _ = ∫ o, (RecordedRoundMoments.rawEstimate (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.initialState p.K)
          (RecordedRoundMoments.fixedRoundInput (ReferenceFirstLaunchNumericalCell.queueParameters rate) rates reward
            hreward_mem true o) j) ^ 2 ∂ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate := by
        congr 1
        funext o
        exact hformula o
      _ = rates.rate j *
          (QuantizedRecordingMoments.quantizedValue (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (rates.rate j) (reward j)) ^ 2 := by
        rw [ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw]
        exact RecordedRoundMoments.rawEstimate_secondMoment_eq (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.initialState p.K) rates reward hreward_mem j rfl
      _ = xi * quantized ^ 2 := by
        rw [hxi]
        simp [reward, rho, quantized, ReferenceFirstLaunchNumericalCell.queueParameters]
  have hpoint : ∀ z : Z,
      firstConservedReadout rate rewards C_star C_h q t control0 z j =
        kernel (ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h q t control0 z) := by
    intro z
    rw [firstConservedReadout_eq_sourceMarker]
  have hYmeas : Measurable
      (fun z : Z => firstConservedReadout rate rewards C_star C_h q t control0 z j) := by
    have hcomp := Measurable.comp hkernel_meas
      (ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceMarker rate rewards C_star C_h q t control0)
    have hEq : (fun z : Z => firstConservedReadout rate rewards C_star C_h q t control0 z j) =
        kernel ∘ ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h q t control0 := by
      funext z
      exact hpoint z
    rw [hEq]
    exact hcomp
  have hYsqmeas : Measurable
      (fun z : Z => (firstConservedReadout rate rewards C_star C_h q t control0 z j) ^ 2) :=
    hYmeas.pow_const 2
  have hYbound : ∀ z : Z,
      ‖firstConservedReadout rate rewards C_star C_h q t control0 z j‖ ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
    intro z
    rw [hpoint z]
    by_cases hz : ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h q t control0 z = some j
    · simp only [kernel, ite_eq_left hz, Real.norm_eq_abs, abs_of_nonneg hquantized_nonneg]
      exact hquantized_bound
    · simp only [kernel, ite_eq_right hz, norm_zero]
      positivity
  have hYsqbound : ∀ z : Z,
      ‖(firstConservedReadout rate rewards C_star C_h q t control0 z j) ^ 2‖ ≤
        (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 := by
    intro z
    rw [hpoint z]
    by_cases hz : ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h q t control0 z = some j
    · simp only [kernel, ite_eq_left hz, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg quantized)]
      have hbinv : 0 ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
        (div_pos (by norm_num) hbeta).le
      have hqbound : quantized ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := hquantized_bound
      have hsq := (sq_le_sq₀ hquantized_nonneg hbinv).2 hqbound
      exact hsq
    · simp only [kernel, ite_eq_right hz, zero_pow (by decide : 2 ≠ 0), norm_zero]
      positivity
  have hYint : Integrable
      (fun z : Z => firstConservedReadout rate rewards C_star C_h q t control0 z j) μZ :=
    Integrable.of_bound hYmeas.aestronglyMeasurable
      (1 / CanonicalRecordingRates.beta p rate.eta.val)
      (Filter.Eventually.of_forall hYbound)
  have hYsqint : Integrable
      (fun z : Z => (firstConservedReadout rate rewards C_star C_h q t control0 z j) ^ 2) μZ :=
    Integrable.of_bound hYsqmeas.aestronglyMeasurable
      ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2)
      (Filter.Eventually.of_forall hYsqbound)
  let cyl : Set (X × V) := Aset ×ˢ Bset
  let E : Set Z := {z | (coords z).1 ∈ Aset ∧ (coords z).2.1 ∈ Bset}
  let F : Z → (X × V) × Option (Fin p.K) := fun z =>
    let c := coords z
    ((c.1, c.2.1), ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h q t control0 z)
  let targetSet : Set ((X × V) × Option (Fin p.K)) := cyl ×ˢ Set.univ
  let H : ((X × V) × Option (Fin p.K)) → ℝ := targetSet.indicator (fun w => kernel w.2)
  let Hsq : ((X × V) × Option (Fin p.K)) → ℝ := targetSet.indicator (fun w => (kernel w.2) ^ 2)
  have hcyl : MeasurableSet cyl := hA.prod hB
  have htarget : MeasurableSet targetSet := hcyl.prod MeasurableSet.univ
  have hE : MeasurableSet E := by
    have hcoords := ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
      rate rewards C_star C_h q t control0
    exact (hA.preimage hcoords.fst).inter (hB.preimage hcoords.snd.fst)
  have hF : Measurable F := by
    change Measurable (fun z : Z =>
      (((coords z).1, (coords z).2.1),
        ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h q t control0 z))
    have hcoords := ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
      rate rewards C_star C_h q t control0
    exact (hcoords.fst.prodMk hcoords.snd.fst).prodMk
      (ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceMarker rate rewards C_star C_h q t control0)
  have hFmap : MeasureTheory.Measure.map F μZ =
      ((μC).prod λA).prod (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) := by
    simpa only [F] using ReferenceFirstLaunchRecordingSourceLaw.source_joint_map rate rewards C_star C_h q t control0
  have hHmeas : Measurable H := (hkernel_meas.comp measurable_snd).indicator htarget
  have hHsqmeas : Measurable Hsq := (hkernel_sq_meas.comp measurable_snd).indicator htarget
  have hHbound : ∀ w, ‖H w‖ ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := by
    intro w
    by_cases hw : w ∈ targetSet
    · simp only [H, Set.indicator_of_mem hw, Real.norm_eq_abs]
      by_cases ho : w.2 = some j
      · simp only [kernel, ite_eq_left ho, abs_of_nonneg hquantized_nonneg]
        exact hquantized_bound
      · simp only [kernel, ite_eq_right ho, abs_zero]
        positivity
    · have hzero : H w = 0 := by simp [H, hw]
      rw [hzero, norm_zero]
      positivity
  have hHsqbound : ∀ w, ‖Hsq w‖ ≤
      (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 := by
    intro w
    by_cases hw : w ∈ targetSet
    · simp only [Hsq, Set.indicator_of_mem hw, Real.norm_eq_abs]
      by_cases ho : w.2 = some j
      · simp [kernel, ho, abs_of_nonneg (sq_nonneg quantized)]
        have hbinv : 0 ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
          (div_pos (by norm_num) hbeta).le
        have hsq := (sq_le_sq₀ hquantized_nonneg hbinv).2 hquantized_bound
        have hpow : (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 =
            (CanonicalRecordingRates.beta p rate.eta.val ^ 2)⁻¹ := by
          field_simp [ne_of_gt hbeta]
        exact hsq.trans_eq hpow
      · simp only [kernel, ite_eq_right ho, zero_pow (by decide : 2 ≠ 0), abs_zero]
        positivity
    · have hzero : Hsq w = 0 := by simp [Hsq, hw]
      rw [hzero, norm_zero]
      positivity
  have hHint : Integrable H (((μC).prod λA).prod (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate)) :=
    Integrable.of_bound hHmeas.aestronglyMeasurable
      (1 / CanonicalRecordingRates.beta p rate.eta.val)
      (Filter.Eventually.of_forall hHbound)
  have hHsqint : Integrable Hsq (((μC).prod λA).prod (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate)) :=
    Integrable.of_bound hHsqmeas.aestronglyMeasurable
      ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2)
      (Filter.Eventually.of_forall hHsqbound)
  have hSourceIndicator : E.indicator
      (fun z => firstConservedReadout rate rewards C_star C_h q t control0 z j) = H ∘ F := by
    funext z
    by_cases hz : z ∈ E
    · have hmem : F z ∈ targetSet := by simpa [F, E, targetSet, cyl] using hz
      simp [Function.comp_apply, H, F, E, targetSet, cyl, hz, hmem, hpoint]
    · have hmem : F z ∉ targetSet := by simpa [F, E, targetSet, cyl] using hz
      simp [Function.comp_apply, H, F, E, targetSet, cyl, hz, hmem]
  have hSourceSqIndicator : E.indicator
      (fun z => (firstConservedReadout rate rewards C_star C_h q t control0 z j) ^ 2) = Hsq ∘ F := by
    funext z
    by_cases hz : z ∈ E
    · have hmem : F z ∈ targetSet := by simpa [F, E, targetSet, cyl] using hz
      simp [Function.comp_apply, Hsq, F, E, targetSet, cyl, hz, hmem, hpoint]
    · have hmem : F z ∉ targetSet := by simpa [F, E, targetSet, cyl] using hz
      simp [Function.comp_apply, Hsq, F, E, targetSet, cyl, hz, hmem]
  have hFiber : ∀ y : X × V,
      (∫ o, H (y, o) ∂ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) =
        cyl.indicator (fun _ => xi * quantized) y := by
    intro y
    by_cases hy : y ∈ cyl
    · have heq : (fun o => H (y, o)) = kernel := by
        funext o
        simp [H, targetSet, hy]
      rw [heq, hkernel_first]
      simp [hy]
    · have heq : (fun o : Option (Fin p.K) => H (y, o)) = fun _ => (0 : ℝ) := by
        funext o
        simp [H, targetSet, hy]
      rw [heq]
      simp [hy]
  have hFiberSq : ∀ y : X × V,
      (∫ o, Hsq (y, o) ∂ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) =
        cyl.indicator (fun _ => xi * quantized ^ 2) y := by
    intro y
    by_cases hy : y ∈ cyl
    · have heq : (fun o => Hsq (y, o)) = fun o => (kernel o) ^ 2 := by
        funext o
        simp [Hsq, targetSet, hy]
      rw [heq, hkernel_second]
      simp [hy]
    · have heq : (fun o : Option (Fin p.K) => Hsq (y, o)) = fun _ => (0 : ℝ) := by
        funext o
        simp [Hsq, targetSet, hy]
      rw [heq]
      simp [hy]
  have hAint : (∫ x in Aset, (1 : ℝ) ∂μC) = (μC Aset).toReal := by
    rw [setIntegral_const]
    simp [measureReal_def]
  have hBint : (∫ v in Bset, (xi * quantized) ∂λA) =
      (λA Bset).toReal * (xi * quantized) := by
    rw [setIntegral_const]
    simp [measureReal_def]
  have hBsqint : (∫ v in Bset, (xi * quantized ^ 2) ∂λA) =
      (λA Bset).toReal * (xi * quantized ^ 2) := by
    rw [setIntegral_const]
    simp [measureReal_def]
  have hfirstIntegral :
      (∫ z in E, firstConservedReadout rate rewards C_star C_h q t control0 z j ∂μZ) =
        (μC Aset).toReal * (λA Bset).toReal * xi * quantized := by
    calc
      _ = ∫ z, E.indicator
          (fun z => firstConservedReadout rate rewards C_star C_h q t control0 z j) z ∂μZ := by
        rw [← integral_indicator hE]
      _ = ∫ z, H (F z) ∂μZ := by
        rw [hSourceIndicator]
        rfl
      _ = ∫ w, H w ∂(MeasureTheory.Measure.map F μZ) :=
        (MeasureTheory.integral_map hF.aemeasurable hHmeas.aestronglyMeasurable).symm
      _ = ∫ w, H w ∂(((μC).prod λA).prod (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate)) := by rw [hFmap]
      _ = ∫ y, ∫ o, H (y, o) ∂ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate ∂((μC).prod λA) :=
        integral_prod H hHint
      _ = ∫ y, cyl.indicator (fun _ => xi * quantized) y ∂((μC).prod λA) := by
        congr 1
        funext y
        exact hFiber y
      _ = ∫ y in cyl, (1 : ℝ) * (xi * quantized) ∂((μC).prod λA) := by
        rw [integral_indicator hcyl]
        congr 1
        funext y
        simp
      _ = (∫ x in Aset, (1 : ℝ) ∂μC) *
          (∫ v in Bset, (xi * quantized) ∂λA) :=
        setIntegral_prod_mul (fun _ : X => (1 : ℝ)) (fun _ : V => xi * quantized)
          Aset Bset
      _ = (μC Aset).toReal * (λA Bset).toReal * xi * quantized := by
        rw [hAint, hBint]
        ring
  have hsecondIntegral :
      (∫ z in E, (firstConservedReadout rate rewards C_star C_h q t control0 z j) ^ 2 ∂μZ) =
        (μC Aset).toReal * (λA Bset).toReal * xi * quantized ^ 2 := by
    calc
      _ = ∫ z, E.indicator
          (fun z => (firstConservedReadout rate rewards C_star C_h q t control0 z j) ^ 2) z ∂μZ := by
        rw [← integral_indicator hE]
      _ = ∫ z, Hsq (F z) ∂μZ := by
        rw [hSourceSqIndicator]
        rfl
      _ = ∫ w, Hsq w ∂(MeasureTheory.Measure.map F μZ) :=
        (MeasureTheory.integral_map hF.aemeasurable hHsqmeas.aestronglyMeasurable).symm
      _ = ∫ w, Hsq w ∂(((μC).prod λA).prod (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate)) := by rw [hFmap]
      _ = ∫ y, ∫ o, Hsq (y, o) ∂ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate ∂((μC).prod λA) :=
        integral_prod Hsq hHsqint
      _ = ∫ y, cyl.indicator (fun _ => xi * quantized ^ 2) y ∂((μC).prod λA) := by
        congr 1
        funext y
        exact hFiberSq y
      _ = ∫ y in cyl, (1 : ℝ) * (xi * quantized ^ 2) ∂((μC).prod λA) := by
        rw [integral_indicator hcyl]
        congr 1
        funext y
        simp
      _ = (∫ x in Aset, (1 : ℝ) ∂μC) *
          (∫ v in Bset, (xi * quantized ^ 2) ∂λA) :=
        setIntegral_prod_mul (fun _ : X => (1 : ℝ)) (fun _ : V => xi * quantized ^ 2)
          Aset Bset
      _ = (μC Aset).toReal * (λA Bset).toReal * xi * quantized ^ 2 := by
        rw [hAint, hBsqint]
        ring
  refine ⟨hYmeas, hYsqmeas, hYint, hYsqint, ?_, ?_⟩
  · simpa only [E, xi, quantized] using hfirstIntegral
  · simpa only [E, xi, quantized] using hsecondIntegral

theorem source_elapsed_eq (z : Z) :
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = t.val := by
  simpa only [ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex] using z.property.2.2

/-- The first physical launch round is in range even when it is the final
round; the proof uses the source stratum's actual elapsed-time coordinate. -/
theorem source_first_span (z : Z) :
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed + 1 ≤ p.T := by
  rw [source_elapsed_eq rate rewards C_star C_h q t z]
  omega

/-- The actual first live window is exactly the actual launch record. -/
theorem source_first_live_window_singleton (z : Z) :
    ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val rewards C_star C_h z.property.2.1 1
      (source_first_span rate rewards C_star C_h q t z) =
      [ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h z.property.2.1
        (by rw [source_elapsed_eq rate rewards C_star C_h q t z]; exact t.isLt)] := by
  let hc := z.property.2.1
  let hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed < p.T := by
    rw [source_elapsed_eq rate rewards C_star C_h q t z]
    exact t.isLt
  let r := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h hc hs
  have hrecords :
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z.val rewards C_star C_h hc 1
        (source_first_span rate rewards C_star C_h q t z)).records = [r] := by
    have hmode : (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate z.val rewards C_star C_h hc).activeAtStart =
        ReferenceFirstLaunchNumericalCell.launchState_allActiveAtStart
          rate z.val rewards C_star C_h hc := Subsingleton.elim _ _
    simpa only [ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
      ReferenceFirstLaunchNumericalCell.firstPhysicalRun, hmode] using
      ReferenceFirstLaunchNumericalCell.firstPhysicalRun_records rate z.val rewards C_star C_h hc hs
  have hcoord : r.input.state.coordinator = .first := by
    rcases ReferenceFirstLaunchNumericalCell.actual_launch_seed
        rate z.val rewards C_star C_h z.property.2.1 with
      ⟨_, _, _, hcoordSeed, _, _, _, _⟩
    have hstate : r.input.state = ReferenceFirstLaunchNumericalCell.launchState
        rate z.val rewards C_star C_h z.property.2.1 := by
      simpa only [r] using
        (ReferenceFirstLaunchNumericalCell.firstPhysicalRecord_source_inputs
          rate z.val rewards C_star C_h z.property.2.1 hs).1
    exact congrArg (fun s => s.coordinator) hstate |>.trans hcoordSeed
  have hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
    have hdispatch := ReferenceActivePhysicalStep.dispatch_first r.input hcoord
    simp [ReferenceCollectionPhaseHistory.cutoffChosen,
      ReferenceActivePhysicalStep.prepare, hdispatch]
  change ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z.val rewards C_star C_h hc 1
        (source_first_span rate rewards C_star C_h q t z)).records = [r]
  rw [hrecords]
  simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hcut]

/-- The chronological index-zero input is exactly the same complete
numerical cell used by the first-launch source map. This keeps the selected
record, prepared ordinary states, assignment payload, pending set, complement,
cutoff, rewards, and proof-carrying cell input aligned. -/
theorem source_first_cell_chronological (z : Z) :
    let hc := z.property.2.1
    let hspan := source_first_span rate rewards C_star C_h q t z
    let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val rewards C_star C_h hc 1 hspan
    let k : Fin window.length := ⟨0, by
      dsimp only [window]
      rw [source_first_live_window_singleton rate rewards C_star C_h q t z]
      simp⟩
    (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h hc 1 hspan k).input =
        firstCell rate rewards C_star C_h q t control0 z ∧
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h hc 1 hspan =
        [firstCell rate rewards C_star C_h q t control0 z] ∧
      window = [ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h hc
        (by rw [source_elapsed_eq rate rewards C_star C_h q t z]; exact t.isLt)] := by
  classical
  dsimp only
  let c := coords z
  let hc := z.property.2.1
  let hspan := source_first_span rate rewards C_star C_h q t z
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val rewards C_star C_h hc 1 hspan
  let k : Fin window.length := ⟨0, by
    dsimp only [window]
    rw [source_first_live_window_singleton rate rewards C_star C_h q t z]
    simp⟩
  let record := window[k.val]
  let liveCell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val rewards C_star C_h hc 1 hspan k
  let physicalRecord := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h hc
    (by rw [source_elapsed_eq rate rewards C_star C_h q t z]; exact t.isLt)
  have hwindow : window = [physicalRecord] := by
    simpa only [window, physicalRecord, hc] using
      source_first_live_window_singleton rate rewards C_star C_h q t z
  have hrecordAt : record = physicalRecord := by
    dsimp only [record]
    simp [k, hwindow]
  have hrecordSource : ReferenceFirstLaunchRecordingPhysicalMarker.record
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 = physicalRecord :=
    ReferenceFirstLaunchRecordingSourceLaw.source_record_eq rate rewards C_star C_h q t control0 z
  rcases ReferenceFirstLaunchRecordingPhysicalMarker.selection_exists
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 with
    ⟨selected, hselection, hpayload, hpending, hcutoff, hcomplement, hlive, hvalid⟩
  obtain ⟨_, _, _, htimeSource, hrewardsSource⟩ :=
    ReferenceFirstLaunchRecordingPhysicalMarker.record_source_inputs rate rewards C_star C_h q t control0
      c.1 c.2.1 c.2.2
  have hordinarySource := fun i =>
    ReferenceFirstLaunchRecordingPhysicalMarker.record_prepared rate rewards C_star C_h q t control0
      c.1 c.2.1 c.2.2 i
  generalize hsourceDef : ReferenceFirstLaunchRecordingPhysicalMarker.record
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 = sourceRecord at *
  have hsourceActual : sourceRecord = record := hrecordSource.trans hrecordAt.symm
  cases hsourceActual
  have hselectionActual :
      record.output.preparation.coordinator.selection = some liveCell.selected := by
    change window[k.val].output.preparation.coordinator.selection = some liveCell.selected
    exact liveCell.selection_actual
  have hselected : liveCell.selected = selected := by
    have hEq := hselectionActual.symm.trans hselection
    exact Option.some.inj hEq
  have hpayload' : liveCell.selected.view.payload =
      ReferenceFirstLaunchRecordingPhysicalMarker.payload rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 := by
    rw [hselected]
    exact hpayload
  have hpending' : liveCell.selected.view.pendingAtChoice = Finset.univ := by
    rw [hselected]
    exact hpending
  have hcutoff' : liveCell.selected.view.cutoff = none := by
    rw [hselected]
    exact hcutoff
  have hcomplement' : liveCell.selected.view.complementWeights = fun _ => 1 := by
    rw [hselected]
    exact funext hcomplement
  have hstate' : liveCell.states = ReferenceFirstLaunchRecordingPhysicalMarker.states
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 := by
    funext i
    have hordinaryActual : (record.output.preparation.followers.followers i).configuration =
        .ordinary (liveCell.states i) (liveCell.memories i) := by
      exact liveCell.ordinary i
    have hordinaryActual' : (record.output.preparation.followers.followers i).configuration =
        .ordinary (liveCell.states i) (liveCell.memories i) := hordinaryActual
    have hordinarySourceAtRecord : (record.output.preparation.followers.followers i).configuration =
        .ordinary (ReferenceFirstLaunchRecordingPhysicalMarker.states rate rewards C_star C_h q t control0
          c.1 c.2.1 c.2.2 i) (ActiveFollowerLifecycle.initialMemory p) := hordinarySource i
    have hsame := hordinaryActual'.symm.trans hordinarySourceAtRecord
    injection hsame with hstate _hmemory
  have htime : record.input.time = t := htimeSource
  have hrewards : record.input.rewards = rewards := hrewardsSource
  have hcellInput : liveCell.input = ReferenceFirstLaunchRecordingPhysicalMarker.numericalCell
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 := by
    rw [liveCell.input_eq]
    simp only [ReferenceFirstLaunchRecordingPhysicalMarker.numericalCell,
      ReferenceFirstWindowNumericalStream.sourceCell]
    congr 1
    · simp [ReferenceFirstWindowNumericalStream.sourceArm, record, window, k,
        hwindow, hsourceDef, hrecordAt, hpayload', hpending', hstate', hcomplement']
      congr 1 <;> try simp [hpayload']
      · generalize hpayloadDef : ReferenceFirstLaunchRecordingPhysicalMarker.payload
          rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 = sourcePayload at *
        cases hpayload'
        rfl
      · rw [hpayload']
    · simp [record, window, k, hwindow, hsourceDef, hrecordAt]
    · exact congrArg AssignmentStartPayload.Input.rate hpayload'
  have hlist : ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h hc 1 hspan =
      [liveCell.input] := by
    simp [ReferenceFirstWindowNumericalStream.actualLiveSourceCells, liveCell, k, window, hwindow]
    congr 1
  refine ⟨?_, ?_, hwindow⟩
  · simpa only [liveCell, k, firstCell] using hcellInput
  · rw [hlist, hcellInput]
    rfl

/-- At the one-cell prefix, the stopped physical boundary is the successor of
the very same chronological record. The prefix and fold equations expose the
actual step; the singleton first-live window identifies its record. -/
theorem source_first_boundary_successor (z : Z) :
    let hc := z.property.2.1
    let hspan := source_first_span rate rewards C_star C_h q t z
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed
    let initial := ReferenceFirstLaunchNumericalCell.launchState
      rate z.val rewards C_star C_h hc
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate z.val rewards C_star C_h hc
    let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h hc 1 hspan
    let hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed < p.T := by
      rw [source_elapsed_eq rate rewards C_star C_h q t z]
      exact t.isLt
    let firstRecord := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
      rate z.val rewards C_star C_h hc hs
    ∃ hprefix : start + 1 ≤ p.T,
      window = [firstRecord] ∧
      (ReferenceActivePhysicalHorizon.run initial z.val.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards start 1
        hprefix seed.activeAtStart).finalState = firstRecord.output.next := by
  classical
  dsimp only
  let hc := z.property.2.1
  let hspan := source_first_span rate rewards C_star C_h q t z
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed
  have hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed < p.T := by
    rw [source_elapsed_eq rate rewards C_star C_h q t z]
    exact t.isLt
  let firstRecord := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
    rate z.val rewards C_star C_h hc hs
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate z.val rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z.val rewards C_star C_h hc
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z.val rewards C_star C_h hc 1 hspan
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z.val rewards C_star C_h hc 1 hspan
  let qparams := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let overflowPrefix := UnstoppedRecordedQueueComparison.firstOverflowPrefix qparams cells
  have hwindow := source_first_live_window_singleton rate rewards C_star C_h q t z
  have hwindowLength : window.length = 1 := by
    change (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h hc 1 hspan).length = 1
    rw [hwindow]
    rfl
  have hb : 1 ≤ window.length := by rw [hwindowLength]
  have hκ : 1 ≤ overflowPrefix := by
    exact UnstoppedRecordedQueueComparison.first_overflow_prefix_pos qparams cells
  have hcommon :=
    ReferenceFirstLiveStoppedQueueComparison.actual_first_live_stopped_queue_common_boundary
      rate z.val rewards C_star C_h hc 1 hspan 1 hb
  dsimp only at hcommon
  have hphysical := hcommon.2.2.2.2.1 hκ
  rcases hphysical with ⟨hprefix, _hboundaryFacts⟩
  let hmode := seed.activeAtStart
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p z.val
  let entry : ReferenceActivePhysicalHorizon.CalendarEntry p start :=
    ⟨start, le_rfl, by simpa only [start] using hs⟩
  have hsuccessor := ReferenceActivePhysicalHorizon.run_successor_step
    initial z.val.1.2 selected rewards start 0 (by omega) hmode
  have hfold := ReferenceActivePhysicalHorizon.foldRound_equations
    initial z.val.1.2 selected rewards start hmode
    (ReferenceActivePhysicalHorizon.run initial z.val.1.2 selected rewards start 0
      (by omega) hmode) entry
  have hinput :
      ReferenceActivePhysicalHorizon.roundInputAt initial z.val.1.2 selected rewards
        start hmode
        (ReferenceActivePhysicalHorizon.run initial z.val.1.2 selected rewards start 0
          (by omega) hmode) entry =
      firstRecord.input := by
    simp [ReferenceFirstLaunchNumericalCell.firstPhysicalRecord,
      ReferenceActivePhysicalHorizon.roundInputAt,
      ReferenceActivePhysicalHorizon.run_zero_final, firstRecord, initial, selected, entry, start]
  have hfinalPhysical :
      (ReferenceActivePhysicalHorizon.run initial z.val.1.2 selected rewards start 1
        hprefix hmode).finalState =
        firstRecord.output.next := by
    calc
      (ReferenceActivePhysicalHorizon.run initial z.val.1.2 selected rewards start 1
        hprefix hmode).finalState =
          (ReferenceActivePhysicalHorizon.foldRound initial z.val.1.2 selected rewards
            start hmode
            (ReferenceActivePhysicalHorizon.run initial z.val.1.2 selected rewards start 0
              (by omega) hmode) entry).finalState := by
                exact congrArg (fun r : ReferenceActivePhysicalHorizon.Run initial => r.finalState)
                  hsuccessor
      _ = (ReferenceActivePhysicalHorizon.roundInputAt initial z.val.1.2 selected rewards
          start hmode
          (ReferenceActivePhysicalHorizon.run initial z.val.1.2 selected rewards start 0
            (by omega) hmode) entry |> ReferenceActivePhysicalStep.step).next := hfold.1
      _ = firstRecord.output.next := by
            rw [hinput]
            rfl
  refine ⟨hprefix, ?_, hfinalPhysical⟩
  simpa only [window, firstRecord] using hwindow

include control0 in
/-- The initial numerical learner is produced by the original initialization,
with the false incoming overflow flag. No next-overflow condition is required. -/
theorem source_initial_coordinator_learner (z : Z) :
    ReferenceInitializationRun.coordinatorLearner
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)) =
      some (RecordedQueueRun.initialState p.K) := by
  have h := ReferenceFirstLaunchRecordingPhysicalMarker.initial_coordinator_learner
    rate rewards C_star C_h q t control0 (coords z).1 (coords z).2.1 (coords z).2.2
  rw [ReferenceFirstLaunchRecordingSourceLaw.source_recover] at h
  exact h.1

/-- The actual successor stores the common update on the known complement.
An unoccupied follower still stores zero registers and its genuine appended
buffer; its singleton replay is virtual. The other branch carries the actual
retained DOWN witness and stored registers. Both branches are produced by the
existing first-live boundary theorem, through its inclusive first update. -/
theorem source_first_physical_storage (z : Z) :
    let c := coords z
    let record := ReferenceFirstLaunchRecordingPhysicalMarker.record
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2
    let payload := ReferenceFirstLaunchRecordingPhysicalMarker.payload
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate z.val rewards C_star C_h z.property.2.1
    ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
      (base : Fin (p.m - 1) → ℕ),
      record.output.next.coordinator = .live r owned base ∧
      r.payload = payload ∧ (∀ i, base i = 0) ∧
      (∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
        (r.complementScores a, owned.queue a) =
          (firstUpdate rate rewards C_star C_h q t control0 z).registers a.1 ∧
        owned.previousService a =
          min (4 * rate.n) (firstArrival rate rewards C_star C_h q t control0 z a.1)) ∧
      ∀ i : Fin (p.m - 1), ∃ sb mb,
        record.output.next.followers i = .ordinary sb mb ∧
        ((sb.status ≠ .unoccupied ∧
          sb.lastDown = some (r.payload.downRecord i) ∧
          (sb.S, sb.backlog) = (firstUpdate rate rewards C_star C_h q t control0 z).registers
            (r.payload.assignment.assigned i) ∧
          sb.delta = min (4 * rate.n)
            (firstArrival rate rewards C_star C_h q t control0 z (r.payload.assignment.assigned i)) ∧
          ReferenceAcceptedUpFollowerHistory.RetainedDown record i (r.payload.downRecord i)) ∨
        (sb.status = .unoccupied ∧
          sb.lastDown = none ∧ sb.S = 0 ∧ sb.delta = 0 ∧ sb.backlog = 0 ∧
          sb.buffer = (seed.followers i).buffer ++
            ReferenceFollowerBufferProvenance.logEmission i record ∧
          ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
            [record] i 1 (r.payload.downRecord i) 1 =
            [(true, firstArrival rate rewards C_star C_h q t control0 z
              (r.payload.assignment.assigned i))] ∧
          QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              [record] i 1 (r.payload.downRecord i) 1) =
            (firstUpdate rate rewards C_star C_h q t control0 z).registers
              (r.payload.assignment.assigned i))) := by
  classical
  dsimp only
  let c := coords z
  let record := ReferenceFirstLaunchRecordingPhysicalMarker.record
    rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2
  let hc := z.property.2.1
  let hspan := source_first_span rate rewards C_star C_h q t z
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z.val rewards C_star C_h hc
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z.val rewards C_star C_h hc 1 hspan
  let qparams := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have hcell := source_first_cell_chronological rate rewards C_star C_h q t control0 z
  dsimp only at hcell
  have hcells : cells = [firstCell rate rewards C_star C_h q t control0 z] := hcell.2.1
  have henabled : (firstCell rate rewards C_star C_h q t control0 z).enabled = true :=
    (ReferenceFirstLaunchRecordingPhysicalMarker.numerical_cell_readout
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2).1
  have hrun : RecordedQueueRun.run qparams (cells.take 1) =
      firstUpdate rate rewards C_star C_h q t control0 z := by
    rw [hcells]
    rfl
  have hb : 1 ≤ (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h hc 1 hspan).length := by
    rw [source_first_live_window_singleton rate rewards C_star C_h q t z]
    exact le_rfl
  have hκ : 1 ≤ UnstoppedRecordedQueueComparison.firstOverflowPrefix qparams cells :=
    UnstoppedRecordedQueueComparison.first_overflow_prefix_pos qparams cells
  have hcommon := ReferenceFirstLiveStoppedQueueComparison.actual_first_live_stopped_queue_common_boundary
    rate z.val rewards C_star C_h hc 1 hspan 1 hb
  dsimp only at hcommon
  have hafter (a : Fin p.K) :
      UnstoppedRecordedQueueComparison.unstoppedReplay qparams cells 1 a =
        (firstUpdate rate rewards C_star C_h q t control0 z).registers a := by
    have h := hcommon.2.2.1 a
    rw [hrun, Nat.min_eq_left hκ] at h
    exact h.symm
  have hbefore (a : Fin p.K) :
      UnstoppedRecordedQueueComparison.unstoppedReplay qparams cells (1 - 1) a = (0, 0) := by
    simp [UnstoppedRecordedQueueComparison.unstoppedReplay, QueueReplay.replay]
  obtain ⟨hprefix, _hzero, hpositive⟩ := hcommon.2.2.2.2.1 hκ
  let boundary := ReferenceActivePhysicalHorizon.run
    (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h hc)
    z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards
    (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed)
    1 hprefix seed.activeAtStart
  have hrecord := ReferenceFirstLaunchRecordingSourceLaw.source_record_eq
    rate rewards C_star C_h q t control0 z
  have hrecords : boundary.records = [record] := by
    have h := ReferenceFirstLaunchNumericalCell.firstPhysicalRun_records
      rate z.val rewards C_star C_h hc
      (by rw [source_elapsed_eq rate rewards C_star C_h q t z]; exact t.isLt)
    rw [← hrecord] at h
    exact h
  have hfinal : boundary.finalState = record.output.next := by
    obtain ⟨_, _, h⟩ := source_first_boundary_successor rate rewards C_star C_h q t z
    rw [← hrecord] at h
    exact h
  obtain ⟨r, owned, base, hcoord, _hsigma, _hn, hbase, hbirth, hfast, hfollowers,
    _hslow, _hcomplement⟩ := hpositive (by decide)
  obtain ⟨birth, hmem, hborn, _htime⟩ := hbirth
  rw [hrecords, List.mem_singleton] at hmem
  subst birth
  obtain ⟨installed, arm, _hchosen, hbranch, hP, _hcoordinates, _hassignment, _hsigma,
    _hanchor, _hweights, _hdown, _hqueues, _hpending, _hscores, _hqueue, _hservice,
    _hbase, _hstrict, _hupper, _hlast⟩ :=
    ReferenceFirstLaunchRecordingPhysicalMarker.installation_exists
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2
  have hpayload : r.payload = ReferenceFirstLaunchRecordingPhysicalMarker.payload
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 := by
    change ReferenceAssignmentPayloadPersistence.InstallationBirth record r.payload at hborn
    rw [ReferenceAssignmentPayloadPersistence.InstallationBirth, hbranch] at hborn
    exact hborn.1.trans hP
  refine ⟨r, owned, base, hfinal ▸ hcoord, hpayload, hbase, ?_, ?_⟩
  · intro a
    obtain ⟨hregisters, hservice⟩ := hfast a
    rw [hrun] at hregisters
    rw [hafter, hbefore] at hservice
    rw [(source_first_update rate rewards C_star C_h q t control0 z).1 a.1 |>.2.1] at hservice
    exact ⟨hregisters, by simpa only [Nat.sub_zero] using hservice⟩
  · intro i
    obtain ⟨sb, mb, hstate, hoccupied, hunoccupied⟩ := hfollowers i
    refine ⟨sb, mb, hfinal ▸ hstate, ?_⟩
    by_cases hstatus : sb.status ≠ .unoccupied
    · left
      refine ⟨hstatus, ?_⟩
      obtain ⟨hlast, hregisters, hservice, k, _hk, hdown⟩ := hoccupied hstatus
      rw [hrun] at hregisters
      rw [hafter, hbefore] at hservice
      rw [(source_first_update rate rewards C_star C_h q t control0 z).1 _ |>.2.1] at hservice
      have hwindow := source_first_live_window_singleton rate rewards C_star C_h q t z
      rw [← hrecord] at hwindow
      have hAt : (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate z.val rewards C_star C_h hc 1 hspan)[k.val] = record := by
        simp [hwindow, record, c]
      rw [hAt] at hdown
      exact ⟨hlast, hregisters, by simpa only [Nat.sub_zero] using hservice, hdown⟩
    · right
      have hun : sb.status = .unoccupied := not_not.mp hstatus
      refine ⟨hun, ?_⟩
      obtain ⟨hlast, hS, hdelta, hbacklog, hbuffer, hqueue, hreplay⟩ := hunoccupied hun
      change sb.buffer = (seed.followers i).buffer ++
        (boundary.records.take 1).flatMap (ReferenceFollowerBufferProvenance.logEmission i) at hbuffer
      change ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
        boundary.records i 1 (r.payload.downRecord i) 1 = _ at hqueue
      change QueueReplay.replay (4 * rate.n) (0, 0)
        (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
          boundary.records i 1 (r.payload.downRecord i) 1) = _ at hreplay
      rw [hrecords] at hbuffer hqueue hreplay
      rw [hafter] at hreplay
      refine ⟨hlast, hS, hdelta, hbacklog, ?_, ?_, hreplay⟩
      · simpa only [List.take_succ_cons, List.take_zero, List.flatMap_cons,
          List.flatMap_nil, List.append_nil] using hbuffer
      · change ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
          [record] i 1 (r.payload.downRecord i) 1 =
          (cells.take 1).map (fun cell =>
            (cell.enabled, RecordedQueueRun.quantizedArrival qparams cell
              (r.payload.assignment.assigned i))) at hqueue
        rw [hcells] at hqueue
        simpa only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          henabled, firstArrival] using hqueue

/-- The actual FIRST installation has unit weights and zero registers, and its
actual recording, service, confirmation, and finish calls succeed. These are
outputs of the existing chronological service producer, with arrivals and
stored registers identified with this same first numerical update. -/
theorem source_first_coordinator_service (z : Z) :
    let c := coords z
    let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val rewards C_star C_h z.property.2.1 1
        (source_first_span rate rewards C_star C_h q t z)
    let k : Fin W.length := ⟨0, by
      dsimp only [W]
      rw [source_first_live_window_singleton rate rewards C_star C_h q t z]
      exact Nat.zero_lt_succ 0⟩
    let record := W[k.val]
    ∃ (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
        (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput record.input)))
      (arm : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
        installed.startRoundResult installed.registers.time installed.registers.complementWeights record.input.row),
      record.output.preparation.coordinator = .first (.chosen installed arm) ∧
      installed.registers.payload = ReferenceFirstLaunchRecordingPhysicalMarker.payload
        rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 ∧
      (∀ a, installed.registers.payload.anchor a = 1) ∧
      (∀ a, installed.registers.complementWeights a = 1) ∧
      (∀ a, installed.registers.payload.queues a = 0) ∧
      (∀ a, installed.registers.complementScores a = 0) ∧
      (∀ a, installed.ownedRegisters.queue a = 0) ∧
      (∀ a, installed.ownedRegisters.previousService a = 0) ∧
      (∀ i, installed.followerBaseScore i = 0) ∧
      ∃ recording serviced pending finished,
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation
            installed.registers installed.startRoundResult) = some recording ∧
        record.output.coordinator.recording = some recording ∧
        CoordinatorLiveServiceFinish.servicePass installed.registers
          installed.ownedRegisters recording = .ok serviced ∧
        (∀ a : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
          serviced.arrival a = firstArrival rate rewards C_star C_h q t control0 z a.1 ∧
          serviced.service a = min (4 * rate.n)
            (firstArrival rate rewards C_star C_h q t control0 z a.1) ∧
          (serviced.score a, serviced.queue a) =
            (firstUpdate rate rewards C_star C_h q t control0 z).registers a.1 ∧
          serviced.previousService a = min (4 * rate.n)
            (firstArrival rate rewards C_star C_h q t control0 z a.1)) ∧
        CoordinatorLocalArmChoice.confirmationUpdate installed.registers.payload
          installed.startRoundResult.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p installed.startRoundResult.clock.u)
          record.input.time record.input.row record.output.preparation.coordinatorObservation = some pending ∧
        CoordinatorPhaseClock.finishRound p rate.eta.val record.input.time
          installed.startRoundResult.clock pending record.input.row = .ok finished ∧
        finished.pending = pending ∧ record.output.coordinator.failure = none ∧
        record.output.next.coordinator =
          .live {
            payload := installed.registers.payload
            priorClock := finished.clock
            pendingAtChoice := finished.pending
            time := record.input.time
            gridBoundary := finished.clock.g
            complementScores := serviced.score }
            { queue := serviced.queue, previousService := serviced.previousService }
            installed.followerBaseScore := by
  classical
  dsimp only
  let c := coords z
  let hc := z.property.2.1
  let hspan := source_first_span rate rewards C_star C_h q t z
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z.val rewards C_star C_h hc 1 hspan
  let k : Fin W.length := ⟨0, by
    dsimp only [W]
    rw [source_first_live_window_singleton rate rewards C_star C_h q t z]
    exact Nat.zero_lt_succ 0⟩
  let record := W[k.val]
  have hchron := source_first_cell_chronological rate rewards C_star C_h q t control0 z
  dsimp only at hchron
  have hcell : (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate z.val rewards C_star C_h hc 1 hspan k).input =
      firstCell rate rewards C_star C_h q t control0 z := hchron.1
  have hrecord := ReferenceFirstLaunchRecordingSourceLaw.source_record_eq
    rate rewards C_star C_h q t control0 z
  have hAt : record = ReferenceFirstLaunchRecordingPhysicalMarker.record
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 := by
    have hW := source_first_live_window_singleton rate rewards C_star C_h q t z
    simpa only [record, W, k, hW, List.getElem_cons_zero, c] using hrecord.symm
  have hcoord : record.input.state.coordinator = .first := by
    rw [hAt]
    exact (ReferenceFirstLaunchRecordingPhysicalMarker.record_seed
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2).1
  obtain ⟨installed, arm, hchosen⟩ :=
    ReferenceFirstAssignmentFibreStep.dispatchFirst_chosen_exists
      (ReferenceActivePhysicalStep.firstInput record.input)
  have hbranch : record.output.preparation.coordinator = .first (.chosen installed arm) := by
    rw [record.output_eq]
    change ReferenceActivePhysicalStep.dispatch record.input = _
    rw [ReferenceActivePhysicalStep.dispatch_first record.input hcoord, hchosen]
  have hinstalled := ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
    record.input installed arm hchosen
  have hP : installed.registers.payload = ReferenceFirstLaunchRecordingPhysicalMarker.payload
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 := by
    have hfirst : installed.registers.payload =
        (AssignmentStartPayload.Input.ofFirstAssignment
          (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput record.input)) :
            ReferenceActivePhysicalStep.Payload rate) := by
      rw [hinstalled]
      exact CoordinatorAssignmentRegisterInstall.first_registers_payload _
    have hsecond : (AssignmentStartPayload.Input.ofFirstAssignment
        (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput record.input)) :
          ReferenceActivePhysicalStep.Payload rate) =
        ReferenceFirstLaunchRecordingPhysicalMarker.payload
          rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 :=
      congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        (AssignmentStartPayload.Input.ofFirstAssignment
          (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput r.input)) :
            ReferenceActivePhysicalStep.Payload rate)) hAt
    exact hfirst.trans hsecond
  have hanchor : ∀ a, installed.registers.payload.anchor a = 1 := by
    rw [hinstalled]
    exact CoordinatorAssignmentRegisterInstall.first_payload_anchor_one _
  have hweights : ∀ a, installed.registers.complementWeights a = 1 := by
    rw [hinstalled]
    exact CoordinatorAssignmentRegisterInstall.first_complementWeight_one _
  have hqueues : ∀ a, installed.registers.payload.queues a = 0 := by
    rw [hP]
    intro a
    rfl
  obtain ⟨hscores, hqueue, hservice, hbase⟩ := ReferenceActivePhysicalStep.dispatchFirst_zero_seed
    record.input installed arm hchosen
  have hactual := ReferenceFirstLiveCoordinatorNumericalService.actual_first_live_coordinator_numerical_service
    rate z.val rewards C_star C_h hc 1 hspan k
  dsimp only at hactual
  rw [hbranch] at hactual
  obtain ⟨recording, serviced, pending, finished, hrun, hrecording, hpass, _hpayload,
    _henabled, harrival, hsteps, _hbounds, _hzero, hconfirm, hfinish, hpending,
    hfailure, _hup, _hbank, hnext⟩ := hactual
  refine ⟨installed, arm, hbranch, hP, hanchor, hweights, hqueues, hscores,
    hqueue, hservice, hbase, recording, serviced, pending, finished,
    hrun, hrecording, hpass, ?_, hconfirm, hfinish, hpending, hfailure, hnext⟩
  intro a
  have hraw : serviced.arrival a = firstArrival rate rewards C_star C_h q t control0 z a.1 := by
    simpa only [hcell, firstArrival] using harrival a
  obtain ⟨hserved, hscore, hbacklog, hprevious, _htransition⟩ := hsteps a
  rw [hcell, hqueue a, Nat.zero_add] at hserved hbacklog
  change serviced.service a = min (4 * rate.n)
    (firstArrival rate rewards C_star C_h q t control0 z a.1) at hserved
  have hregisters : (serviced.score a, serviced.queue a) =
      (firstUpdate rate rewards C_star C_h q t control0 z).registers a.1 := by
    rw [(source_first_update rate rewards C_star C_h q t control0 z).1 a.1 |>.2.1]
    rw [hscore, hscores a, Nat.zero_add, hbacklog, hserved]
    rfl
  exact ⟨hraw, hserved, hregisters, hprevious.trans hserved⟩

/-- The same first update is the existing machine's execution on the complete
chronological first-window input list. -/
theorem source_first_chronological_execute (z : Z) :
    RecordedQueueRun.execute (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val rewards C_star C_h
        z.property.2.1 1 (source_first_span rate rewards C_star C_h q t z))
      (RecordedQueueRun.initialState p.K) =
      firstUpdate rate rewards C_star C_h q t control0 z := by
  rw [(source_first_cell_chronological rate rewards C_star C_h q t control0 z).2.1]
  rfl

/-- Each assigned arm's arrival is the contribution of the actual current log
emission. Its conserved normalized value is M's same original-source saved
readout, without claiming that deferred service is physically stored. -/
theorem source_first_saved_arrival (z : Z) (i : Fin (p.m - 1)) :
    let c := coords z
    let record := ReferenceFirstLaunchRecordingPhysicalMarker.record
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2
    let payload := ReferenceFirstLaunchRecordingPhysicalMarker.payload
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2
    SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ) rate.eta.val
      (payload.exponent (payload.assignment.assigned i)) (payload.assignment.assigned i)
      (record.input.time.val + 1) (ReferenceFollowerBufferProvenance.logEmission i record) =
      firstArrival rate rewards C_star C_h q t control0 z (payload.assignment.assigned i) ∧
    firstConservedReadout rate rewards C_star C_h q t control0 z (payload.assignment.assigned i) =
      ReferenceFirstLaunchSavedSourceMoments.sourceSaved rate rewards C_star C_h q t control0 z i := by
  dsimp only
  let c := coords z
  let payload := ReferenceFirstLaunchRecordingPhysicalMarker.payload
    rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2
  have h := ReferenceFirstLaunchRecordingPhysicalMarker.current_saved_eq_numerical_arrival
    rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 i
  refine ⟨h, ?_⟩
  have htotal := (source_first_update rate rewards C_star C_h q t control0 z).1
    (payload.assignment.assigned i) |>.2.2
  change (((firstUpdate rate rewards C_star C_h q t control0 z).registers
    (payload.assignment.assigned i)).1 + ((firstUpdate rate rewards C_star C_h q t control0 z).registers
    (payload.assignment.assigned i)).2 : ℕ) / (rate.eta.val * (D p : ℝ)) =
    ((ReferenceFirstLaunchRecordingSourceLaw.currentSaved
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 i : ℕ) : ℝ) /
      (rate.eta.val * (D p : ℝ))
  rw [htotal]
  exact congrArg (fun n : ℕ => (n : ℝ) / (rate.eta.val * (D p : ℝ))) h.symm

/-- The first- and second-moment coefficients obey the manuscript's rounding
and second-moment bounds for every arm, including a zero grid reward. -/
theorem first_update_moment_coefficients_bounds (j : Fin p.K) :
    let rho := ((rewards t j).val : ℝ) / (D p : ℝ)
    let xi := CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j
    let value := QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val xi rho
    rho - xi / (rate.eta.val * (D p : ℝ)) ≤ xi * value ∧
      xi * value ≤ rho ∧ xi * value ^ 2 ≤ rho ^ 2 / xi ∧ rho ^ 2 / xi ≤ 1 / xi := by
  dsimp only
  have hxi := CanonicalRecordingRates.xi_pos p rate.eta.property (fun _ => 1) j
  have hrho : ((rewards t j).val : ℝ) / (D p : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    have hD : 0 < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
    refine ⟨div_nonneg (Nat.cast_nonneg _) hD.le, (div_le_one hD).2 ?_⟩
    exact_mod_cast Nat.le_of_lt_succ (rewards t j).isLt
  refine ⟨QuantizedRecordingMoments.quantizedValue_roundingError
      _ _ _ _ (D_pos p) rate.eta.property hxi hrho,
    QuantizedRecordingMoments.quantizedValue_firstMoment_le
      _ _ _ _ (D_pos p) rate.eta.property hxi hrho,
    QuantizedRecordingMoments.quantizedValue_secondMoment_le
      _ _ _ _ (D_pos p) rate.eta.property hxi hrho, ?_⟩
  exact div_le_div_of_nonneg_right
    (pow_le_one₀ hrho.1 hrho.2) hxi.le

end Bandits.Support.ReferenceFirstLaunchCommonUpdateSource

end
