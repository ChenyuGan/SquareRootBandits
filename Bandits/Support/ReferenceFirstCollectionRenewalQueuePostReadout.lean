/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Actual first-renewal accepted-complement post readout

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:93-188,245-318`,
`sources/zip4/manuscript/05_binary_transport.tex:352-431`, and
`sources/zip4/manuscript/06_interruptions.tex:399-426`.

The literal integer records below give a measurable observation of the existing
queue step. Its actual-cell characterization retains the same existential call
and recording supplied by the accepted-complement identity. No actual call is
selected on the whole pair carrier. The incoming overflow flag disables later
updates; an overflow first caused by this update does not remove its service.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments
open Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix
open Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability

namespace Bandits.Support.ReferenceFirstCollectionRenewalQueuePostReadout

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
variable (control0 : ContinuousLearningRows.TimeControl p)

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local notation "B" =>
  ReferenceFirstCollectionRenewalAcceptedComplementMoments.Pair rate rewards C_star C_h u t
local notation "mu" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t
local notation "qp" => ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- The recorder's existing floor index, accepted only before incoming
overflow and on the coordinator's actual complement gate event. -/
def integerArrival (b : B) (j : Fin p.K) : ℕ :=
  if (incoming rate rewards C_star C_h u t b.2).overflow then 0
  else (ReferenceFirstCollectionRenewalGateCoefficient.gateEvent
    rate rewards C_star C_h u t j).indicator
      (fun b => QuantizedRecordingMoments.quantizedIndex (D p) rate.eta.val
        (ReferenceFirstCollectionRenewalComplementMoments.xi
          rate rewards C_star C_h u t b j)
        (ReferenceFirstCollectionRenewalComplementMoments.r rewards t j)) b

/-- Every arm is enabled before overflow, including arms with zero arrival. -/
def queueRecord (b : B) (j : Fin p.K) : Bool × ℕ :=
  (!(incoming rate rewards C_star C_h u t b.2).overflow,
    integerArrival rate rewards C_star C_h u t b j)

/-- The literal integer transition, with the source service capacity. -/
def postRegisters (b : B) (j : Fin p.K) : ℕ × ℕ :=
  QueueReplay.transition (4 * rate.n)
    ((incoming rate rewards C_star C_h u t b.2).registers j)
    (queueRecord rate rewards C_star C_h u t b j)

/-- Registers, post-update overflow, and chronological accepted records, in
the existing `stateReadout` carrier and field order. -/
def postReadout (b : B) :
    (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))) :=
  (postRegisters rate rewards C_star C_h u t b,
    (incoming rate rewards C_star C_h u t b.2).overflow ||
      decide (∃ j, 32 * (postRegisters rate rewards C_star C_h u t b j).2 > D p),
    fun j => (incoming rate rewards C_star C_h u t b.2).records j ++
      [queueRecord rate rewards C_star C_h u t b j])

/-- The literal index normalizes to the accepted estimator on every pair,
without an actual-call witness or an almost-everywhere restriction. -/
theorem integerArrival_div_n (b : B) (j : Fin p.K) :
    (integerArrival rate rewards C_star C_h u t b j : ℝ) / (rate.n : ℝ) =
      acceptedA rate rewards C_star C_h u t j b := by
  by_cases hf : (incoming rate rewards C_star C_h u t b.2).overflow = true
  · simp [integerArrival, acceptedA, hf]
  · by_cases hg : b ∈ ReferenceFirstCollectionRenewalGateCoefficient.gateEvent
        rate rewards C_star C_h u t j
    · simp [integerArrival, acceptedA, hf,
        ReferenceFirstCollectionRenewalComplementMoments.a, hg,
        ReferenceFirstCollectionRenewalComplementMoments.q,
        QuantizedRecordingMoments.quantizedValue, rate.n_scale]
    · simp [integerArrival, acceptedA, hf,
        ReferenceFirstCollectionRenewalComplementMoments.a, hg]

/-- This floor is a proved reconstruction of the same integer index, rather
than a second definition of physical rounding. -/
theorem integerArrival_eq_floor (b : B) (j : Fin p.K) :
    integerArrival rate rewards C_star C_h u t b j =
      Nat.floor ((rate.n : ℝ) * acceptedA rate rewards C_star C_h u t j b) := by
  have hn : (rate.n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos)
  have hscale : (rate.n : ℝ) * acceptedA rate rewards C_star C_h u t j b =
      (integerArrival rate rewards C_star C_h u t b j : ℝ) := by
    rw [← integerArrival_div_n rate rewards C_star C_h u t b j]
    field_simp [hn]
  rw [hscale, Nat.floor_natCast]

/-- Borelness follows from the accepted real estimator and its exact
integer reconstruction; no real coordinate is given a discrete structure. -/
theorem measurable_integerArrival (j : Fin p.K) :
    Measurable (fun b : B => integerArrival rate rewards C_star C_h u t b j) := by
  have h : Measurable (fun b : B =>
      Nat.floor ((rate.n : ℝ) * acceptedA rate rewards C_star C_h u t j b)) :=
    Nat.measurable_floor.comp
      (measurable_const.mul (measurable_acceptedA rate rewards C_star C_h u t j))
  convert h using 1
  funext b
  exact integerArrival_eq_floor rate rewards C_star C_h u t b j

private theorem measurable_incoming_pair :
    Measurable (fun b : B => incomingReadout rate rewards C_star C_h u t b.2) :=
  (measurable_incomingReadout rate rewards C_star C_h u t).comp measurable_snd

private theorem measurable_incoming_overflow :
    Measurable (fun b : B => (incoming rate rewards C_star C_h u t b.2).overflow) :=
  measurable_fst.comp (measurable_snd.comp
    (measurable_incoming_pair rate rewards C_star C_h u t))

/-- The enabled flag and integer arrival are jointly measurable. -/
theorem measurable_queueRecord (j : Fin p.K) :
    Measurable (fun b : B => queueRecord rate rewards C_star C_h u t b j) := by
  exact ((measurable_of_countable (fun f : Bool => !f)).comp
    (measurable_incoming_overflow rate rewards C_star C_h u t)).prodMk
      (measurable_integerArrival rate rewards C_star C_h u t j)

private theorem measurable_queueRecords :
    Measurable (fun b : B => fun j : Fin p.K =>
      queueRecord rate rewards C_star C_h u t b j) := by
  apply measurable_pi_iff.mpr
  intro j
  exact measurable_queueRecord rate rewards C_star C_h u t j

private theorem measurable_incoming_registers :
    Measurable (fun b : B =>
      (incoming rate rewards C_star C_h u t b.2).registers) :=
  measurable_fst.comp (measurable_incoming_pair rate rewards C_star C_h u t)

private theorem measurable_registerTransition {K : ℕ} (capacity : ℕ) :
    Measurable (fun v : (Fin K → ℕ × ℕ) × (Fin K → Bool × ℕ) => fun j =>
      QueueReplay.transition capacity (v.1 j) (v.2 j)) :=
  measurable_of_countable _

/-- Borelness of all post registers uses only countable natural fields. -/
theorem measurable_postRegisters :
    Measurable (postRegisters rate rewards C_star C_h u t) := by
  let fields (b : B) : (Fin p.K → ℕ × ℕ) × (Fin p.K → Bool × ℕ) :=
    ((incomingReadout rate rewards C_star C_h u t b.2).1,
      fun j => queueRecord rate rewards C_star C_h u t b j)
  let transition (v : (Fin p.K → ℕ × ℕ) × (Fin p.K → Bool × ℕ)) :=
    fun j => QueueReplay.transition (4 * rate.n) (v.1 j) (v.2 j)
  have hfields : Measurable fields :=
    (measurable_fst.comp (measurable_incoming_pair rate rewards C_star C_h u t)).prodMk
      (measurable_queueRecords rate rewards C_star C_h u t)
  have htransition : Measurable transition :=
    measurable_registerTransition (K := p.K) (4 * rate.n)
  have heq : postRegisters rate rewards C_star C_h u t = transition ∘ fields := by
    funext b j
    rfl
  rw [heq]
  exact htransition.comp hfields

private instance recordListMeasurableSingleton :
    MeasurableSingletonClass (List (Bool × ℕ)) where
  measurableSet_singleton l := by
    let : MeasurableSingletonClass (Unit ⊕ (Bool × ℕ)) := ⟨fun x => by
      cases x with
      | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
      | inr a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inr_image⟩
    have hinj : Function.Injective (listObservationCoordinates (α := Bool × ℕ)) := by
      intro a b h
      have hlen : a.length = b.length := congrArg Prod.fst h
      apply List.ext_getElem hlen
      intro i hi hj
      have he := congrFun (congrArg Prod.snd h) i
      simpa only [listObservationCoordinates, listObservationAt,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Sum.inr.injEq] using he
    have hm := measurable_listObservationCoordinates (α := Bool × ℕ)
    have hh := hm (MeasurableSet.singleton (listObservationCoordinates l))
    convert hh using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

private theorem measurable_readoutUpdate {K : ℕ} (capacity denominator : ℕ) :
    Measurable (fun v :
      ((Fin K → ℕ × ℕ) × (Bool × (Fin K → List (Bool × ℕ)))) ×
        (Fin K → Bool × ℕ) =>
      let registers := fun j => QueueReplay.transition capacity (v.1.1 j) (v.2 j)
      (registers, v.1.2.1 || decide (∃ j, 32 * (registers j).2 > denominator),
        fun j => v.1.2.2 j ++ [v.2 j])) :=
  measurable_of_countable _

/-- The full literal post observation is ambient Borel on the unchanged pair
carrier, including the updated overflow flag and appended no-op records. -/
theorem measurable_postReadout :
    Measurable (postReadout rate rewards C_star C_h u t) := by
  let fields (b : B) :=
    (incomingReadout rate rewards C_star C_h u t b.2,
      fun j => queueRecord rate rewards C_star C_h u t b j)
  let update (v :
      ((Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))) ×
        (Fin p.K → Bool × ℕ)) :=
    let registers := fun j => QueueReplay.transition (4 * rate.n) (v.1.1 j) (v.2 j)
    (registers, v.1.2.1 || decide (∃ j, 32 * (registers j).2 > D p),
      fun j => v.1.2.2 j ++ [v.2 j])
  have hfields : Measurable fields :=
    (measurable_incoming_pair rate rewards C_star C_h u t).prodMk
      (measurable_queueRecords rate rewards C_star C_h u t)
  have hupdate : Measurable update :=
    measurable_readoutUpdate (K := p.K) (4 * rate.n) (D p)
  have heq : postReadout rate rewards C_star C_h u t = update ∘ fields := by
    funext b
    rfl
  rw [heq]
  exact hupdate.comp hfields

/-- Incoming normalized backlog of the existing queue. -/
def backlogBefore (b : B) (j : Fin p.K) : ℝ :=
  ((incoming rate rewards C_star C_h u t b.2).registers j).2 / (rate.n : ℝ)

/-- Post-update normalized backlog of the literal readout. -/
def backlogAfter (b : B) (j : Fin p.K) : ℝ :=
  (postRegisters rate rewards C_star C_h u t b j).2 / (rate.n : ℝ)

/-- Actual incoming score weight, with the original denominator and score. -/
def weightBefore (b : B) (j : Fin p.K) : ℝ :=
  (1 + 1 / (D p : ℝ)) ^ ((incoming rate rewards C_star C_h u t b.2).registers j).1

/-- Score weight of the post-update register. -/
def weightAfter (b : B) (j : Fin p.K) : ℝ :=
  (1 + 1 / (D p : ℝ)) ^ (postRegisters rate rewards C_star C_h u t b j).1

/-- Service of the literal accepted record, zero when that record is disabled. -/
def integerService (b : B) (j : Fin p.K) : ℕ :=
  RecordedQueueRun.recordService (4 * rate.n)
    ((incoming rate rewards C_star C_h u t b.2).registers j)
    (queueRecord rate rewards C_star C_h u t b j)

/-- Normalized score increment associated with that same service. -/
def normalizedService (b : B) (j : Fin p.K) : ℝ :=
  (integerService rate rewards C_star C_h u t b j : ℝ) / (rate.n : ℝ)

theorem weightBefore_eq_scoreWeight (b : B) (j : Fin p.K) :
    weightBefore rate rewards C_star C_h u t b j =
      RecordedQueueRun.scoreWeight qp (incoming rate rewards C_star C_h u t b.2) j := rfl

/-- Scores increase by exactly the service of the literal record. -/
theorem post_score_eq_add_service (b : B) (j : Fin p.K) :
    (postRegisters rate rewards C_star C_h u t b j).1 =
      ((incoming rate rewards C_star C_h u t b.2).registers j).1 +
        integerService rate rewards C_star C_h u t b j :=
  RecordedQueueRun.transition_score_eq_add_recordService _ _ _

/-- Enabled zero arrivals remain enabled records. -/
theorem queueRecord_of_noOverflow (b : B) (j : Fin p.K)
    (hf : (incoming rate rewards C_star C_h u t b.2).overflow = false) :
    queueRecord rate rewards C_star C_h u t b j =
      (true, integerArrival rate rewards C_star C_h u t b j) := by
  simp [queueRecord, hf]

/-- The source's capped integer service before overflow. -/
theorem integerService_of_noOverflow (b : B) (j : Fin p.K)
    (hf : (incoming rate rewards C_star C_h u t b.2).overflow = false) :
    integerService rate rewards C_star C_h u t b j =
      min (4 * rate.n) (((incoming rate rewards C_star C_h u t b.2).registers j).2 +
        integerArrival rate rewards C_star C_h u t b j) := by
  rw [integerService, queueRecord_of_noOverflow rate rewards C_star C_h u t b j hf]
  rfl

/-- The exact integer score increment, including the first overflowing update. -/
theorem score_increment_of_noOverflow (b : B) (j : Fin p.K)
    (hf : (incoming rate rewards C_star C_h u t b.2).overflow = false) :
    (postRegisters rate rewards C_star C_h u t b j).1 -
        ((incoming rate rewards C_star C_h u t b.2).registers j).1 =
      min (4 * rate.n) (((incoming rate rewards C_star C_h u t b.2).registers j).2 +
        integerArrival rate rewards C_star C_h u t b j) := by
  rw [post_score_eq_add_service,
    integerService_of_noOverflow rate rewards C_star C_h u t b j hf]
  omega

/-- Literal normalized queue recursion. The hypothesis reads only the
incoming flag, so the update which first overflows is included. -/
theorem backlogAfter_of_noOverflow (b : B) (j : Fin p.K)
    (hf : (incoming rate rewards C_star C_h u t b.2).overflow = false) :
    backlogAfter rate rewards C_star C_h u t b j =
      max (backlogBefore rate rewards C_star C_h u t b j +
        acceptedA rate rewards C_star C_h u t j b - 4) 0 := by
  have hn : (rate.n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos)
  have hb : (postRegisters rate rewards C_star C_h u t b j).2 =
      ((incoming rate rewards C_star C_h u t b.2).registers j).2 +
        integerArrival rate rewards C_star C_h u t b j - 4 * rate.n := by
    rw [postRegisters, queueRecord_of_noOverflow rate rewards C_star C_h u t b j hf]
    simp only [QueueReplay.transition, ite_true]
    omega
  rw [backlogAfter, hb, CanonicalQueueProcess.nat_sub_cast_eq_max,
    ← max_div_div_right (Nat.cast_nonneg rate.n)]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, zero_div]
  rw [← integerArrival_div_n rate rewards C_star C_h u t b j]
  apply congrArg (fun x : ℝ => max x 0)
  unfold backlogBefore
  rw [sub_div, add_div, mul_div_cancel_right₀ _ hn]

/-- Service always lies in the source interval, including disabled records. -/
theorem normalizedService_bounds (b : B) (j : Fin p.K) :
    0 ≤ normalizedService rate rewards C_star C_h u t b j ∧
      normalizedService rate rewards C_star C_h u t b j ≤ 4 := by
  have hn : 0 < (rate.n : ℝ) := Nat.cast_pos.mpr
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos
  have hservice : integerService rate rewards C_star C_h u t b j ≤ 4 * rate.n :=
    RecordedQueueRun.recordService_le_capacity qp _ _
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hn.le
  · apply (div_le_iff₀ hn).mpr
    exact_mod_cast hservice

/-- Incoming overflow accepts exactly the disabled zero record. -/
theorem queueRecord_of_overflow (b : B) (j : Fin p.K)
    (hf : (incoming rate rewards C_star C_h u t b.2).overflow = true) :
    queueRecord rate rewards C_star C_h u t b j = (false, 0) := by
  simp [queueRecord, integerArrival, hf]

/-- Both integer registers are preserved after incoming overflow. -/
theorem postRegisters_of_overflow (b : B) (j : Fin p.K)
    (hf : (incoming rate rewards C_star C_h u t b.2).overflow = true) :
    postRegisters rate rewards C_star C_h u t b j =
      (incoming rate rewards C_star C_h u t b.2).registers j := by
  rw [postRegisters, queueRecord_of_overflow rate rewards C_star C_h u t b j hf]
  rfl

/-- Normalized backlog is preserved on the disabled stopped branch. -/
theorem backlogAfter_of_overflow (b : B) (j : Fin p.K)
    (hf : (incoming rate rewards C_star C_h u t b.2).overflow = true) :
    backlogAfter rate rewards C_star C_h u t b j =
      backlogBefore rate rewards C_star C_h u t b j := by
  rw [backlogAfter, postRegisters_of_overflow rate rewards C_star C_h u t b j hf]
  rfl

/-- The same score weights are preserved after overflow. -/
theorem weightAfter_of_overflow (b : B) (j : Fin p.K)
    (hf : (incoming rate rewards C_star C_h u t b.2).overflow = true) :
    weightAfter rate rewards C_star C_h u t b j =
      weightBefore rate rewards C_star C_h u t b j := by
  rw [weightAfter, postRegisters_of_overflow rate rewards C_star C_h u t b j hf]
  rfl

theorem integerService_of_overflow (b : B) (j : Fin p.K)
    (hf : (incoming rate rewards C_star C_h u t b.2).overflow = true) :
    integerService rate rewards C_star C_h u t b j = 0 := by
  rw [integerService, queueRecord_of_overflow rate rewards C_star C_h u t b j hf]
  rfl

theorem normalizedService_of_overflow (b : B) (j : Fin p.K)
    (hf : (incoming rate rewards C_star C_h u t b.2).overflow = true) :
    normalizedService rate rewards C_star C_h u t b j = 0 := by
  rw [normalizedService, integerService_of_overflow rate rewards C_star C_h u t b j hf]
  simp

/-- Record lists grow even when overflow disables register updates. -/
theorem postReadout_records (b : B) (j : Fin p.K) :
    (postReadout rate rewards C_star C_h u t b).2.2 j =
      (incoming rate rewards C_star C_h u t b.2).records j ++
        [queueRecord rate rewards C_star C_h u t b j] := rfl

theorem postReadout_records_of_overflow (b : B) (j : Fin p.K)
    (hf : (incoming rate rewards C_star C_h u t b.2).overflow = true) :
    (postReadout rate rewards C_star C_h u t b).2.2 j =
      (incoming rate rewards C_star C_h u t b.2).records j ++ [(false, 0)] := by
  rw [postReadout_records, queueRecord_of_overflow rate rewards C_star C_h u t b j hf]

theorem postReadout_overflow_of_overflow (b : B)
    (hf : (incoming rate rewards C_star C_h u t b.2).overflow = true) :
    (postReadout rate rewards C_star C_h u t b).2.1 = true := by
  simp [postReadout, hf]

/-- One simultaneous almost-everywhere characterization on the original
finite unnormalized pair law. The same actual call and coordinator recording
retain every identification from the accepted-complement producer, and also
identify every literal record and the entire post observation with their
actual witnessed queue step. No witness is selected to define the readout. -/
theorem ae_actual_postReadout_identity :
    ∀ᵐ b : B ∂mu,
      ∃ d : ActualCall rate rewards C_star C_h u t b,
        ∃ recording : CoordinatorRecordingOperation.Output p,
          d.record = ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
            rate rewards C_star C_h u t b.2 ∧
          d.record.output.coordinator.recording = some recording ∧
          ReferenceFirstCollectionRenewalComplementMoments.v
              rate rewards C_star C_h u t b =
            AssignmentScoreReconstruction.currentWeight d.out ∧
          (∀ j : Fin p.K, recording.gateArm = some j ↔
            b ∈ ReferenceFirstCollectionRenewalGateCoefficient.gateEvent
              rate rewards C_star C_h u t j) ∧
          (∀ j : Fin p.K, recording.gateArm = some j →
            PublicDiscreteDraws.slotDraw (d.record.input.row.2 d.record.input.time).1 =
                PublicDiscreteDraws.dataSlot ∧
            PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
                (d.record.input.row.2 d.record.input.time).1 =
              ActiveRoundActions.coordinator p.two_le_m ∧
            d.record.output.preparation.feedback.feedback
                (ActiveRoundActions.coordinator p.two_le_m) = rewards t j ∧
            d.record.output.preparation.coordinatorObservation = rewards t j ∧
            (d.record.output.preparation.feedback.observations
                (ActiveRoundActions.coordinator p.two_le_m)).val.val =
              RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j)) ∧
          ((ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
              rate rewards C_star C_h u t b.2).overflow = false ↔
            ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength
                rate rewards C_star C_h u t b.2 <
              UnstoppedRecordedQueueComparison.firstOverflowPrefix
                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
                  rate rewards C_star C_h u t b.2)) ∧
          (∀ j : Fin p.K,
            acceptedA rate rewards C_star C_h u t j b =
              if (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
                  rate rewards C_star C_h u t b.2).overflow then 0
              else if recording.gateArm = some j then
                (recording.rawArrival : ℝ) / (rate.eta.val * (D p : ℝ))
              else 0) ∧
          (∀ j : Fin p.K, b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
              rate rewards C_star C_h u t control0 →
            (AssignmentScoreReconstruction.sourceScore d.out j,
              AssignmentScoreReconstruction.initialQueue d.out j) =
                (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
                  rate rewards C_star C_h u t b.2).registers j) ∧
          (∀ j : Fin p.K,
            acceptedA rate rewards C_star C_h u t j b =
              ((RecordedQueueRun.acceptedRecord
                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
                  rate rewards C_star C_h u t b.2)
                (actualNumericalCell rate rewards C_star C_h u t b d recording) j).2 : ℝ) /
                (rate.eta.val * (D p : ℝ))) ∧
          (∀ j : Fin p.K,
            queueRecord rate rewards C_star C_h u t b j =
              RecordedQueueRun.acceptedRecord
                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                (incoming rate rewards C_star C_h u t b.2)
                (actualNumericalCell rate rewards C_star C_h u t b d recording) j) ∧
          postReadout rate rewards C_star C_h u t b =
            stateReadout (RecordedQueueRun.step
              (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (incoming rate rewards C_star C_h u t b.2)
              (actualNumericalCell rate rewards C_star C_h u t b d recording)) := by
  filter_upwards [ae_actual_recorder_acceptedRecord_identity
    rate rewards C_star C_h u t control0] with b hb
  rcases hb with ⟨d, recording, hrecord, hrecording, hweight, hgate, hfeedback,
    hstrict, harrival, hscore, haccepted⟩
  have hn : 0 < (rate.n : ℝ) := Nat.cast_pos.mpr
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos
  have hrec : ∀ j : Fin p.K,
      queueRecord rate rewards C_star C_h u t b j =
        RecordedQueueRun.acceptedRecord qp (incoming rate rewards C_star C_h u t b.2)
          (actualNumericalCell rate rewards C_star C_h u t b d recording) j := by
    intro j
    apply Prod.ext
    · change (!(incoming rate rewards C_star C_h u t b.2).overflow) = _
      cases hf : (incoming rate rewards C_star C_h u t b.2).overflow <;>
        simp [RecordedQueueRun.acceptedRecord, actualNumericalCell, hf]
    · change integerArrival rate rewards C_star C_h u t b j = _
      apply Nat.cast_injective (R := ℝ)
      have hdiv :
          (integerArrival rate rewards C_star C_h u t b j : ℝ) / (rate.n : ℝ) =
            ((RecordedQueueRun.acceptedRecord qp
              (incoming rate rewards C_star C_h u t b.2)
              (actualNumericalCell rate rewards C_star C_h u t b d recording) j).2 : ℝ) /
                (rate.n : ℝ) := by
        calc
          _ = acceptedA rate rewards C_star C_h u t j b :=
            integerArrival_div_n rate rewards C_star C_h u t b j
          _ = _ := by simpa only [rate.n_scale] using haccepted j
      calc
        _ = (integerArrival rate rewards C_star C_h u t b j : ℝ) /
              (rate.n : ℝ) * (rate.n : ℝ) := (div_mul_cancel₀ _ (ne_of_gt hn)).symm
        _ = _ := congrArg (fun x : ℝ => x * (rate.n : ℝ)) hdiv
        _ = _ := div_mul_cancel₀ _ (ne_of_gt hn)
  refine ⟨d, recording, hrecord, hrecording, hweight, hgate, hfeedback, hstrict,
    harrival, hscore, haccepted, hrec, ?_⟩
  have hregs : postRegisters rate rewards C_star C_h u t b = fun j =>
      QueueReplay.transition (4 * rate.n)
        ((incoming rate rewards C_star C_h u t b.2).registers j)
        (RecordedQueueRun.acceptedRecord qp (incoming rate rewards C_star C_h u t b.2)
          (actualNumericalCell rate rewards C_star C_h u t b d recording) j) := by
    funext j
    exact congrArg (QueueReplay.transition (4 * rate.n)
      ((incoming rate rewards C_star C_h u t b.2).registers j)) (hrec j)
  unfold postReadout stateReadout RecordedQueueRun.step
  apply Prod.ext hregs
  apply Prod.ext
  · exact congrArg (fun registers : Fin p.K → ℕ × ℕ =>
      (incoming rate rewards C_star C_h u t b.2).overflow ||
        decide (∃ j, 32 * (registers j).2 > D p)) hregs
  · funext j
    exact congrArg (fun record : Bool × ℕ =>
      (incoming rate rewards C_star C_h u t b.2).records j ++ [record]) (hrec j)

end Bandits.Support.ReferenceFirstCollectionRenewalQueuePostReadout

end
