/-
Copyright (c) 2026 Bandits formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.RecordedRoundMoments

import Mathlib.MeasureTheory.Function.Floor

/-!
# Quantized estimate replay for the recorded queue

The source estimate is the accepted integer arrival divided by its integer
denominator. This module factors the accepted queue update and finite execution
through those normalized vectors, without retaining a recording-outcome label.
-/

@[expose] public section

namespace Bandits.Support.RecordedQuantizedEstimateReplay

open MeasureTheory

variable {K T : ℕ}

/-- The normalized natural-floor coarsening used by the manuscript's estimate. -/
noncomputable def scalarCoarsening (n : ℕ) (x : ℝ) : ℝ :=
  (Nat.floor ((n : ℝ) * x) : ℝ) / (n : ℝ)

/-- Coordinatewise normalized floor coarsening of a real estimate vector. -/
noncomputable def vectorCoarsening (n : ℕ) (x : Fin K → ℝ) : Fin K → ℝ :=
  fun i => scalarCoarsening n (x i)

theorem scalarCoarsening_measurable (n : ℕ) :
    Measurable (scalarCoarsening n) := by
  unfold scalarCoarsening
  have hmul : Measurable (fun x : ℝ => (n : ℝ) * x) :=
    measurable_const.mul measurable_id
  have hcast : Measurable (fun a : ℕ => (a : ℝ)) :=
    measurable_of_countable _
  exact (hcast.comp (Nat.measurable_floor.comp hmul)).div_const (n : ℝ)

theorem vectorCoarsening_measurable (n : ℕ) :
    Measurable (vectorCoarsening (K := K) n) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (scalarCoarsening_measurable n).comp (measurable_pi_apply i)

/-- The enabled, pre-overflow unquantized reward/rate input to the floor map.
The zero branches include no recorded arm, a zero reward, a disabled round,
and every post-overflow round. -/
noncomputable def sourceUnquantizedInput (state : RecordedQueueRun.RunState K)
    (round : RecordedQueueRun.RoundInput K) (i : Fin K) : ℝ :=
  if state.overflow then 0 else if round.enabled then
    if round.recordedArm = some i then round.reward i / round.rate i else 0
  else 0

/-- The actual accepted normalized estimate vector of one round. -/
noncomputable def sourceEstimate (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K)
    (round : RecordedQueueRun.RoundInput K) : Fin K → ℝ :=
  fun i => RecordedRoundMoments.rawEstimate p state round i

theorem rawEstimate_eq_sourceCoarsening (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (round : RecordedQueueRun.RoundInput K)
    (i : Fin K) :
    RecordedRoundMoments.rawEstimate p state round i =
      scalarCoarsening p.n (sourceUnquantizedInput state round i) := by
  cases hOverflow : state.overflow <;> cases hEnabled : round.enabled <;>
    by_cases hRecorded : round.recordedArm = some i <;>
    simp [RecordedRoundMoments.rawEstimate, scalarCoarsening,
      sourceUnquantizedInput, RecordedQueueRun.acceptedRecord,
      RecordedQueueRun.acceptedArrival, RecordedQueueRun.quantizedArrival,
      hOverflow, hEnabled, hRecorded, ← mul_div_assoc]

theorem sourceVectorCoarsening_measurable (p : RecordedQueueRun.Parameters) :
    Measurable (vectorCoarsening (K := K) p.n) :=
  vectorCoarsening_measurable (K := K) p.n

/-- The source integer arrival is recovered from its normalized lattice value. -/
theorem rawEstimate_floor_recovery (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (round : RecordedQueueRun.RoundInput K)
    (i : Fin K) :
    Nat.floor ((p.n : ℝ) * RecordedRoundMoments.rawEstimate p state round i) =
      RecordedQueueRun.acceptedArrival
        (RecordedQueueRun.acceptedRecord p state round i) := by
  unfold RecordedRoundMoments.rawEstimate
  have hn : (p.n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt p.n_pos)
  rw [show (p.n : ℝ) *
        ((RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord p state round i) : ℝ) / (p.n : ℝ)) =
          (RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord p state round i) : ℝ) by
      field_simp [hn]]
  exact Nat.floor_natCast _

/-- Construct one accepted record from PRE, the enabled bit, and an exact
integer arrival code. -/
def acceptedRecordFromArrivalCode (state : RecordedQueueRun.RunState K)
    (enabled : Bool) (arrival : Fin K → ℕ) (i : Fin K) : Bool × ℕ :=
  if state.overflow then (false, 0)
  else if enabled then (true, arrival i)
  else (false, 0)

/-- Apply a complete queue update from exact integer arrival codes. -/
noncomputable def stepFromArrivalCode (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (enabled : Bool)
    (arrival : Fin K → ℕ) : RecordedQueueRun.RunState K := by
  classical
  let recs := fun i => acceptedRecordFromArrivalCode state enabled arrival i
  let registers := fun i => QueueReplay.transition (4 * p.n)
    (state.registers i) (recs i)
  let overflow := state.overflow || decide (∃ i, 32 * (registers i).2 > p.D)
  exact ⟨registers, overflow, fun i => state.records i ++ [recs i]⟩

/-- Reconstruct one accepted record from PRE, the enabled bit, and the
normalized estimate vector. Enabled zero estimates still carry an enabled
record and therefore still serve the existing backlog. -/
noncomputable def acceptedRecordFromEstimate (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (enabled : Bool)
    (estimate : Fin K → ℝ) (i : Fin K) : Bool × ℕ :=
  acceptedRecordFromArrivalCode state enabled
    (fun j => Nat.floor ((p.n : ℝ) * estimate j)) i

theorem acceptedRecordFromSourceEstimate_eq (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (round : RecordedQueueRun.RoundInput K)
    (i : Fin K) :
    acceptedRecordFromEstimate p state round.enabled (sourceEstimate p state round) i =
      RecordedQueueRun.acceptedRecord p state round i := by
  cases hOverflow : state.overflow
  · cases hEnabled : round.enabled
    · simp [acceptedRecordFromEstimate,
        acceptedRecordFromArrivalCode, RecordedQueueRun.acceptedRecord,
        hOverflow, hEnabled]
    · have hfloor : Nat.floor ((p.n : ℝ) *
          sourceEstimate p state round i) =
          RecordedQueueRun.quantizedArrival p round i := by
        simpa [sourceEstimate, RecordedQueueRun.acceptedRecord,
          RecordedQueueRun.acceptedArrival, hOverflow, hEnabled] using
            rawEstimate_floor_recovery p state round i
      simp [acceptedRecordFromEstimate, acceptedRecordFromArrivalCode,
        RecordedQueueRun.acceptedRecord, hOverflow, hEnabled, hfloor]
  · simp [acceptedRecordFromEstimate, acceptedRecordFromArrivalCode,
      RecordedQueueRun.acceptedRecord, hOverflow]

/-- Apply the complete recorded queue update using only PRE, the enabled bit,
and the normalized estimate vector. The overflow test follows the updated
registers, so the first crossing update remains in the records. -/
noncomputable def stepFromEstimate (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (enabled : Bool)
    (estimate : Fin K → ℝ) : RecordedQueueRun.RunState K :=
  stepFromArrivalCode p state enabled
    (fun i => Nat.floor ((p.n : ℝ) * estimate i))

theorem stepFromSourceEstimate_eq_step (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (round : RecordedQueueRun.RoundInput K) :
    stepFromEstimate p state round.enabled (sourceEstimate p state round) =
      RecordedQueueRun.step p state round := by
  have hrecord : ∀ i, acceptedRecordFromArrivalCode state round.enabled
      (fun j => Nat.floor ((p.n : ℝ) * sourceEstimate p state round j)) i =
        RecordedQueueRun.acceptedRecord p state round i :=
    fun i => by
      simpa [acceptedRecordFromEstimate] using
        acceptedRecordFromSourceEstimate_eq p state round i
  unfold stepFromEstimate stepFromArrivalCode RecordedQueueRun.step
  simp [hrecord]

/-- Reconstruct a chronological execution by evaluating the source estimate
at each actual accepted prefix and feeding only its normalized vector to the
next deterministic update. -/
noncomputable def executeFromSourceEstimates (p : RecordedQueueRun.Parameters) :
    List (RecordedQueueRun.RoundInput K) → RecordedQueueRun.RunState K →
      RecordedQueueRun.RunState K
  | [], state => state
  | round :: rounds, state =>
      executeFromSourceEstimates p rounds
        (stepFromEstimate p state round.enabled (sourceEstimate p state round))

theorem executeFromSourceEstimates_eq_execute (p : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput K))
    (state : RecordedQueueRun.RunState K) :
    executeFromSourceEstimates p rounds state =
      RecordedQueueRun.execute p rounds state := by
  induction rounds generalizing state with
  | nil => rfl
  | cons round rounds ih =>
      change executeFromSourceEstimates p rounds
          (stepFromEstimate p state round.enabled (sourceEstimate p state round)) =
        RecordedQueueRun.execute p rounds (RecordedQueueRun.step p state round)
      rw [stepFromSourceEstimate_eq_step]
      exact ih _

/-- The accepted integer state has a local discrete measurable structure. Its
carrier is countable: it consists of finitely many natural register pairs,
one Boolean, and finitely many finite integer histories. -/
theorem runState_countable : Countable (RecordedQueueRun.RunState K) := by
  have hinj : Function.Injective
      (fun state : RecordedQueueRun.RunState K =>
        (state.registers, state.overflow, state.records)) := by
    intro a b hab
    cases a
    cases b
    simp_all
  exact hinj.countable

/-- Local countable measurable structure used for the integer machine output.
No measurable structure is installed on the real estimate carrier. -/
@[instance_reducible] def runStateMeasurableSpace (K : ℕ) :
    MeasurableSpace (RecordedQueueRun.RunState K) := ⊤

theorem runState_observable_measurable {α : Type*} [MeasurableSpace α]
    (f : RecordedQueueRun.RunState K → α) :
    @Measurable (RecordedQueueRun.RunState K) α
      (runStateMeasurableSpace K) inferInstance f := by
  exact @measurable_of_countable
    (RecordedQueueRun.RunState K) α (runStateMeasurableSpace K) inferInstance
    (runState_countable (K := K)) inferInstance f

theorem stepFromEstimate_measurable (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (enabled : Bool) :
    @Measurable (Fin K → ℝ) (RecordedQueueRun.RunState K) inferInstance
      (runStateMeasurableSpace K)
      (stepFromEstimate p state enabled) := by
  have hcode : Measurable
      (fun estimate : Fin K → ℝ => fun i => Nat.floor ((p.n : ℝ) * estimate i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact Nat.measurable_floor.comp
      (measurable_const.mul (measurable_pi_apply i))
  have hstep : @Measurable (Fin K → ℕ) (RecordedQueueRun.RunState K)
      inferInstance (runStateMeasurableSpace K)
      (fun arrivals => stepFromArrivalCode p state enabled arrivals) := by
    exact @measurable_of_countable
      (Fin K → ℕ) (RecordedQueueRun.RunState K)
      inferInstance (runStateMeasurableSpace K) inferInstance inferInstance _
  exact hstep.comp hcode

/-- Floor codes for one finite sequence of real estimate vectors. -/
noncomputable def estimateSequenceCodes (p : RecordedQueueRun.Parameters)
    (estimates : Fin T → Fin K → ℝ) : Fin T → Fin K → ℕ :=
  fun t i => Nat.floor ((p.n : ℝ) * estimates t i)

theorem estimateSequenceCodes_measurable (p : RecordedQueueRun.Parameters)
    (T : ℕ) :
    Measurable (estimateSequenceCodes (K := K) (T := T) p) := by
  apply measurable_pi_iff.mpr
  intro t
  apply measurable_pi_iff.mpr
  intro i
  have hcoordinate : Measurable
      (fun estimates : Fin T → Fin K → ℝ => estimates t i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply t)
  exact Nat.measurable_floor.comp (measurable_const.mul hcoordinate)

/-- Replay a finite chronological list of integer estimate codes. -/
noncomputable def replayFromEstimateCodes (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) :
    List (Bool × (Fin K → ℕ)) → RecordedQueueRun.RunState K
  | [] => state
  | (enabled, arrivals) :: codes =>
      replayFromEstimateCodes p
        (stepFromArrivalCode p state enabled arrivals) codes

/-- Finite chronological replay of a fixed-length enabled schedule from real
estimate vectors, after applying the source's integer normalization. -/
noncomputable def finiteEstimateReplay (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (enabled : Fin T → Bool)
    (estimates : Fin T → Fin K → ℝ) : RecordedQueueRun.RunState K :=
  replayFromEstimateCodes p state
    (List.ofFn fun t => (enabled t, estimateSequenceCodes p estimates t))

theorem finiteEstimateReplay_measurable (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (enabled : Fin T → Bool) :
    @Measurable (Fin T → Fin K → ℝ) (RecordedQueueRun.RunState K)
      inferInstance (runStateMeasurableSpace K)
      (finiteEstimateReplay p state enabled) := by
  have hcode : Measurable (estimateSequenceCodes (K := K) (T := T) p) :=
    estimateSequenceCodes_measurable (K := K) p T
  have hreplay : @Measurable (Fin T → Fin K → ℕ) (RecordedQueueRun.RunState K)
      inferInstance (runStateMeasurableSpace K)
      (fun codes : Fin T → Fin K → ℕ =>
        replayFromEstimateCodes p state
          (List.ofFn fun t => (enabled t, codes t))) := by
    exact @measurable_of_countable
      (Fin T → Fin K → ℕ) (RecordedQueueRun.RunState K)
      inferInstance (runStateMeasurableSpace K) inferInstance inferInstance _
  exact hreplay.comp hcode

theorem finiteEstimateReplay_registers_measurable (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (enabled : Fin T → Bool)
    (i : Fin K) :
    Measurable (fun estimates =>
      (finiteEstimateReplay p state enabled estimates).registers i) := by
  have hprojection : @Measurable (RecordedQueueRun.RunState K)
      RecordedQueueRun.Registers (runStateMeasurableSpace K) inferInstance
      (fun result => result.registers i) :=
    runState_observable_measurable (K := K) (fun result => result.registers i)
  exact hprojection.comp (finiteEstimateReplay_measurable p state enabled)

theorem finiteEstimateReplay_scoreWeight_measurable (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (enabled : Fin T → Bool)
    (i : Fin K) :
    Measurable (fun estimates =>
      RecordedQueueRun.scoreWeight p (finiteEstimateReplay p state enabled estimates) i) := by
  have hprojection : @Measurable (RecordedQueueRun.RunState K) ℝ
      (runStateMeasurableSpace K) inferInstance
      (fun result => RecordedQueueRun.scoreWeight p result i) :=
    runState_observable_measurable (K := K)
      (fun result => RecordedQueueRun.scoreWeight p result i)
  exact hprojection.comp (finiteEstimateReplay_measurable p state enabled)

end Bandits.Support.RecordedQuantizedEstimateReplay
