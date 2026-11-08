/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon
public import Bandits.Support.OrdinaryActivePhysicalStep
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# Deterministic all-active ordinary/reference suffix comparison

Sources: `sources/zip4/manuscript/06_interruptions.tex:3-5,235-297,355-361`,
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-75`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.

From one fixed common canonical boundary state, the ordinary computation below
folds the accepted ordinary physical step over the accepted reference calendar.
Each ordinary input uses its own evolving state, the same original whole row
family, actual selected index, and full denominator-D reward table. Its records
compute their outputs by the literal ordinary step; they never read reference
successors or replay reference actions. The sole all-active boundary condition
is propagated using ordinary activation preservation.

The analytical comparison stops at saved wrong-unique-acceptance diagnostics in
computed reference records. Both physical folds still process the whole chosen
interval, including the first overflow update and all later physical updates.
Missing cuts, ambiguous/rejected batches, failed logging, and local dagger paths
are retained. Equality is of the full canonical state and computed physical
projections, never raw dependent outputs or ordinary/reference diagnostics.

This is internal all-active, common-selected-row suffix mathematics. It does
not construct genuine launch or splice actual initialization, identify source
exceptional events, establish local validity or score/queue invariants, or prove
measurability, probability, expectation, or any manuscript regret assertion.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceActiveStoppedPrefixCoupling


variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- An immutable physical projection, computed from a literal round output.
It carries no decoder diagnostic or additional operational storage. -/
structure PhysicalRound (p : Parameters) where
  time : Fin p.T
  actions : Fin p.m → Fin p.K
  gridFeedback : Fin p.m → Fin (D p + 1)
  ownEntries : Fin p.m → Fin p.K × ReferencePrelaunchFollower.Observation p

/-- The physical reward is the sum of the actual own observations. -/
def PhysicalRound.totalReward (physical : PhysicalRound p) : ℝ :=
  ∑ player : Fin p.m, ReferenceActivePhysicalHorizon.observationValue (physical.ownEntries player).2

/-- Only the actual ordinary input is stored. The output is always computed
by `OrdinaryActivePhysicalStep.step`, rather than supplied as a trace. -/
structure RoundRecord where
  input : ReferenceActivePhysicalStep.RoundInput p rate

/-- The literal ordinary step on this record's own input. -/
def RoundRecord.output (record : RoundRecord (p := p) (rate := rate)) :=
  OrdinaryActivePhysicalStep.step record.input

/-- The ordinary record's computed time, simultaneous profile, full feedback,
and each player's arm/observation pair. -/
def RoundRecord.physical (record : RoundRecord (p := p) (rate := rate)) : PhysicalRound p :=
  ⟨record.input.time, record.output.preparation.arms.actions,
    record.output.preparation.feedback.feedback, record.output.ownEntries⟩

/-- The identical physical projection of an existing reference record. -/
def referencePhysical (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : PhysicalRound p :=
  ⟨record.input.time, record.actions, record.gridFeedback, record.ownEntries⟩

/-- Ordinary records link their own pre-states to their literal successors. -/
def Connected (initial : ReferenceActivePhysicalStep.State p rate) :
    List (RoundRecord (p := p) (rate := rate)) → ReferenceActivePhysicalStep.State p rate → Prop
  | [], final => final = initial
  | record :: rest, final =>
      record.input.state = initial ∧ Connected record.output.next rest final

/-- An ordinary fold accumulator uses the existing canonical state and actual
records only. Both proof fields are derived from the computation. -/
structure Run (initial : ReferenceActivePhysicalStep.State p rate) where
  finalState : ReferenceActivePhysicalStep.State p rate
  records : List (RoundRecord (p := p) (rate := rate))
  activations_preserved : finalState.activations = initial.activations
  connected : Connected initial records finalState

/-- Chronological physical projections of the computed ordinary records. -/
def Run.physicalTrace {initial : ReferenceActivePhysicalStep.State p rate} (execution : Run initial) :=
  execution.records.map RoundRecord.physical

/-- Physical cumulative reward of the independently computed ordinary suffix. -/
def Run.totalReward {initial : ReferenceActivePhysicalStep.State p rate} (execution : Run initial) : ℝ :=
  (execution.physicalTrace.map PhysicalRound.totalReward).sum

/-- Appending one literal ordinary step extends its own state chain. -/
theorem Connected.append_one {initial current : ReferenceActivePhysicalStep.State p rate}
    (records : List (RoundRecord (p := p) (rate := rate)))
    (record : RoundRecord (p := p) (rate := rate))
    (hchain : Connected initial records current) (hpre : record.input.state = current) :
    Connected initial (records ++ [record]) record.output.next := by
  induction records generalizing initial current with
  | nil =>
      change current = initial at hchain
      exact ⟨hpre.trans hchain, rfl⟩
  | cons head tail ih =>
      exact ⟨hchain.1, ih hchain.2 hpre⟩

variable (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (start : ℕ)

/-- The ordinary input reads only its own accumulator. Its activation typing
is derived from the single boundary mode and ordinary preservation. -/
def roundInputAt (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (acc : Run initial) (entry : ReferenceActivePhysicalHorizon.CalendarEntry p start) : ReferenceActivePhysicalStep.RoundInput p rate :=
  { state := acc.finalState
    rows := rows
    selected := selected
    time := ⟨entry.val, entry.property.2⟩
    active := fun i => by
      rw [acc.activations_preserved]
      exact le_trans (hmode i) (Nat.add_le_add_right entry.property.1 1)
    rewards := rewards }

/-- One genuine ordinary physical update, with no reference computation. -/
def foldRound (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (acc : Run initial) (entry : ReferenceActivePhysicalHorizon.CalendarEntry p start) : Run initial :=
  let input := roundInputAt initial rows selected rewards start hmode acc entry
  let record : RoundRecord (p := p) (rate := rate) := ⟨input⟩
  { finalState := record.output.next
    records := acc.records ++ [record]
    activations_preserved := (OrdinaryActivePhysicalStep.step_activation_preserved input).trans
      acc.activations_preserved
    connected := Connected.append_one acc.records record acc.connected rfl }

/-- The ordinary suffix genuinely folds its step over the existing finite
calendar; there is no second calendar or reference fold. -/
def run (count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) : Run initial :=
  (ReferenceActivePhysicalHorizon.calendarEntries start start count le_rfl hspan).foldl
    (foldRound initial rows selected rewards start hmode) ⟨initial, [], rfl, rfl⟩

/-- Empty intervals perform no ordinary step. This includes `start = T`. -/
theorem run_zero (hspan : start + 0 ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (run initial rows selected rewards start 0 hspan hmode).finalState = initial ∧
      (run initial rows selected rewards start 0 hspan hmode).records = [] := by
  have hnil : ReferenceActivePhysicalHorizon.calendarEntries start start 0 le_rfl hspan = [] := by
    apply List.eq_nil_of_length_eq_zero
    exact ReferenceActivePhysicalHorizon.calendarEntries_length start start 0 le_rfl hspan
  simp only [run, hnil, List.foldl_nil, and_self]

/-- The accepted calendar split exposes precisely the next ordinary physical
step. Its coordinate is `< T`, so no action occurs at sentinel `T+1`. -/
theorem run_successor_step (count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    run initial rows selected rewards start (count + 1) hspan hmode =
      foldRound initial rows selected rewards start hmode
        (run initial rows selected rewards start count (by omega) hmode)
        ⟨start + count, by omega, by omega⟩ := by
  unfold run
  rw [ReferenceActivePhysicalHorizon.calendarEntries_append start start count 1 le_rfl hspan, List.foldl_append,
    ReferenceActivePhysicalHorizon.calendarEntries_one]
  rfl

/-- The next ordinary record is computed from its own prefix state. -/
def ordinaryRecordAt (index : ℕ) (hspan : start + (index + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) : RoundRecord (p := p) (rate := rate) :=
  ⟨roundInputAt initial rows selected rewards start hmode
    (run initial rows selected rewards start index (by omega) hmode)
    ⟨start + index, by omega, by omega⟩⟩

/-- This is the actual next record of the accepted reference run, as exposed
by its successor equation. It defines no alternative reference transition. -/
def referenceRecordAt (index : ℕ) (hspan : start + (index + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
  let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start hmode
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start index (by omega) hmode)
    ⟨start + index, by omega, by omega⟩
  ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩

/-- Exact ordinary successor and append equations on computed records. -/
theorem run_successor_equations (count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (run initial rows selected rewards start (count + 1) hspan hmode).finalState =
        (ordinaryRecordAt initial rows selected rewards start count hspan hmode).output.next ∧
      (run initial rows selected rewards start (count + 1) hspan hmode).records =
        (run initial rows selected rewards start count (by omega) hmode).records ++
          [ordinaryRecordAt initial rows selected rewards start count hspan hmode] := by
  rw [run_successor_step]
  exact ⟨rfl, rfl⟩

/-- Exact reference equations, consuming the accepted successor theorem. -/
theorem reference_successor_equations (count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (count + 1) hspan hmode).finalState =
        (referenceRecordAt initial rows selected rewards start count hspan hmode).output.next ∧
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (count + 1) hspan hmode).records =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count (by omega) hmode).records ++
          [referenceRecordAt initial rows selected rewards start count hspan hmode] := by
  rw [ReferenceActivePhysicalHorizon.run_successor_step]
  exact ⟨rfl, rfl⟩

/-- Both folds retain the original activation fields, not fresh roundwise
all-active hypotheses. The reference fact is consumed from the accepted API. -/
theorem run_activations_preserved (count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (run initial rows selected rewards start count hspan hmode).finalState.activations =
        initial.activations ∧
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState.activations =
        initial.activations :=
  ⟨(run initial rows selected rewards start count hspan hmode).activations_preserved,
    ReferenceActivePhysicalHorizon.run_activations_preserved initial rows selected rewards start count hspan hmode⟩

/-- The derived boundary mode for each later ordinary and reference state. -/
theorem run_allActiveAtEnd (count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    ReferenceActivePhysicalHorizon.allActiveAtStart (run initial rows selected rewards start count hspan hmode).finalState
        (start + count) ∧
      ReferenceActivePhysicalHorizon.allActiveAtStart
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState
        (start + count) := by
  have h := run_activations_preserved initial rows selected rewards start count hspan hmode
  constructor
  · intro i
    rw [h.1]
    exact le_trans (hmode i) (Nat.add_le_add_right (Nat.le_add_right start count) 1)
  · intro i
    rw [h.2]
    exact le_trans (hmode i) (Nat.add_le_add_right (Nat.le_add_right start count) 1)

/-- Every actual ordinary record retains the original whole rows, selected
index, and full reward table. Nothing is sampled or reselected in the fold. -/
theorem run_record_inputs (count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (∀ record ∈ (run initial rows selected rewards start count hspan hmode).records,
      record.input.rows = rows ∧ record.input.selected = selected ∧ record.input.rewards = rewards) ∧
    (∀ record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records,
      record.input.rows = rows ∧ record.input.selected = selected ∧ record.input.rewards = rewards) := by
  constructor
  · unfold run
    apply List.foldlRecOn
      (motive := fun acc : Run initial => ∀ record ∈ acc.records,
        record.input.rows = rows ∧ record.input.selected = selected ∧ record.input.rewards = rewards)
    · intro record hrecord
      exact False.elim (List.not_mem_nil hrecord)
    · intro acc hacc entry _ record hrecord
      change record ∈ acc.records ++ [_] at hrecord
      rcases List.mem_append.mp hrecord with hold | hnew
      · exact hacc record hold
      · have heq := List.mem_singleton.mp hnew
        subst record
        exact ⟨rfl, rfl, rfl⟩
  · exact ReferenceActivePhysicalHorizon.run_record_inputs initial rows selected rewards start count hspan hmode

/-- Exactly one record is produced per ordinary calendar entry. -/
theorem run_record_count (count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (run initial rows selected rewards start count hspan hmode).records.length = count := by
  revert hspan
  induction count with
  | zero =>
      intro hspan
      rw [(run_zero initial rows selected rewards start hspan hmode).2]
      rfl
  | succ count ih =>
      intro hspan
      rw [(run_successor_equations initial rows selected rewards start count hspan hmode).2,
        List.length_append, ih]
      rfl

/-- The ordinary timestamps are exactly the existing chronological calendar. -/
theorem run_time_values (count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    ((run initial rows selected rewards start count hspan hmode).records.map
      (fun record => record.input.time.val)) = ReferenceActivePhysicalHorizon.calendar start count := by
  unfold run
  have hfold : ∀ (entries : List (ReferenceActivePhysicalHorizon.CalendarEntry p start)) (acc : Run initial),
      ((entries.foldl (foldRound initial rows selected rewards start hmode) acc).records.map
        (fun record => record.input.time.val)) =
      acc.records.map (fun record => record.input.time.val) ++ entries.map Subtype.val := by
    intro entries
    induction entries with
    | nil => intro acc; exact (List.append_nil _).symm
    | cons entry rest ih =>
        intro acc
        rw [List.foldl_cons, ih]
        change (acc.records ++ [_]).map (fun record : RoundRecord (p := p) (rate := rate) => record.input.time.val) ++ _ = _
        simp only [List.map_append, List.map_cons, List.append_assoc]
        rfl
  rw [hfold]
  exact ReferenceActivePhysicalHorizon.calendarEntries_time_values start start count le_rfl hspan

/-- All actual record inputs agree once their independently computed
pre-states agree. Every other field is derived from the two computations. -/
theorem next_inputs_eq_of_finalState_eq (index : ℕ) (hspan : start + (index + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hstate : (run initial rows selected rewards start index (by omega) hmode).finalState =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start index (by omega) hmode).finalState) :
    (ordinaryRecordAt initial rows selected rewards start index hspan hmode).input =
      (referenceRecordAt initial rows selected rewards start index hspan hmode).input := by
  have input_ext (left right : ReferenceActivePhysicalStep.RoundInput p rate)
      (hs : left.state = right.state) (hr : left.rows = right.rows)
      (hj : left.selected = right.selected) (ht : left.time = right.time)
      (hw : left.rewards = right.rewards) : left = right := by
    rcases left with ⟨state, table, j, time, active, reward⟩
    rcases right with ⟨otherState, otherTable, otherJ, otherTime, otherActive, otherReward⟩
    dsimp only at hs hr hj ht hw
    cases hs
    cases hr
    cases hj
    cases ht
    cases hw
    rfl
  have hmem : referenceRecordAt initial rows selected rewards start index hspan hmode ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
        (index + 1) hspan hmode).records := by
    rw [(reference_successor_equations initial rows selected rewards start index hspan hmode).2]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hfields := (run_record_inputs initial rows selected rewards start (index + 1) hspan hmode).2
    (referenceRecordAt initial rows selected rewards start index hspan hmode) hmem
  exact input_ext _ _ hstate hfields.1.symm hfields.2.1.symm rfl hfields.2.2.symm

/-- Immediate physical projections agree on the same actual input without any
restriction on the current round's reception diagnostics. -/
theorem physical_eq_reference (input : ReferenceActivePhysicalStep.RoundInput p rate) :
    (RoundRecord.mk input).physical =
      referencePhysical ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ := rfl

/-- Literal exclusions on the saved diagnostics of one existing reference
record. Absent cuts impose no additional condition. -/
def no_wrong_unique_accepted (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Prop :=
  (∀ d, record.output.coordinator.up = some d → d.wrongUniqueAccepted = false) ∧
    (∀ i cut, (record.output.followers i).down = some cut →
      ¬ ReferenceDownReception.wrongUniqueAccepted cut)

/-- Literal existence of an actually saved wrong unique acceptance. -/
def saved_wrong_unique_accepted (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Prop :=
  (∃ d, record.output.coordinator.up = some d ∧ d.wrongUniqueAccepted = true) ∨
    (∃ i cut, (record.output.followers i).down = some cut ∧
      ReferenceDownReception.wrongUniqueAccepted cut)

theorem no_wrong_unique_accepted_iff (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    no_wrong_unique_accepted record ↔ ¬ saved_wrong_unique_accepted record := by
  constructor
  · intro hgood hbad
    rcases hbad with ⟨d, hd, hwrong⟩ | ⟨i, cut, hcut, hwrong⟩
    · rw [hgood.1 d hd] at hwrong
      exact Bool.false_ne_true hwrong
    · exact hgood.2 i cut hcut hwrong
  · intro hbad
    constructor
    · intro d hd
      cases heq : d.wrongUniqueAccepted with
      | false => rfl
      | true => exact False.elim (hbad (Or.inl ⟨d, hd, heq⟩))
    · intro i cut hcut hwrong
      exact hbad (Or.inr ⟨i, cut, hcut, hwrong⟩)

/-- Full canonical state and chronological physical equality on every computed
prefix whose actual reference records pass the two literal exclusions. No
local validity, no-dagger, or supplied one-step coupling law is assumed. -/
theorem run_eq_reference (count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hgood : ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records,
      no_wrong_unique_accepted record) :
    (run initial rows selected rewards start count hspan hmode).finalState =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState ∧
      (run initial rows selected rewards start count hspan hmode).physicalTrace =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
          referencePhysical := by
  revert hspan
  induction count with
  | zero =>
      intro hspan _
      constructor
      · rw [(run_zero initial rows selected rewards start hspan hmode).1, ReferenceActivePhysicalHorizon.run_zero_final]
      · simp only [Run.physicalTrace,
          (run_zero initial rows selected rewards start hspan hmode).2,
          ReferenceActivePhysicalHorizon.run_zero_records, List.map_nil]
  | succ count ih =>
      intro hspan hgood
      have hrecords := (reference_successor_equations initial rows selected rewards start
        count hspan hmode).2
      have hprevious : ∀ record ∈
          (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count (by omega) hmode).records,
          no_wrong_unique_accepted record := by
        intro record hrecord
        apply hgood record
        rw [hrecords]
        exact List.mem_append_left _ hrecord
      have hcurrent : no_wrong_unique_accepted
          (referenceRecordAt initial rows selected rewards start count hspan hmode) := by
        apply hgood
        rw [hrecords]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hprefix := ih (by omega) hprevious
      have hinput := next_inputs_eq_of_finalState_eq initial rows selected rewards start
        count hspan hmode hprefix.1
      have hstep := OrdinaryActivePhysicalStep.step_eq_reference_of_saved_diagnostics_not_wrongUniqueAccepted
        (referenceRecordAt initial rows selected rewards start count hspan hmode).input
        hcurrent.1 hcurrent.2
      constructor
      · rw [(run_successor_equations initial rows selected rewards start count hspan hmode).1,
          (reference_successor_equations initial rows selected rewards start count hspan hmode).1]
        change (OrdinaryActivePhysicalStep.step _).next = (ReferenceActivePhysicalStep.step _).next
        rw [hinput]
        exact hstep
      · unfold Run.physicalTrace
        rw [(run_successor_equations initial rows selected rewards start count hspan hmode).2,
          hrecords, List.map_append, List.map_append, List.map_singleton, List.map_singleton]
        apply congrArg₂ (fun a b : List (PhysicalRound p) => a ++ b) hprefix.2
        apply congrArg (fun physical : PhysicalRound p => [physical])
        exact (congrArg (fun input : ReferenceActivePhysicalStep.RoundInput p rate =>
          (RoundRecord.mk input).physical) hinput).trans (physical_eq_reference _)

/-- The observation-based cumulative rewards agree whenever the computed
physical traces agree; diagnostic fields play no role. -/
theorem totalReward_eq_of_physicalTrace_eq (ordinaryRun : Run initial)
    (referenceRun : ReferenceActivePhysicalHorizon.Run initial)
    (htrace : ordinaryRun.physicalTrace = referenceRun.records.map referencePhysical) :
    ordinaryRun.totalReward = referenceRun.totalReward := by
  unfold Run.totalReward
  rw [htrace, List.map_map]
  rfl

/-- Reward equality for every good computed prefix, including the empty one. -/
theorem run_totalReward_eq_reference (count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hgood : ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records,
      no_wrong_unique_accepted record) :
    (run initial rows selected rewards start count hspan hmode).totalReward =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).totalReward :=
  totalReward_eq_of_physicalTrace_eq initial _ _
    (run_eq_reference initial rows selected rewards start count hspan hmode hgood).2


/-- The computed ordinary records have the exact chronological prefix given
by the shorter ordinary fold. The full fold is never stopped. -/
theorem run_prefix_records (count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hk : k ≤ count) :
    (run initial rows selected rewards start count hspan hmode).records.take k =
      (run initial rows selected rewards start k (by omega) hmode).records := by
  revert hspan hk
  induction count with
  | zero =>
      intro hspan hk
      have hkzero : k = 0 := by omega
      subst k
      rw [List.take_zero, (run_zero initial rows selected rewards start hspan hmode).2]
  | succ count ih =>
      intro hspan hk
      by_cases heq : k = count + 1
      · subst k
        apply List.take_of_length_le
        rw [run_record_count]
      · have hkle : k ≤ count := by omega
        rw [(run_successor_equations initial rows selected rewards start count hspan hmode).2,
          List.take_append_of_le_length (by rw [run_record_count]; exact hkle)]
        exact ih (by omega) hkle

/-- Exact record prefixes of the accepted reference computation, proved using
its accepted successor and record-count APIs rather than another reference fold. -/
theorem reference_run_prefix_records (count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hk : k ≤ count) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.take k =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start k (by omega) hmode).records := by
  revert hspan hk
  induction count with
  | zero =>
      intro hspan hk
      have hkzero : k = 0 := by omega
      subst k
      rw [List.take_zero, ReferenceActivePhysicalHorizon.run_zero_records]
  | succ count ih =>
      intro hspan hk
      by_cases heq : k = count + 1
      · subst k
        apply List.take_of_length_le
        rw [ReferenceActivePhysicalHorizon.run_record_count]
      · have hkle : k ≤ count := by omega
        rw [(reference_successor_equations initial rows selected rewards start count hspan hmode).2,
          List.take_append_of_le_length
            (by rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hkle)]
        exact ih (by omega) hkle

/-- The computed physical trace of a shorter ordinary interval is literally
the corresponding prefix of the full ordinary interval. -/
theorem run_prefix_physicalTrace (count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hk : k ≤ count) :
    (run initial rows selected rewards start count hspan hmode).physicalTrace.take k =
      (run initial rows selected rewards start k (by omega) hmode).physicalTrace := by
  unfold Run.physicalTrace
  rw [← List.map_take, run_prefix_records initial rows selected rewards start count hspan hmode k hk]

/-- A candidate reference record is an actual record of every longer computed
interval containing its physical coordinate. -/
theorem referenceRecordAt_mem (count index : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (hindex : index < count) :
    referenceRecordAt initial rows selected rewards start index (by omega) hmode ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records := by
  apply List.mem_of_mem_take (i := index + 1)
  rw [reference_run_prefix_records initial rows selected rewards start count hspan hmode
    (index + 1) (by omega)]
  rw [(reference_successor_equations initial rows selected rewards start index (by omega) hmode).2]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- For every `k ≤ count`, exclusions on exactly the first `k` computed
reference records give full canonical boundary-state equality, equality of the
chronological physical prefixes of both full folds, and cumulative reward
equality for those prefixes. The full physical runs still have length `count`. -/
theorem stopped_prefix_eq (count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hk : k ≤ count)
    (hgood : ∀ record ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.take k,
      no_wrong_unique_accepted record) :
    (run initial rows selected rewards start k (by omega) hmode).finalState =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start k (by omega) hmode).finalState ∧
      (run initial rows selected rewards start count hspan hmode).physicalTrace.take k =
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
          referencePhysical).take k ∧
      (run initial rows selected rewards start k (by omega) hmode).totalReward =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start k (by omega) hmode).totalReward := by
  have hgoodPrefix : ∀ record ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start k (by omega) hmode).records,
      no_wrong_unique_accepted record := by
    intro record hrecord
    apply hgood record
    rw [reference_run_prefix_records initial rows selected rewards start count hspan hmode k hk]
    exact hrecord
  have hprefix := run_eq_reference initial rows selected rewards start k (by omega) hmode hgoodPrefix
  refine ⟨hprefix.1, ?_, run_totalReward_eq_reference initial rows selected rewards start
    k (by omega) hmode hgoodPrefix⟩
  rw [run_prefix_physicalTrace initial rows selected rewards start count hspan hmode k hk,
    ← List.map_take,
    reference_run_prefix_records initial rows selected rewards start count hspan hmode k hk]
  exact hprefix.2

/-- The action profiles, full grid feedback vectors, and own arm/observation
entries agree chronologically on every excluded-diagnostic prefix. -/
theorem stopped_prefix_projections_eq (count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hk : k ≤ count)
    (hgood : ∀ record ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.take k,
      no_wrong_unique_accepted record) :
    ((run initial rows selected rewards start count hspan hmode).physicalTrace.take k).map
        PhysicalRound.actions =
      (((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
        referencePhysical).take k).map PhysicalRound.actions ∧
    ((run initial rows selected rewards start count hspan hmode).physicalTrace.take k).map
        PhysicalRound.gridFeedback =
      (((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
        referencePhysical).take k).map PhysicalRound.gridFeedback ∧
    ((run initial rows selected rewards start count hspan hmode).physicalTrace.take k).map
        PhysicalRound.ownEntries =
      (((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
        referencePhysical).take k).map PhysicalRound.ownEntries := by
  have htrace := (stopped_prefix_eq initial rows selected rewards start count hspan hmode k hk hgood).2.1
  exact ⟨congrArg (List.map PhysicalRound.actions) htrace,
    congrArg (List.map PhysicalRound.gridFeedback) htrace,
    congrArg (List.map PhysicalRound.ownEntries) htrace⟩

/-- Immediate play and observations in the next round agree even if that
round saves a wrong acceptance. Only earlier records need the exclusions;
no equality of the next successor or diagnostic fields is asserted here. -/
theorem successor_physicalTrace_eq_of_good_predecessor (index : ℕ)
    (hspan : start + (index + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hearlier : ∀ record ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start index (by omega) hmode).records,
      no_wrong_unique_accepted record) :
    (run initial rows selected rewards start (index + 1) hspan hmode).physicalTrace =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (index + 1) hspan hmode).records.map
        referencePhysical := by
  have hprefix := run_eq_reference initial rows selected rewards start index (by omega) hmode hearlier
  have hinput := next_inputs_eq_of_finalState_eq initial rows selected rewards start index hspan hmode hprefix.1
  unfold Run.physicalTrace
  rw [(run_successor_equations initial rows selected rewards start index hspan hmode).2,
    (reference_successor_equations initial rows selected rewards start index hspan hmode).2,
    List.map_append, List.map_append, List.map_singleton, List.map_singleton]
  apply congrArg₂ (fun a b : List (PhysicalRound p) => a ++ b) hprefix.2
  apply congrArg (fun physical : PhysicalRound p => [physical])
  exact (congrArg (fun input : ReferenceActivePhysicalStep.RoundInput p rate =>
    (RoundRecord.mk input).physical) hinput).trans (physical_eq_reference _)

/-- A universally quantified first-bad candidate: exactly its earlier actual
reference records pass the exclusions, and its computed saved cut is bad.
The bad record belongs to the full run at time `start + index`. All preceding
boundary states agree, and physical prefixes and cumulative reward agree
through that record. No claim compares successors after its bad acceptance. -/
theorem first_bad_boundary (count index : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (hindex : index < count)
    (hearlier : ∀ record ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.take index,
      no_wrong_unique_accepted record)
    (hbad : saved_wrong_unique_accepted
      (referenceRecordAt initial rows selected rewards start index (by omega) hmode)) :
    (∃ record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records,
      record.input.time.val = start + index ∧ saved_wrong_unique_accepted record) ∧
    (∀ (k : ℕ) (_hk : k ≤ index),
      (run initial rows selected rewards start k (by omega) hmode).finalState =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start k (by omega) hmode).finalState) ∧
    (∀ k, k ≤ index + 1 →
      (run initial rows selected rewards start count hspan hmode).physicalTrace.take k =
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
          referencePhysical).take k) ∧
    (run initial rows selected rewards start (index + 1) (by omega) hmode).totalReward =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (index + 1) (by omega) hmode).totalReward := by
  have hgoodIndex : ∀ record ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start index (by omega) hmode).records,
      no_wrong_unique_accepted record := by
    intro record hrecord
    apply hearlier record
    rw [reference_run_prefix_records initial rows selected rewards start count hspan hmode index (by omega)]
    exact hrecord
  have hthrough := successor_physicalTrace_eq_of_good_predecessor initial rows selected rewards start
    index (by omega) hmode hgoodIndex
  have hfullThrough :
      (run initial rows selected rewards start count hspan hmode).physicalTrace.take (index + 1) =
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
          referencePhysical).take (index + 1) := by
    rw [run_prefix_physicalTrace initial rows selected rewards start count hspan hmode (index + 1) (by omega),
      ← List.map_take,
      reference_run_prefix_records initial rows selected rewards start count hspan hmode (index + 1) (by omega)]
    exact hthrough
  refine ⟨⟨referenceRecordAt initial rows selected rewards start index (by omega) hmode,
    referenceRecordAt_mem initial rows selected rewards start count index hspan hmode hindex, rfl, hbad⟩,
    ?_, ?_, totalReward_eq_of_physicalTrace_eq initial _ _ hthrough⟩
  · intro k hk
    apply (run_eq_reference initial rows selected rewards start k (by omega) hmode ?_).1
    intro record hrecord
    apply hgoodIndex record
    apply List.mem_of_mem_take (i := k)
    rw [reference_run_prefix_records initial rows selected rewards start index (by omega) hmode k hk]
    exact hrecord
  · intro k hk
    have h := congrArg (List.take k) hfullThrough
    simpa only [List.take_take, Nat.min_eq_left hk] using h

/-- If there is no saved bad acceptance anywhere in the computed interval,
the entire canonical final state, chronological physical trace, and reward
agree. This says nothing about source exceptional-event identities. -/
theorem run_eq_reference_of_no_saved_wrong_unique_accepted (count : ℕ)
    (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hnone : ∀ record ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records,
      ¬ saved_wrong_unique_accepted record) :
    (run initial rows selected rewards start count hspan hmode).finalState =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState ∧
      (run initial rows selected rewards start count hspan hmode).physicalTrace =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
          referencePhysical ∧
      (run initial rows selected rewards start count hspan hmode).totalReward =
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).totalReward := by
  have hgood : ∀ record ∈
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records,
      no_wrong_unique_accepted record := by
    intro record hrecord
    exact (no_wrong_unique_accepted_iff record).mpr (hnone record hrecord)
  have h := run_eq_reference initial rows selected rewards start count hspan hmode hgood
  exact ⟨h.1, h.2, run_totalReward_eq_reference initial rows selected rewards start count hspan hmode hgood⟩

/-- The terminal empty ordinary interval preserves the whole boundary state
and has no records, no actions, and zero reward. The mode follows from the
typed activation range rather than a new launch assumption. -/
theorem run_terminal :
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial p.T :=
      fun i => (initial.activations i).property.2
    (run initial rows selected rewards p.T 0 (by omega) hmode).finalState = initial ∧
      (run initial rows selected rewards p.T 0 (by omega) hmode).records = [] ∧
      (run initial rows selected rewards p.T 0 (by omega) hmode).totalReward = 0 := by
  dsimp only
  have hzero := run_zero initial rows selected rewards p.T (by omega)
    (fun i => (initial.activations i).property.2)
  refine ⟨hzero.1, hzero.2, ?_⟩
  simp only [Run.totalReward, Run.physicalTrace, hzero.2, List.map_nil, List.sum_nil]

end Bandits.Support.ReferenceActiveStoppedPrefixCoupling

end
