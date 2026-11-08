/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStep
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# Canonical finite postlaunch physical horizon

The one-round transition is the integrated `ReferenceActivePhysicalStep.step`.
This module folds that transition over the physical calendar interval
`[start, start + count)`, retaining the actual typed input and literal step
output for every round. The protocol order follows
`sources/zip4/manuscript/06_interruptions.tex:9-70,235-297,355-426`, with the
complete-table and fixed selected-row scope of `sources/zip4/manuscript/08_main_theorem.tex:29-42`
and local exceptional-state semantics of
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.

The input is a fixed typed boundary state and an explicit all-active mode
condition. This fold constructs only its postlaunch suffix; it does not
construct that boundary state or prove the mode condition from launch.
Runtime failures and dagger states remain in the actual outputs while the
calendar continues through every physical round in the requested interval.
There is no analytical-overflow stopping test. Selected-row invariance fixes
the boundary state; it proves no row-only initialization, reachability,
absence of dagger, truthful scores, measurability, probability law, exact bad-event
provenance, whole-run coupling, or regret assertion.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep

namespace Bandits.Support.ReferenceActivePhysicalHorizon

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalStep.State

variable {p : Parameters} {rate : RateInput p}

/-- The standard finite-list calendar for the half-open interval
`[start, start + count)`. -/
def calendar (start count : ℕ) : List ℕ :=
  List.range' start count 1

/-- Every calendar entry is a physical coordinate; the terminal sentinel is
never included in the interval. -/
theorem calendar_bounds {start count time : ℕ}
    (hspan : start + count ≤ p.T)
    (hmem : time ∈ calendar start count) :
    start ≤ time ∧ time < p.T := by
  have hmem' : time ∈ List.range' start count 1 := by
    simpa only [calendar] using hmem
  constructor
  · exact List.left_le_of_mem_range' hmem'
  · obtain ⟨offset, hoffset, rfl⟩ := List.mem_range'.mp hmem'
    omega

/-- A typed physical calendar entry whose time is at or after the fixed
all-active mode origin. -/
abbrev CalendarEntry (p : Parameters) (origin : ℕ) :=
  {time : ℕ // origin ≤ time ∧ time < p.T}

/-- Convert the standard `List.range'` interval to entries carrying exactly
the bounds needed to construct each literal `Fin T` round input. -/
def calendarEntries (origin intervalStart count : ℕ)
    (horigin : origin ≤ intervalStart)
    (hspan : intervalStart + count ≤ p.T) : List (CalendarEntry p origin) :=
  ((calendar intervalStart count).attach).map fun entry =>
    ⟨entry.val,
      ⟨le_trans horigin (calendar_bounds hspan entry.property).1,
        (calendar_bounds hspan entry.property).2⟩⟩

/-- The explicit postlaunch mode required by each typed active-round input.
It is stated once at the fixed boundary state and propagated through the fold
using `step_next_fields` and calendar monotonicity. -/
def allActiveAtStart (initial : State p rate) (start : ℕ) : Prop :=
  ∀ i, (initial.activations i).val ≤ start + 1

/-- A round record has no supplied trace fields: its output is tied by equality
to the literal accepted `step` call on its retained input. -/
structure RoundRecord where
  input : ReferenceActivePhysicalStep.RoundInput p rate
  output : ReferenceActivePhysicalStep.RoundOutput input
  output_eq : output = ReferenceActivePhysicalStep.step input

/-- The simultaneously selected physical action profile from the actual
round's preparation. -/
def RoundRecord.actions (record : RoundRecord (p := p) (rate := rate)) :
    Fin p.m → Fin p.K := record.output.preparation.arms.actions

/-- The full grid feedback vector computed from the actual simultaneous
profile and complete denominator-`D` reward table. -/
def RoundRecord.gridFeedback (record : RoundRecord (p := p) (rate := rate)) :
    Fin p.m → Fin (D p + 1) := record.output.preparation.feedback.feedback

/-- Each player's actual arm and decoded own observation from the literal
physical step output. -/
def RoundRecord.ownEntries (record : RoundRecord (p := p) (rate := rate)) :=
  record.output.ownEntries

/-- Coordinator recording and UP-decoder diagnostics retained by the actual
step. -/
def RoundRecord.coordinatorDiagnostics
    (record : RoundRecord (p := p) (rate := rate)) := record.output.coordinator

/-- Per-follower local failures and DOWN-decoder diagnostics retained by the
actual step. -/
def RoundRecord.followerDiagnostics
    (record : RoundRecord (p := p) (rate := rate)) := record.output.followers

/-- Exact collision-filtered grid feedback for this player's computed action.
-/
theorem RoundRecord.gridFeedback_formula
    (record : RoundRecord (p := p) (rate := rate)) (player : Fin p.m) :
    record.gridFeedback player =
      if FiniteBanditModel.collisionFreeFor record.actions player then
        record.input.rewards record.input.time (record.actions player) else 0 := by
  unfold RoundRecord.gridFeedback RoundRecord.actions
  rw [record.output_eq]
  exact (ReferenceActivePhysicalStep.prepare record.input).feedback_rule player

/-- Exact own-entry equation from the accepted step, including conversion of
the actual collision feedback into this player's typed observation. -/
theorem RoundRecord.ownEntries_formula
    (record : RoundRecord (p := p) (rate := rate)) (player : Fin p.m) :
    record.ownEntries player =
      (record.actions player,
        ActualInitializationPhysicalStep.observationOfGrid p
          (if FiniteBanditModel.collisionFreeFor record.actions player then
            record.input.rewards record.input.time (record.actions player) else 0)) := by
  unfold RoundRecord.ownEntries RoundRecord.actions
  calc
    record.output.ownEntries player =
        ((ReferenceActivePhysicalStep.prepare record.input).arms.actions player,
          ActualInitializationPhysicalStep.observationOfGrid p
            ((ReferenceActivePhysicalStep.prepare record.input).feedback.feedback player)) := by
      rw [record.output_eq]
      exact ReferenceActivePhysicalStep.step_own_entry record.input player
    _ = (record.output.preparation.arms.actions player,
          ActualInitializationPhysicalStep.observationOfGrid p
            (if FiniteBanditModel.collisionFreeFor record.output.preparation.arms.actions player then
              record.input.rewards record.input.time
                (record.output.preparation.arms.actions player) else 0)) := by
      rw [record.output_eq]
      simp only [ReferenceActivePhysicalStep.PreparedRound.feedback_rule]
      rfl

/-- Numerical value carried by an actual typed own observation. -/
def observationValue (observation : ReferencePrelaunchFollower.Observation p) : ℝ :=
  observation.val.val

theorem observationValue_bounds (observation : ReferencePrelaunchFollower.Observation p) :
    0 ≤ observationValue observation ∧ observationValue observation ≤ 1 := by
  change 0 ≤ observation.val.val ∧ observation.val.val ≤ 1
  exact observation.val.property

/-- Sum of the simultaneous players' actual own observations in one record. -/
def RoundRecord.totalReward (record : RoundRecord (p := p) (rate := rate)) : ℝ :=
  ∑ player : Fin p.m, observationValue (record.ownEntries player).2

/-- Chronological records form one actual state chain from the fixed boundary
state to the computed final state. -/
def Connected (initial : State p rate) :
    List (RoundRecord (p := p) (rate := rate)) → State p rate → Prop
  | [], final => final = initial
  | record :: rest, final =>
      record.input.state = initial ∧ Connected record.output.next rest final

/-- The fold result stores only its computed final state and chronological
actual round records, together with the derived preservation/linkage facts. -/
structure Run (initial : State p rate) where
  finalState : State p rate
  records : List (RoundRecord (p := p) (rate := rate))
  activations_preserved : finalState.activations = initial.activations
  connected : Connected initial records finalState

/-- Total recorded own reward, computed from the actual chronological step
records. -/
def Run.totalReward {initial : State p rate} (execution : Run initial) : ℝ :=
  (execution.records.map RoundRecord.totalReward).sum

/-- Each actual round contributes between zero and one unit per player. -/
theorem RoundRecord.totalReward_bounds
    (record : RoundRecord (p := p) (rate := rate)) :
    0 ≤ record.totalReward ∧ record.totalReward ≤ (p.m : ℝ) := by
  constructor
  · apply Finset.sum_nonneg
    intro player _
    exact observationValue_bounds (record.ownEntries player).2 |>.1
  · calc
      record.totalReward ≤ ∑ _player : Fin p.m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro player _
        exact observationValue_bounds (record.ownEntries player).2 |>.2
      _ = (p.m : ℝ) := by simp

/-- Extending an actual chain appends one record whose pre-state is the
previous computed successor. -/
theorem Connected.append_one {initial current : State p rate}
    (records : List (RoundRecord (p := p) (rate := rate)))
    (record : RoundRecord (p := p) (rate := rate))
    (hchain : Connected initial records current)
    (hpre : record.input.state = current) :
    Connected initial (records ++ [record]) record.output.next := by
  induction records generalizing initial current with
  | nil =>
      simp only [Connected] at hchain
      subst current
      simp only [List.nil_append, Connected]
      exact ⟨hpre, True.intro⟩
  | cons head tail ih =>
      simp only [Connected] at hchain ⊢
      exact ⟨hchain.1, ih hchain.2 hpre⟩

/-- A coordinator dagger persists through every literal step in a connected
run; it does not stop the physical calendar or erase other round outputs. -/
theorem Connected.coordinator_dagger {initial final : State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (hchain : Connected initial records final)
    (hdagger : initial.coordinator = .dagger) :
    final.coordinator = .dagger ∧
      ∀ record ∈ records, record.input.state.coordinator = .dagger := by
  induction records generalizing initial final with
  | nil =>
      subst final
      exact ⟨hdagger, by simp⟩
  | cons record rest ih =>
      rcases hchain with ⟨hpre, hrest⟩
      have hrecord : record.input.state.coordinator = .dagger := by
        rw [hpre]
        exact hdagger
      have hnext : record.output.next.coordinator = .dagger := by
        rw [record.output_eq]
        exact (ReferenceActivePhysicalStep.step_coordinator_dagger record.input hrecord).1
      obtain ⟨hfinal, hrecords⟩ := ih hrest hnext
      refine ⟨hfinal, ?_⟩
      intro current hcurrent
      rcases List.mem_cons.mp hcurrent with heq | htail
      · subst current
        exact hrecord
      · exact hrecords current htail

/-- A follower's local dagger persists by the accepted local-step theorem,
while the remaining followers and coordinator continue to be folded. -/
theorem Connected.follower_dagger {initial final : State p rate}
    {records : List (RoundRecord (p := p) (rate := rate))}
    (hchain : Connected initial records final) (i : Fin (p.m - 1))
    (hdagger : initial.followers i = .dagger) :
    final.followers i = .dagger ∧
      ∀ record ∈ records, record.input.state.followers i = .dagger := by
  induction records generalizing initial final with
  | nil =>
      subst final
      exact ⟨hdagger, by simp⟩
  | cons record rest ih =>
      rcases hchain with ⟨hpre, hrest⟩
      have hrecord : record.input.state.followers i = .dagger := by
        rw [hpre]
        exact hdagger
      have hnext : record.output.next.followers i = .dagger := by
        rw [record.output_eq]
        exact ReferenceActivePhysicalStep.step_follower_dagger record.input i hrecord
      obtain ⟨hfinal, hrecords⟩ := ih hrest hnext
      refine ⟨hfinal, ?_⟩
      intro current hcurrent
      rcases List.mem_cons.mp hcurrent with heq | htail
      · subst current
        exact hrecord
      · exact hrecords current htail

/-- The actual input at one physical calendar coordinate. Activation typing
comes from the boundary mode and the accumulator's proved preservation field. -/
def roundInputAt (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start : ℕ) (hmode : allActiveAtStart initial start)
    (acc : Run initial) (entry : CalendarEntry p start) : ReferenceActivePhysicalStep.RoundInput p rate :=
  { state := acc.finalState
    rows := rows
    selected := selected
    time := ⟨entry.val, entry.property.2⟩
    active := fun i => by
      rw [acc.activations_preserved]
      exact le_trans (hmode i) (Nat.add_le_add_right entry.property.1 1)
    rewards := rewards }

/-- Perform one calendar entry by constructing its genuine `Fin T` input and
calling exactly the integrated physical step. -/
def foldRound (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start : ℕ) (hmode : allActiveAtStart initial start)
    (acc : Run initial)
    (entry : CalendarEntry p start) : Run initial := by
  let input := roundInputAt initial rows selected rewards start hmode acc entry
  let output := ReferenceActivePhysicalStep.step input
  let record : RoundRecord (p := p) (rate := rate) := ⟨input, output, rfl⟩
  exact {
    finalState := output.next
    records := acc.records ++ [record]
    activations_preserved := by
      exact (ReferenceActivePhysicalStep.step_next_fields input).2.2.1.trans
        acc.activations_preserved
    connected := by
      exact Connected.append_one acc.records record acc.connected rfl }

/-- Fold the one-round worker over one contiguous interval, continuing from a
previous computed accumulator. -/
def foldCalendar (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin intervalStart count : ℕ) (horigin : origin ≤ intervalStart)
    (hspan : intervalStart + count ≤ p.T)
    (hmode : allActiveAtStart initial origin) (acc : Run initial) : Run initial :=
  (calendarEntries origin intervalStart count horigin hspan).foldl
    (foldRound initial rows selected rewards origin hmode) acc

/-- Canonical finite-calendar fold of the existing postlaunch state and
literal one-round transition over `[start, start + count)`. `selected` is
retained as the actual row index; all reward-table coordinates remain present
in `rewards`. -/
def run (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) : Run initial :=
  foldCalendar initial rows selected rewards start start count le_rfl hspan hmode
    ⟨initial, [], rfl, by simp [Connected]⟩

/-- The empty interval computes no physical transition. -/
theorem run_zero_final (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start : ℕ) (hspan : start + 0 ≤ p.T)
    (hmode : allActiveAtStart initial start) :
    (run initial rows selected rewards start 0 hspan hmode).finalState = initial := by
  have hentries : calendarEntries start start 0 le_rfl hspan = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp [calendarEntries, calendar]
  simp only [run, foldCalendar]
  rw [hentries]
  rfl

theorem run_zero_records (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start : ℕ) (hspan : start + 0 ≤ p.T)
    (hmode : allActiveAtStart initial start) :
    (run initial rows selected rewards start 0 hspan hmode).records = [] := by
  have hentries : calendarEntries start start 0 le_rfl hspan = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp [calendarEntries, calendar]
  simp only [run, foldCalendar]
  rw [hentries]
  rfl

/-- Each fold entry contributes exactly one actual record. -/
theorem foldRound_records_length (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start : ℕ)
    (hmode : allActiveAtStart initial start)
    (entries : List (CalendarEntry p start))
    (acc : Run initial) :
    ((entries.foldl (foldRound initial rows selected rewards start hmode) acc).records).length =
      acc.records.length + entries.length := by
  induction entries generalizing acc with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      rw [ih (foldRound initial rows selected rewards start hmode acc entry)]
      simp [foldRound]
      omega

/-- The chronological timestamps added by a fold are exactly the input
calendar entries, after any records already present in the accumulator. -/
theorem foldRound_time_values (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start : ℕ)
    (hmode : allActiveAtStart initial start)
    (entries : List (CalendarEntry p start))
    (acc : Run initial) :
    ((entries.foldl (foldRound initial rows selected rewards start hmode) acc).records.map
      (fun record => record.input.time.val)) =
        acc.records.map (fun record => record.input.time.val) ++ entries.unattach := by
  induction entries generalizing acc with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      rw [ih (foldRound initial rows selected rewards start hmode acc entry)]
      simp [foldRound, roundInputAt, List.map_append]

/-- The typed calendar entries preserve both the standard list length and
the exact consecutive natural timestamp enumeration. -/
theorem calendarEntries_length (origin intervalStart count : ℕ)
    (horigin : origin ≤ intervalStart) (hspan : intervalStart + count ≤ p.T) :
    (calendarEntries origin intervalStart count horigin hspan).length = count := by
  simp [calendarEntries, calendar]

theorem calendarEntries_time_values (origin intervalStart count : ℕ)
    (horigin : origin ≤ intervalStart) (hspan : intervalStart + count ≤ p.T) :
    (calendarEntries origin intervalStart count horigin hspan).unattach =
      calendar intervalStart count := by
  unfold calendarEntries
  simp only [List.unattach, List.map_map]
  change (calendar intervalStart count).attach.unattach = calendar intervalStart count
  exact List.unattach_attach

/-- Splitting one contiguous interval splits its typed standard-list calendar
into the corresponding chronological prefix and suffix. -/
theorem calendarEntries_append (origin intervalStart left right : ℕ)
    (horigin : origin ≤ intervalStart)
    (hspan : intervalStart + (left + right) ≤ p.T) :
    calendarEntries origin intervalStart (left + right) horigin hspan =
      calendarEntries origin intervalStart left horigin (by omega) ++
        calendarEntries origin (intervalStart + left) right (by omega) (by omega) := by
  have hspanLeft : intervalStart + left ≤ p.T := by omega
  have horiginRight : origin ≤ intervalStart + left := by omega
  have hspanRight : intervalStart + left + right ≤ p.T := by omega
  have hcalendar : calendar intervalStart (left + right) =
      calendar intervalStart left ++ calendar (intervalStart + left) right := by
    simp [calendar]
  have hvalues :
      (calendarEntries origin intervalStart (left + right) horigin hspan).unattach =
        (calendarEntries origin intervalStart left horigin hspanLeft).unattach ++
          (calendarEntries origin (intervalStart + left) right horiginRight hspanRight).unattach := by
    calc
      _ = calendar intervalStart (left + right) :=
        calendarEntries_time_values origin intervalStart (left + right) horigin hspan
      _ = calendar intervalStart left ++ calendar (intervalStart + left) right := hcalendar
      _ = (calendarEntries origin intervalStart left horigin hspanLeft).unattach ++
          (calendarEntries origin (intervalStart + left) right horiginRight hspanRight).unattach := by
        rw [calendarEntries_time_values, calendarEntries_time_values]
  have hmap :
      (calendarEntries origin intervalStart (left + right) horigin hspan).map Subtype.val =
        (calendarEntries origin intervalStart left horigin hspanLeft ++
          calendarEntries origin (intervalStart + left) right horiginRight hspanRight).map Subtype.val := by
    simpa only [List.unattach, List.map_append] using hvalues
  exact (List.map_inj_right (f := Subtype.val)
    (fun a b hab => Subtype.ext hab)).mp hmap

/-- Folding a concatenated calendar is the same as continuing the computed
prefix accumulator through the contiguous suffix. -/
theorem foldCalendar_append (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin intervalStart left right : ℕ)
    (horigin : origin ≤ intervalStart)
    (hspan : intervalStart + (left + right) ≤ p.T)
    (hmode : allActiveAtStart initial origin) (acc : Run initial) :
    foldCalendar initial rows selected rewards origin intervalStart (left + right)
        horigin hspan hmode acc =
      foldCalendar initial rows selected rewards origin (intervalStart + left) right
        (by omega) (by omega) hmode
        (foldCalendar initial rows selected rewards origin intervalStart left
          horigin (by omega) hmode acc) := by
  unfold foldCalendar
  rw [calendarEntries_append origin intervalStart left right horigin hspan,
    List.foldl_append]

/-- Prefix concatenation for the canonical execution: the suffix starts from
the prefix's computed state and retained records. -/
theorem run_append (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start left right : ℕ)
    (hspan : start + (left + right) ≤ p.T)
    (hmode : allActiveAtStart initial start) :
    run initial rows selected rewards start (left + right) hspan hmode =
      foldCalendar initial rows selected rewards start (start + left) right
        (by omega) (by omega) hmode
        (run initial rows selected rewards start left (by omega) hmode) := by
  change foldCalendar initial rows selected rewards start start (left + right)
      le_rfl hspan hmode ⟨initial, [], rfl, by simp [Connected]⟩ =
    foldCalendar initial rows selected rewards start (start + left) right
      (by omega) (by omega) hmode
      (foldCalendar initial rows selected rewards start start left le_rfl
        (by omega) hmode ⟨initial, [], rfl, by simp [Connected]⟩)
  exact foldCalendar_append initial rows selected rewards start start left right
    le_rfl hspan hmode ⟨initial, [], rfl, by simp [Connected]⟩

/-- One successor step appends exactly the physical round at `start + count`;
the zero-count case remains the empty fold from `run_zero_final`. -/
theorem run_successor (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ)
    (hspan : start + (count + 1) ≤ p.T)
    (hmode : allActiveAtStart initial start) :
    run initial rows selected rewards start (count + 1) hspan hmode =
      foldCalendar initial rows selected rewards start (start + count) 1
        (by omega) (by omega) hmode
        (run initial rows selected rewards start count (by omega) hmode) :=
  run_append initial rows selected rewards start count 1 hspan hmode

/-- The actual retained input times enumerate `List.range' start count 1` in
chronological order, with no sentinel and no omitted rounds. -/
theorem run_time_values (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) :
    ((run initial rows selected rewards start count hspan hmode).records.map
      (fun record => record.input.time.val)) = calendar start count := by
  have h := foldRound_time_values initial rows selected rewards start hmode
    (calendarEntries start start count le_rfl hspan) ⟨initial, [], rfl, by simp [Connected]⟩
  rw [calendarEntries_time_values] at h
  simpa [run, foldCalendar] using h

/-- The canonical fold retains exactly `count` literal physical rounds. -/
theorem run_record_count (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) :
    (run initial rows selected rewards start count hspan hmode).records.length = count := by
  have h := foldRound_records_length initial rows selected rewards start hmode
    (calendarEntries start start count le_rfl hspan) ⟨initial, [], rfl, by simp [Connected]⟩
  simpa [run, foldCalendar, calendarEntries_length] using h

/-- Pathwise total reward over a canonical fold lies between zero and the
number of players times the number of physically executed rounds. -/
theorem run_totalReward_bounds (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) :
    0 ≤ (run initial rows selected rewards start count hspan hmode).totalReward ∧
      (run initial rows selected rewards start count hspan hmode).totalReward ≤
        (p.m : ℝ) * count := by
  let execution := run initial rows selected rewards start count hspan hmode
  have hlist (records : List (RoundRecord (p := p) (rate := rate))) :
      0 ≤ (records.map RoundRecord.totalReward).sum ∧
        (records.map RoundRecord.totalReward).sum ≤ (p.m : ℝ) * records.length := by
    induction records with
    | nil => simp
    | cons record rest ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        obtain ⟨hrest0, hrest1⟩ := ih
        obtain ⟨hround0, hround1⟩ := RoundRecord.totalReward_bounds record
        constructor
        · exact add_nonneg hround0 hrest0
        · calc
            record.totalReward + (rest.map RoundRecord.totalReward).sum ≤
                (p.m : ℝ) + (p.m : ℝ) * (rest.length : ℝ) :=
              add_le_add hround1 hrest1
            _ = (p.m : ℝ) * ((rest.length : ℝ) + 1) := by ring
            _ = (p.m : ℝ) * ((rest.length + 1 : ℕ) : ℝ) := by
              rw [Nat.cast_add, Nat.cast_one]
  have h := hlist execution.records
  have hcount : execution.records.length = count := by
    dsimp [execution]
    exact run_record_count initial rows selected rewards start count hspan hmode
  constructor
  · simpa [execution, Run.totalReward] using h.1
  · have hupper := h.2
    rw [hcount] at hupper
    simpa [execution, Run.totalReward] using hupper

/-- Persistence is inherited round by round from the accepted coordinator
dagger step theorem. -/
theorem run_coordinator_dagger (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start)
    (hdagger : initial.coordinator = .dagger) :
    (run initial rows selected rewards start count hspan hmode).finalState.coordinator = .dagger ∧
      ∀ record ∈ (run initial rows selected rewards start count hspan hmode).records,
        record.input.state.coordinator = .dagger := by
  exact (run initial rows selected rewards start count hspan hmode).connected.coordinator_dagger
    hdagger

/-- Persistence is inherited independently for each follower from the
accepted follower dagger step theorem. -/
theorem run_follower_dagger (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) (i : Fin (p.m - 1))
    (hdagger : initial.followers i = .dagger) :
    (run initial rows selected rewards start count hspan hmode).finalState.followers i = .dagger ∧
      ∀ record ∈ (run initial rows selected rewards start count hspan hmode).records,
        record.input.state.followers i = .dagger := by
  exact (run initial rows selected rewards start count hspan hmode).connected.follower_dagger i
    hdagger

/-- A projection used only to compare computed rounds. It stores no replacement
protocol state and is never an input to the calendar or a local operation. -/
structure RoundEvidence where
  before : State p rate
  time : Fin p.T
  actions : Fin p.m → Fin p.K
  gridFeedback : Fin p.m → Fin (D p + 1)
  ownEntries : Fin p.m → Fin p.K × ReferencePrelaunchFollower.Observation p
  coordinator : CoordinatorObservation p rate
  followers : Fin (p.m - 1) → FollowerObservation p rate
  after : State p rate

/-- Erase only the unused-table-dependent types from a literal round record;
all actions, observations, diagnostics and states are the actual projections. -/
def RoundRecord.evidence (record : RoundRecord (p := p) (rate := rate)) :
    RoundEvidence (p := p) (rate := rate) :=
  ⟨record.input.state, record.input.time, record.actions, record.gridFeedback,
    record.ownEntries, record.coordinatorDiagnostics, record.followerDiagnostics,
    record.output.next⟩

/-- Derived comparison data for the literal accepted step, never a second
round implementation. -/
def computedEvidence (input : ReferenceActivePhysicalStep.RoundInput p rate) :
    RoundEvidence (p := p) (rate := rate) :=
  (RoundRecord.mk input (ReferenceActivePhysicalStep.step input) rfl).evidence

/-- The actual coordinator arm and sender view use only the selected row.
This is a projection of the original dispatcher, not a second dispatcher. -/
theorem dispatch_selected_row
    (state : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    let x : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, rows, selected, time, active, rewards⟩
    let y : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
    ((dispatch x).arm, (dispatch x).downView) =
      ((dispatch y).arm, (dispatch y).downView) := by
  dsimp only
  rcases state with ⟨coordinator, bank, activations, followers⟩
  cases coordinator with
  | first =>
      let x : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨⟨.first, bank, activations, followers⟩, rows, selected, time, active, rewards⟩
      let y : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨⟨.first, bank, activations, followers⟩, (fun _ => rows selected),
          selected, time, active, rewards⟩
      have hx : dispatch x = .first (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) := rfl
      have hy : dispatch y = .first (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) := rfl
      change ((dispatch x).arm, (dispatch x).downView) =
        ((dispatch y).arm, (dispatch y).downView)
      rw [hx, hy]
      cases h : CoordinatorRoundDispatch.dispatchFirst (firstInput x) with
      | choiceDomainFailure installed => rfl
      | recorderBoundaryFailure installed => rfl
      | choiceRejected installed => rfl
      | chosen installed chosen =>
          by_cases ht : installed.registers.time = time <;>
            simp only [DispatchCut.arm, DispatchCut.downView, DispatchCut.selection,
              selectionAt, x, y, ht, eq_self, dite_true, dite_false,
              Option.map_some, Option.map_none]
          all_goals rfl
  | live r q base =>
      let x : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨⟨.live r q base, bank, activations, followers⟩, rows, selected, time, active, rewards⟩
      let y : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨⟨.live r q base, bank, activations, followers⟩, (fun _ => rows selected),
          selected, time, active, rewards⟩
      have hx : dispatch x = .live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := rfl
      have hy : dispatch y = .live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := rfl
      change ((dispatch x).arm, (dispatch x).downView) =
        ((dispatch y).arm, (dispatch y).downView)
      rw [hx, hy]
      cases h : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) <;>
        simp only [DispatchCut.arm, DispatchCut.downView, DispatchCut.selection,
          selectionAt, x, y, eq_self, dite_true, Option.map_some, Option.map_none]
  | collection payload ledger proposal =>
      let x : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨⟨.collection payload ledger proposal, bank, activations, followers⟩,
          rows, selected, time, active, rewards⟩
      let y : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨⟨.collection payload ledger proposal, bank, activations, followers⟩,
          (fun _ => rows selected), selected, time, active, rewards⟩
      change ((dispatch x).arm, (dispatch x).downView) =
        ((dispatch y).arm, (dispatch y).downView)
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := collectionClock payload ledger proposal cutoff
        have hx : dispatch x = .collection payload ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection (collectionInput x payload ledger clock cutoff)) := by
          simp only [dispatch, show x.state.coordinator = .collection payload ledger proposal from rfl,
            hc, CoordinatorRoundDispatch.dispatch]
          rfl
        have hy : dispatch y = .collection payload ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection (collectionInput x payload ledger clock cutoff)) := by
          simp only [dispatch, show y.state.coordinator = .collection payload ledger proposal from rfl,
            hc, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hx, hy]
        cases h : CoordinatorRoundDispatch.dispatchCollection
          (collectionInput x payload ledger clock cutoff)
        case laterChosen core consistent started hstart instruction hinstruction output
            hlocal clockData installed chosen =>
          by_cases ht : instruction.time = time <;>
            simp only [DispatchCut.arm, DispatchCut.downView, DispatchCut.selection,
              selectionAt, x, y, ht, eq_self, dite_true, dite_false,
              Option.map_some, Option.map_none]
          all_goals rfl
        all_goals rfl
      · have hx : dispatch x = .invalidCollectionCutoff := by
          simp only [dispatch, show x.state.coordinator = .collection payload ledger proposal from rfl,
            hc, dite_false]
        have hy : dispatch y = .invalidCollectionCutoff := by
          simp only [dispatch, show y.state.coordinator = .collection payload ledger proposal from rfl,
            hc, dite_false]
        rw [hx, hy]
        rfl
  | dagger => rfl

/-- The actual simultaneous profile is unaffected by other complete rows. -/
theorem actions_selected_row
    (state : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    let x : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, rows, selected, time, active, rewards⟩
    let y : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
    (prepare x).arms.actions = (prepare y).arms.actions := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
  have ha : (dispatch x).arm = (dispatch y).arm :=
    congrArg Prod.fst (dispatch_selected_row state rows selected time active rewards)
  let followerArm (player : Fin p.m)
      (hplayer : player ≠ ActiveRoundActions.coordinator p.two_le_m) : Fin p.K :=
    let i := ActiveRoundActions.followerIndex p.two_le_m player hplayer
    (DeclaredFollowerLocalRound.prepare rate i (rows selected) (state.activations i)
      time (active i) (state.followers i)).arm
  change (fun player => if hplayer : player = ActiveRoundActions.coordinator p.two_le_m then
      (dispatch x).arm else followerArm player hplayer) =
    (fun player => if hplayer : player = ActiveRoundActions.coordinator p.two_le_m then
      (dispatch y).arm else followerArm player hplayer)
  exact congrArg (fun arm => fun player =>
    if hplayer : player = ActiveRoundActions.coordinator p.two_le_m then arm
    else followerArm player hplayer) ha

/-- The finite grid feedback is derived from the same simultaneous actions. -/
theorem feedback_selected_row
    (state : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    let x : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, rows, selected, time, active, rewards⟩
    let y : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
    (prepare x).feedback.feedback = (prepare y).feedback.feedback := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
  have ha := actions_selected_row state rows selected time active rewards
  funext player
  rw [(prepare x).feedback_rule, (prepare y).feedback_rule, ha]

/-- Typed observations retain the same computed collision feedback. -/
theorem observations_selected_row
    (state : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    let x : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, rows, selected, time, active, rewards⟩
    let y : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
    (prepare x).feedback.observations = (prepare y).feedback.observations := by
  funext player
  rw [ReferenceActiveFeedbackCut.FeedbackCut.observations_eq,
    ReferenceActiveFeedbackCut.FeedbackCut.observations_eq,
    feedback_selected_row state rows selected time active rewards]

/-- Follower failures and full DOWN diagnostics are computed from that
follower's original local preparation, same-row sender view and own observation. -/
theorem followers_selected_row
    (state : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    let x : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, rows, selected, time, active, rewards⟩
    let y : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
    (prepare x).observeFollower = (prepare y).observeFollower := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
  have hv : (dispatch x).downView = (dispatch y).downView :=
    congrArg Prod.snd (dispatch_selected_row state rows selected time active rewards)
  have ho := observations_selected_row state rows selected time active rewards
  funext i
  change finishFollower (dispatch x).downView
      (DeclaredFollowerLocalRound.prepare rate i (rows selected) (state.activations i)
        time (active i) (state.followers i))
      ((prepare x).feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
    finishFollower (dispatch y).downView
      (DeclaredFollowerLocalRound.prepare rate i (rows selected) (state.activations i)
        time (active i) (state.followers i))
      ((prepare y).feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))
  exact congrArg₂ (fun view observation => finishFollower view
    (DeclaredFollowerLocalRound.prepare rate i (rows selected) (state.activations i)
      time (active i) (state.followers i)) observation) hv
    (congrFun ho (PublicDiscreteDraws.followerPlayer p.two_le_m i))

/-- The original live post-choice tail uses the same recorder input and own
feedback when only unused complete rows are replaced. -/
theorem livePostChoice_selected_row
    (state : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    let x : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, rows, selected, time, active, rewards⟩
    let y : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
    livePostChoice (prepare x) r q base started = livePostChoice (prepare y) r q base started := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
  have ha : (dispatch x).arm = (dispatch y).arm :=
    congrArg Prod.fst (dispatch_selected_row state rows selected time active rewards)
  have ho : (prepare x).coordinatorObservation = (prepare y).coordinatorObservation :=
    congrFun (feedback_selected_row state rows selected time active rewards)
      (ActiveRoundActions.coordinator p.two_le_m)
  have hr : liveRecordingInput (prepare x) r started =
      liveRecordingInput (prepare y) r started := by
    exact congrArg₂ (fun arm observation =>
      ({ currentWeights := r.complementWeights
         time := time
         gridBoundary := started.clock.g
         row := rows selected
         ownArm := arm
         observation := observation
         mode := .live (decide (started.pending = ∅)) } :
        CoordinatorRecorderComplementBridge.Input r.payload)) ha ho
  change livePostChoice (prepare x) r q base started = livePostChoice (prepare y) r q base started
  simp only [livePostChoice, hr, ho]
  rfl
/-- The original UP receiver and all its diagnostic fields use the same
selected row, prepared sender and computed coordinator observation. -/
theorem receiveUp_selected_row
    (state : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (ledger : Ledger rate) :
    let x : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, rows, selected, time, active, rewards⟩
    let y : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
    receiveUp (prepare x) ledger = receiveUp (prepare y) ledger := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
  have ho : (prepare x).coordinatorObservation = (prepare y).coordinatorObservation :=
    congrFun (feedback_selected_row state rows selected time active rewards)
      (ActiveRoundActions.coordinator p.two_le_m)
  change receiveUp (prepare x) ledger = receiveUp (prepare y) ledger
  simp only [receiveUp, upInputs, ho]
  rfl

/-- The original collection tail preserves its actual service, reception and
finish operations when unused complete rows are changed. -/
theorem collectionPostChoice_selected_row
    (state : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (payload : Payload rate) (ledger : Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    let x : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, rows, selected, time, active, rewards⟩
    let y : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
    collectionPostChoice (prepare x) payload ledger started weights =
      collectionPostChoice (prepare y) payload ledger started weights := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
  have ha : (dispatch x).arm = (dispatch y).arm :=
    congrArg Prod.fst (dispatch_selected_row state rows selected time active rewards)
  have ho : (prepare x).coordinatorObservation = (prepare y).coordinatorObservation :=
    congrFun (feedback_selected_row state rows selected time active rewards)
      (ActiveRoundActions.coordinator p.two_le_m)
  have hr : collectionRecordingInput (prepare x) payload started weights =
      collectionRecordingInput (prepare y) payload started weights := by
    exact congrArg₂ (fun arm observation =>
      ({ currentWeights := weights
         time := time
         gridBoundary := started.clock.g
         row := rows selected
         ownArm := arm
         observation := observation
         mode := .collection } :
        CoordinatorRecorderComplementBridge.Input payload)) ha ho
  change collectionPostChoice (prepare x) payload ledger started weights =
    collectionPostChoice (prepare y) payload ledger started weights
  have hu (current : Ledger rate) : receiveUp (prepare x) current = receiveUp (prepare y) current :=
    receiveUp_selected_row state rows selected time active rewards current
  simp only [collectionPostChoice, hr, hu]
  rfl

/-- The full coordinator result, including UP decoder diagnostics and every
local failure, uses only the selected complete row. -/
theorem coordinator_selected_row
    (state : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    let x : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, rows, selected, time, active, rewards⟩
    let y : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
    (prepare x).observeCoordinator = (prepare y).observeCoordinator := by
  dsimp only
  rcases state with ⟨coordinator, bank, activations, followers⟩
  cases coordinator with
  | first =>
      let x : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨⟨.first, bank, activations, followers⟩, rows, selected, time, active, rewards⟩
      let y : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨⟨.first, bank, activations, followers⟩, (fun _ => rows selected),
          selected, time, active, rewards⟩
      have hlive (r' : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (q' : CoordinatorLiveServiceFinish.OwnedRegisters r')
          (base' : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
          livePostChoice (prepare x) r' q' base' started =
            livePostChoice (prepare y) r' q' base' started :=
        livePostChoice_selected_row _ rows selected time active rewards r' q' base' started
      have hcollection (payload' : Payload rate) (ledger' : Ledger rate)
          (started : CoordinatorPhaseClock.StartRoundResult p)
          (weights : CanonicalFastSampling.FastArm payload'.slowSet → ℝ) :
          collectionPostChoice (prepare x) payload' ledger' started weights =
            collectionPostChoice (prepare y) payload' ledger' started weights :=
        collectionPostChoice_selected_row _ rows selected time active rewards
          payload' ledger' started weights
      have hx : dispatch x = .first (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) := rfl
      have hy : dispatch y = .first (CoordinatorRoundDispatch.dispatchFirst (firstInput x)) := rfl
      change (prepare x).observeCoordinator = (prepare y).observeCoordinator
      rw [observeCoordinator_first_equation (prepare x) _ hx,
        observeCoordinator_first_equation (prepare y) _ hy]
      cases h : CoordinatorRoundDispatch.dispatchFirst (firstInput x) with
      | choiceDomainFailure installed => simp only [DispatchCut.selection, eq_self, ite_true]; rfl
      | recorderBoundaryFailure installed => simp only [DispatchCut.selection, eq_self, ite_true]; rfl
      | choiceRejected installed => simp only [DispatchCut.selection, eq_self, ite_true]; rfl
      | chosen installed chosen =>
          by_cases ht : installed.registers.time = time <;>
            simp only [DispatchCut.selection, selectionAt, x, y, ht, eq_self,
              dite_true, dite_false, reduceCtorEq, ite_true, ite_false]
          all_goals exact hlive _ _ _ _
  | live r q base =>
      let x : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨⟨.live r q base, bank, activations, followers⟩, rows, selected, time, active, rewards⟩
      let y : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨⟨.live r q base, bank, activations, followers⟩, (fun _ => rows selected),
          selected, time, active, rewards⟩
      have hlive (r' : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (q' : CoordinatorLiveServiceFinish.OwnedRegisters r')
          (base' : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
          livePostChoice (prepare x) r' q' base' started =
            livePostChoice (prepare y) r' q' base' started :=
        livePostChoice_selected_row _ rows selected time active rewards r' q' base' started
      have hcollection (payload' : Payload rate) (ledger' : Ledger rate)
          (started : CoordinatorPhaseClock.StartRoundResult p)
          (weights : CanonicalFastSampling.FastArm payload'.slowSet → ℝ) :
          collectionPostChoice (prepare x) payload' ledger' started weights =
            collectionPostChoice (prepare y) payload' ledger' started weights :=
        collectionPostChoice_selected_row _ rows selected time active rewards
          payload' ledger' started weights
      have hx : dispatch x = .live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := rfl
      have hy : dispatch y = .live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := rfl
      change (prepare x).observeCoordinator = (prepare y).observeCoordinator
      rw [observeCoordinator_live_equation (prepare x) _ _ _ _ hx,
        observeCoordinator_live_equation (prepare y) _ _ _ _ hy]
      cases h : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) <;>
        simp only [DispatchCut.selection, selectionAt, x, y, eq_self, dite_true,
          reduceCtorEq, ite_true, ite_false, hlive]
      all_goals exact hcollection _ _ _ _
  | collection payload ledger proposal =>
      let x : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨⟨.collection payload ledger proposal, bank, activations, followers⟩,
          rows, selected, time, active, rewards⟩
      let y : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨⟨.collection payload ledger proposal, bank, activations, followers⟩,
          (fun _ => rows selected), selected, time, active, rewards⟩
      change (prepare x).observeCoordinator = (prepare y).observeCoordinator
      have hlive (r' : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (q' : CoordinatorLiveServiceFinish.OwnedRegisters r')
          (base' : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
          livePostChoice (prepare x) r' q' base' started =
            livePostChoice (prepare y) r' q' base' started :=
        livePostChoice_selected_row _ rows selected time active rewards r' q' base' started
      have hcollection (payload' : Payload rate) (ledger' : Ledger rate)
          (started : CoordinatorPhaseClock.StartRoundResult p)
          (weights : CanonicalFastSampling.FastArm payload'.slowSet → ℝ) :
          collectionPostChoice (prepare x) payload' ledger' started weights =
            collectionPostChoice (prepare y) payload' ledger' started weights :=
        collectionPostChoice_selected_row _ rows selected time active rewards
          payload' ledger' started weights
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := collectionClock payload ledger proposal cutoff
        have hx : dispatch x = .collection payload ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection (collectionInput x payload ledger clock cutoff)) := by
          simp only [dispatch, show x.state.coordinator = .collection payload ledger proposal from rfl,
            hc, CoordinatorRoundDispatch.dispatch]
          rfl
        have hy : dispatch y = .collection payload ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection (collectionInput x payload ledger clock cutoff)) := by
          simp only [dispatch, show y.state.coordinator = .collection payload ledger proposal from rfl,
            hc, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [observeCoordinator_collection_equation (prepare x) _ _ _ _ _ hx,
          observeCoordinator_collection_equation (prepare y) _ _ _ _ _ hy]
        cases h : CoordinatorRoundDispatch.dispatchCollection
          (collectionInput x payload ledger clock cutoff)
        case laterChosen core consistent started hstart instruction hinstruction output
            hlocal clockData installed chosen =>
          by_cases ht : instruction.time = time <;>
            simp only [DispatchCut.selection, selectionAt, x, y, ht, eq_self,
              dite_true, dite_false, reduceCtorEq, ite_true, ite_false]
          all_goals exact hlive _ _ _ _
        case continuing core snapshot boundary checked =>
          simp only [DispatchCut.selection, reduceCtorEq, ite_false]
          exact hcollection _ _ _ _
        all_goals simp only [DispatchCut.selection, eq_self, ite_true]
        all_goals rfl
      · have hx : dispatch x = .invalidCollectionCutoff := by
          simp only [dispatch, show x.state.coordinator = .collection payload ledger proposal from rfl,
            hc, dite_false]
        have hy : dispatch y = .invalidCollectionCutoff := by
          simp only [dispatch, show y.state.coordinator = .collection payload ledger proposal from rfl,
            hc, dite_false]
        simp only [PreparedRound.observeCoordinator, prepare, hx, hy,
          DispatchCut.selection, eq_self]
        all_goals rfl
  | dagger =>
      simp only [PreparedRound.observeCoordinator, prepare, dispatch,
        DispatchCut.selection, eq_self]
      rfl

/-- All retained comparison data comes from the literal accepted round,
and factors through the selected complete row. -/
theorem computedEvidence_selected_row
    (state : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    computedEvidence ⟨state, rows, selected, time, active, rewards⟩ =
      computedEvidence ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩ := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩
  have ha := actions_selected_row state rows selected time active rewards
  have hg := feedback_selected_row state rows selected time active rewards
  have hc := coordinator_selected_row state rows selected time active rewards
  have hf := followers_selected_row state rows selected time active rewards
  have he : (ReferenceActivePhysicalStep.step x).ownEntries =
      (ReferenceActivePhysicalStep.step y).ownEntries := by
    funext player
    rw [ReferenceActivePhysicalStep.step_own_entry, ReferenceActivePhysicalStep.step_own_entry,
      ha, hg]
  have hn : (ReferenceActivePhysicalStep.step x).next =
      (ReferenceActivePhysicalStep.step y).next := by
    exact congrArg₂ (fun (coordinator : CoordinatorObservation p rate)
      (followers : Fin (p.m - 1) → FollowerObservation p rate) =>
        ReferenceActivePhysicalStep.State.mk coordinator.configuration coordinator.upDecoderBank
          state.activations (fun i => (followers i).configuration)) hc hf
  change RoundEvidence.mk state time (prepare x).arms.actions (prepare x).feedback.feedback
      (ReferenceActivePhysicalStep.step x).ownEntries (prepare x).observeCoordinator
      (prepare x).observeFollower (ReferenceActivePhysicalStep.step x).next =
    RoundEvidence.mk state time (prepare y).arms.actions (prepare y).feedback.feedback
      (ReferenceActivePhysicalStep.step y).ownEntries (prepare y).observeCoordinator
      (prepare y).observeFollower (ReferenceActivePhysicalStep.step y).next
  congr 1

/-- Replacing arbitrary other complete rows preserves the literal step's
computed data, with the initial state and selected index fixed. -/
theorem computedEvidence_rows
    (state : State p rate) (rows otherRows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hrow : rows selected = otherRows selected) :
    computedEvidence ⟨state, rows, selected, time, active, rewards⟩ =
      computedEvidence ⟨state, otherRows, selected, time, active, rewards⟩ := by
  calc
    _ = computedEvidence ⟨state, (fun _ => rows selected), selected, time, active, rewards⟩ :=
      computedEvidence_selected_row state rows selected time active rewards
    _ = computedEvidence ⟨state, (fun _ => otherRows selected), selected, time, active, rewards⟩ :=
      congrArg (fun row => computedEvidence ⟨state, (fun _ => row), selected, time, active, rewards⟩) hrow
    _ = _ := (computedEvidence_selected_row state otherRows selected time active rewards).symm

/-- Congruence of actual computed data. Every compared input field is explicit;
no history or successful-operation premise is supplied. -/
theorem computedEvidence_congr
    (left right : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : left.state = right.state) (hselected : left.selected = right.selected)
    (htime : left.time = right.time) (hrewards : left.rewards = right.rewards)
    (hrow : left.row = right.row) : computedEvidence left = computedEvidence right := by
  rcases left with ⟨state, rows, selected, time, active, rewards⟩
  rcases right with ⟨otherState, otherRows, otherSelected, otherTime, otherActive, otherRewards⟩
  dsimp only at hstate hselected htime hrewards
  cases hstate
  cases hselected
  cases htime
  cases hrewards
  exact computedEvidence_rows state rows otherRows selected time active rewards hrow
/-- With the boundary state fixed, preserving the selected complete row
preserves every successor, action, own observation and decoder diagnostic.
The initial state is not asserted to have been constructed from that row. -/
theorem run_rows_eq (initial : State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) (hrow : rows selected = otherRows selected) :
    (run initial rows selected rewards start count hspan hmode).finalState =
        (run initial otherRows selected rewards start count hspan hmode).finalState ∧
      (run initial rows selected rewards start count hspan hmode).records.map RoundRecord.evidence =
        (run initial otherRows selected rewards start count hspan hmode).records.map
          RoundRecord.evidence := by
  unfold run foldCalendar
  refine List.foldl_rel
    (r := fun (left right : Run initial) => left.finalState = right.finalState ∧
      left.records.map RoundRecord.evidence = right.records.map RoundRecord.evidence)
    ⟨rfl, rfl⟩ ?_
  intro entry _ left right h
  let x := roundInputAt initial rows selected rewards start hmode left entry
  let y := roundInputAt initial otherRows selected rewards start hmode right entry
  have hi : computedEvidence x = computedEvidence y :=
    computedEvidence_congr x y h.1 rfl rfl rfl hrow
  constructor
  · change (ReferenceActivePhysicalStep.step x).next = (ReferenceActivePhysicalStep.step y).next
    exact congrArg RoundEvidence.after hi
  · change (left.records ++ [RoundRecord.mk x (ReferenceActivePhysicalStep.step x) rfl]).map
        RoundRecord.evidence =
      (right.records ++ [RoundRecord.mk y (ReferenceActivePhysicalStep.step y) rfl]).map
        RoundRecord.evidence
    simp only [List.map_append, List.map_singleton]
    exact congrArg₂ (fun a b : List (RoundEvidence (p := p) (rate := rate)) => a ++ b) h.2
      (congrArg (fun evidence => [evidence]) hi)
/-- One append records exactly its actual input and literal step output. -/
theorem foldRound_equations (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start : ℕ) (hmode : allActiveAtStart initial start) (acc : Run initial)
    (entry : CalendarEntry p start) :
    let input := roundInputAt initial rows selected rewards start hmode acc entry
    (foldRound initial rows selected rewards start hmode acc entry).finalState =
        (ReferenceActivePhysicalStep.step input).next ∧
      (foldRound initial rows selected rewards start hmode acc entry).records =
        acc.records ++ [RoundRecord.mk input (ReferenceActivePhysicalStep.step input) rfl] :=
  ⟨rfl, rfl⟩

/-- A one-element calendar contains exactly the one physical coordinate. -/
theorem calendarEntries_one (origin intervalStart : ℕ) (horigin : origin ≤ intervalStart)
    (hspan : intervalStart + 1 ≤ p.T) :
    calendarEntries origin intervalStart 1 horigin hspan =
      [⟨intervalStart, horigin, by omega⟩] := by
  apply (List.map_inj_right (f := Subtype.val) (fun a b hab => Subtype.ext hab)).mp
  change (calendarEntries origin intervalStart 1 horigin hspan).unattach = [intervalStart]
  rw [calendarEntries_time_values]
  rfl

/-- The successor equation exposes the single literal step at `start+count`;
there is no action at the source terminal sentinel. -/
theorem run_successor_step (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : allActiveAtStart initial start) :
    run initial rows selected rewards start (count + 1) hspan hmode =
      foldRound initial rows selected rewards start hmode
        (run initial rows selected rewards start count (by omega) hmode)
        ⟨start + count, by omega, by omega⟩ := by
  rw [run_successor]
  unfold foldCalendar
  rw [calendarEntries_one]
  rfl

/-- The canonical execution's chronological records link every pre-state to
the preceding literal successor and finish at the computed final state. -/
theorem run_connected (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) :
    Connected initial (run initial rows selected rewards start count hspan hmode).records
      (run initial rows selected rewards start count hspan hmode).finalState :=
  (run initial rows selected rewards start count hspan hmode).connected

/-- All stored activations are preserved by the actual step field equation. -/
theorem run_activations_preserved (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) :
    (run initial rows selected rewards start count hspan hmode).finalState.activations =
      initial.activations :=
  (run initial rows selected rewards start count hspan hmode).activations_preserved

/-- The end state supplies the all-active mode at the later calendar boundary,
without an additional successor-round activation premise. -/
theorem run_allActiveAtEnd (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) :
    allActiveAtStart (run initial rows selected rewards start count hspan hmode).finalState
      (start + count) := by
  intro i
  rw [run_activations_preserved]
  exact le_trans (hmode i) (Nat.add_le_add_right (Nat.le_add_right start count) 1)

/-- At the terminal boundary the mode proof follows from the original typed
activation fields; the zero-length fold performs no physical operation. -/
theorem run_terminal (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    let hmode : allActiveAtStart initial p.T := fun i => (initial.activations i).property.2
    (run initial rows selected rewards p.T 0 (by omega) hmode).finalState = initial ∧
      (run initial rows selected rewards p.T 0 (by omega) hmode).records = [] :=
  ⟨run_zero_final initial rows selected rewards p.T (by omega) _,
    run_zero_records initial rows selected rewards p.T (by omega) _⟩

/-- Every retained input contains the original full table, the fixed selected
index and the full reward table; no row is reselected or resampled by the fold. -/
theorem run_record_inputs (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) :
    ∀ record ∈ (run initial rows selected rewards start count hspan hmode).records,
      record.input.rows = rows ∧ record.input.selected = selected ∧ record.input.rewards = rewards := by
  unfold run foldCalendar
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

end Bandits.Support.ReferenceActivePhysicalHorizon

end
