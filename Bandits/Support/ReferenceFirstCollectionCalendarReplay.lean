/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionEnabledPrefix
public import Bandits.Support.ReferenceFirstCollectionRawCells

import Lean.Elab.Tactic.Omega

/-!
# Calendar replay for the actual first collection prefix

For an actual selected input in the original first collection window, the
pre-reception ledger replays the preceding physical collection rows in their
calendar order.  The current row is treated only as the literal pure
`startRoundCandidate`; this file makes no claim that its actual protocol step
succeeds.

The source evidence is `sources/zip4/manuscript/06_interruptions.tex:9-100,
246-295`, `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferenceCollectionSegmentExtraction
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceFirstCollectionEpochAlignment
open Bandits.Support.ReferenceFirstCollectionChosenContext
open Bandits.Support.ReferenceFirstCollectionEnabledPrefix
open Bandits.Support.ReferenceFirstCollectionRawCells
open Bandits.Support.ReferenceCollectionRawBufferHistory
open Bandits.Support.CollectionBufferProvenance
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.QueueReplay

namespace Bandits.Support.ReferenceFirstCollectionCalendarReplay

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters}

/-- Recover the recorder option from the actual first matching physical row.
The selected prefixes in this module separately prove that the matching row
is unique whenever a lookup is used. -/
def prefixDiagnosticSequence (rate : RateInput p) (records : List
    (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    Fin p.T → Option (Fin p.K × ℕ) := fun time =>
  match ReferenceFirstCollectionRawCells.findPhysicalRecord? records time with
  | none => none
  | some record => ReferenceCollectionRawBufferHistory.rawDiagnostic record

private theorem mem_take_getElem {α : Type} (records : List α) (count : ℕ)
    {record : α} (hmem : record ∈ records.take count) :
    ∃ index, index < count ∧ ∃ hindex : index < records.length,
      records[index]'hindex = record := by
  obtain ⟨index, hindex, hget⟩ := List.mem_iff_getElem.mp hmem
  have hbounds : index < count ∧ index < records.length := by
    simp only [List.length_take] at hindex
    omega
  refine ⟨index, hbounds.1, ⟨hbounds.2, ?_⟩⟩
  exact (List.getElem_take' hbounds.2 hbounds.1).trans hget

private theorem findPhysicalRecord_eq_none_of_no_match
    (rate : RateInput p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (time : Fin p.T)
    (hno : ∀ record ∈ records, record.input.time ≠ time) :
    ReferenceFirstCollectionRawCells.findPhysicalRecord? records time = none := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      have hhead := hno record (by simp)
      have htail : ∀ later ∈ rest, later.input.time ≠ time := by
        intro later hmem
        exact hno later (List.mem_cons_of_mem record hmem)
      change List.find? (fun item => decide (item.input.time = time))
          (record :: rest) = none
      rw [List.find?_cons]
      have hpred : decide (record.input.time = time) = false := by
        simp [hhead]
      rw [hpred]
      change ReferenceFirstCollectionRawCells.findPhysicalRecord? rest time = none
      exact ih htail

private theorem findPhysicalRecord_eq_some_of_unique
    (rate : RateInput p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (time : Fin p.T) (record : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate))
    (hmem : record ∈ records) (htime : record.input.time = time)
    (hunique : ∀ left ∈ records, ∀ right ∈ records,
      left.input.time = right.input.time → left = right) :
    ReferenceFirstCollectionRawCells.findPhysicalRecord? records time = some record := by
  induction records with
  | nil => simp at hmem
  | cons head tail ih =>
      rcases List.mem_cons.mp hmem with heq | htail
      · subst record
        simp [ReferenceFirstCollectionRawCells.findPhysicalRecord?, htime]
      · have htailUnique : ∀ left ∈ tail, ∀ right ∈ tail,
            left.input.time = right.input.time → left = right := by
          intro left hleft right hright htimes
          exact hunique left (List.mem_cons_of_mem head hleft)
            right (List.mem_cons_of_mem head hright) htimes
        by_cases hhead : head.input.time = time
        · have heq : head = record :=
            hunique head (by simp) record (by simp [htail])
              (hhead.trans htime.symm)
          subst record
          simp [ReferenceFirstCollectionRawCells.findPhysicalRecord?, hhead]
        · change List.find? (fun item => decide (item.input.time = time))
            (head :: tail) = some record
          rw [List.find?_cons]
          have hpred : decide (head.input.time = time) = false := by simp [hhead]
          rw [hpred]
          change ReferenceFirstCollectionRawCells.findPhysicalRecord? tail time = some record
          exact ih htail htailUnique

private theorem time_unique_append_singleton {α β : Type}
    (records : List α) (last : α) (time : α → β)
    (hunique : ∀ left ∈ records, ∀ right ∈ records,
      time left = time right → left = right)
    (hno : ∀ record ∈ records, time record ≠ time last) :
    ∀ left ∈ records ++ [last], ∀ right ∈ records ++ [last],
      time left = time right → left = right := by
  intro left hleft right hright htimes
  rcases List.mem_append.mp hleft with hleftPrefix | hleftLast
  · rcases List.mem_append.mp hright with hrightPrefix | hrightLast
    · exact hunique left hleftPrefix right hrightPrefix htimes
    · have hright : right = last := List.mem_singleton.mp hrightLast
      exact False.elim (hno left hleftPrefix (by simpa [hright] using htimes))
  · have hleft : left = last := List.mem_singleton.mp hleftLast
    rcases List.mem_append.mp hright with hrightPrefix | hrightLast
    · exact False.elim (hno right hrightPrefix (by simpa [hleft] using htimes.symm))
    · have hright : right = last := List.mem_singleton.mp hrightLast
      rw [hleft, hright]

private theorem prefixDiagnosticSequence_eq_of_find
    (rate : RateInput p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (time : Fin p.T) (record : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate))
    (hfind : ReferenceFirstCollectionRawCells.findPhysicalRecord? records time =
      some record) :
    prefixDiagnosticSequence rate records time =
      ReferenceCollectionRawBufferHistory.rawDiagnostic record := by
  simp [prefixDiagnosticSequence, hfind]

private theorem rawDiagnostic_amount_le_D
    (rate : RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (arm : Fin p.K) (amount : ℕ)
    (hdiag : ReferenceCollectionRawBufferHistory.rawDiagnostic record =
      some (arm, amount)) :
    amount ≤ ConstructorDimensions.D p := by
  unfold ReferenceCollectionRawBufferHistory.rawDiagnostic at hdiag
  cases hrecording : record.output.coordinator.recording with
  | none => simp [hrecording] at hdiag
  | some output =>
      cases hgate : output.gateArm with
      | none => simp [hrecording, hgate] at hdiag
      | some recordedArm =>
          have hpair : (recordedArm, output.rawArrival) = (arm, amount) := by
            simpa [hrecording, hgate] using hdiag
          have hamount := congrArg Prod.snd hpair
          have hamount' : output.rawArrival = amount := by simpa using hamount
          rw [← hamount']
          exact output.rawArrival_le_D

private theorem calendarIndices_succ (T start length : ℕ)
    (hbound : start + (length + 1) ≤ T) :
    CoordinatorCollectionLedger.calendarIndices T start (length + 1) hbound =
      (⟨start, by omega⟩ : Fin T) ::
        CoordinatorCollectionLedger.calendarIndices T (start + 1) length (by omega) := by
  simp only [CoordinatorCollectionLedger.calendarIndices, List.ofFn_succ]
  apply congrArg (fun tail => (⟨start, by omega⟩ : Fin T) :: tail)
  apply congrArg List.ofFn
  funext i
  apply Fin.ext
  simp
  omega

private theorem calendar_next_bound (origin count : ℕ) (time : Fin p.T)
    (htime : time.val + 1 = (origin + 1) + count) :
    origin + count + 1 ≤ p.T := by
  have hlt := time.isLt
  omega

private theorem calendarIndices_eq_map_take {α : Type}
    (records : List α) (time : α → Fin p.T) (origin count : ℕ)
    (hcount : count ≤ records.length) (hbound : origin + count ≤ p.T)
    (hchron : ∀ i (hi : i < records.length), (time records[i]).val = origin + i) :
    CoordinatorCollectionLedger.calendarIndices p.T origin count hbound =
      (records.take count).map time := by
  induction count generalizing origin records with
  | zero => simp [CoordinatorCollectionLedger.calendarIndices]
  | succ count ih =>
      cases records with
      | nil => simp at hcount
      | cons head tail =>
          have htailCount : count ≤ tail.length := by simpa using hcount
          have hheadChron : (time head).val = origin := by
            have h := hchron 0 (by simp only [List.length_cons]; omega)
            change (time head).val = origin
            exact h
          have hhead : time head = (⟨origin, by omega⟩ : Fin p.T) := by
            apply Fin.ext
            exact hheadChron
          have htailChron : ∀ i (hi : i < tail.length),
              (time tail[i]).val = (origin + 1) + i := by
            intro i hi
            have hi' : i + 1 < (head :: tail).length := by
              simp only [List.length_cons]
              omega
            have h := hchron (i + 1) hi'
            have hget : (head :: tail)[i + 1] = tail[i] := by
              rw [List.getElem_cons_succ]
            rw [hget] at h
            omega
          have hsplit := calendarIndices_succ p.T origin count (by omega)
          have htailBound : (origin + 1) + count ≤ p.T := by omega
          have htail := ih tail (origin + 1) htailCount htailBound htailChron
          calc
            CoordinatorCollectionLedger.calendarIndices p.T origin (count + 1) hbound =
                (⟨origin, by omega⟩ : Fin p.T) ::
                  CoordinatorCollectionLedger.calendarIndices p.T (origin + 1) count
                    (by omega) := by
                      simpa only [Nat.add_comm count 1] using hsplit
            _ = time head :: (tail.take count).map time := by
              rw [← hhead, htail]
            _ = ((head :: tail).take (count + 1)).map time := by
              simp only [List.take_succ_cons, List.map_cons]

private theorem startRoundCandidate_buffer_other_round
    (rate : RateInput p)
    (ledger : CoordinatorCollectionLedger.Ledger (p := p) rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (round : Fin p.T) (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (arm : Fin p.K) (time : Fin p.T) (hneq : time ≠ round) :
    (CoordinatorCollectionLedger.startRoundCandidate ledger round enabled raw).rawBuffer
        arm time = ledger.rawBuffer arm time := by
  cases hraw : raw with
  | none => rfl
  | some pair =>
      rcases pair with ⟨recordedArm, amount⟩
      by_cases hcondition : ledger.currentRegisters recordedArm = none ∧
          0 < amount ∧ CoordinatorCollectionLedger.sourceRound round < ledger.freezeAt
      · have hput := CoordinatorCollectionLedger.putRaw_other ledger.rawBuffer
          recordedArm arm round time amount (Or.inr hneq)
        simpa [CoordinatorCollectionLedger.startRoundCandidate, hraw, hcondition]
          using hput
      · simp [CoordinatorCollectionLedger.startRoundCandidate, hraw, hcondition]

private theorem physicalRawCell_getD_eq_replayArrival
    (rate : RateInput p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (freezeAt : ℕ) (arm : Fin p.K) (time : Fin p.T) :
    (ReferenceFirstCollectionRawCells.physicalRawCell records freezeAt arm time).getD 0 =
      CoordinatorCollectionLedger.replayArrival
        (prefixDiagnosticSequence rate records) freezeAt arm time := by
  by_cases hbefore : time.val + 1 < freezeAt
  · unfold CoordinatorCollectionLedger.replayArrival
    rw [if_pos (by simpa [CoordinatorCollectionLedger.sourceRound] using hbefore)]
    unfold CoordinatorCollectionLedger.explicitArrival
    cases hfind : ReferenceFirstCollectionRawCells.findPhysicalRecord? records time with
    | none => simp [ReferenceFirstCollectionRawCells.physicalRawCell,
        prefixDiagnosticSequence, hfind]
    | some record =>
        cases hdiag : ReferenceCollectionRawBufferHistory.rawDiagnostic record with
        | none => simp [ReferenceFirstCollectionRawCells.physicalRawCell,
            prefixDiagnosticSequence, hfind, hdiag]
        | some pair =>
            rcases pair with ⟨recordedArm, amount⟩
            by_cases harm : recordedArm = arm
            · by_cases hpositive : 0 < amount
              · simp [ReferenceFirstCollectionRawCells.physicalRawCell,
                  prefixDiagnosticSequence, hfind, hdiag, harm, hpositive,
                  hbefore]
              · have hzero : amount = 0 := by omega
                simp [ReferenceFirstCollectionRawCells.physicalRawCell,
                  prefixDiagnosticSequence, hfind, hdiag, harm, hzero]
            · simp [ReferenceFirstCollectionRawCells.physicalRawCell,
                prefixDiagnosticSequence, hfind, hdiag, harm]
  · unfold ReferenceFirstCollectionRawCells.physicalRawCell
    cases hfind : ReferenceFirstCollectionRawCells.findPhysicalRecord? records time with
    | none => simp [CoordinatorCollectionLedger.replayArrival,
        CoordinatorCollectionLedger.sourceRound, hbefore, hfind, prefixDiagnosticSequence]
    | some record =>
        cases hdiag : ReferenceCollectionRawBufferHistory.rawDiagnostic record with
        | none => simp [CoordinatorCollectionLedger.replayArrival,
            CoordinatorCollectionLedger.sourceRound, hbefore, hfind, hdiag,
            prefixDiagnosticSequence]
        | some pair =>
            rcases pair with ⟨recordedArm, amount⟩
            simp [CoordinatorCollectionLedger.replayArrival,
              CoordinatorCollectionLedger.sourceRound, hbefore, hfind, hdiag,
              prefixDiagnosticSequence]

private theorem replay_total_mass_bound
    (capacity arrivalBound : ℕ) (initial : ℕ × ℕ)
    (records : List (Bool × ℕ))
    (harrival : ∀ record ∈ records, record.2 ≤ arrivalBound) :
    (QueueReplay.replay capacity initial records).1 +
      (QueueReplay.replay capacity initial records).2 ≤
        initial.1 + initial.2 + records.length * arrivalBound := by
  induction records generalizing initial with
  | nil => simp [QueueReplay.replay]
  | cons record rest ih =>
      have htail : ∀ later ∈ rest, later.2 ≤ arrivalBound := by
        intro later hmem
        exact harrival later (List.mem_cons_of_mem record hmem)
      have hrecord := harrival record (by simp)
      have hstep :
          (QueueReplay.transition capacity initial record).1 +
            (QueueReplay.transition capacity initial record).2 ≤
              initial.1 + initial.2 + record.2 := by
        cases record with
        | mk enabled amount =>
            cases enabled
            · simp [QueueReplay.transition]
            · have hmin : min capacity (initial.2 + amount) ≤ initial.2 + amount :=
                Nat.min_le_right _ _
              simp only [QueueReplay.transition, Bool.true_eq, ↓reduceIte]
              omega
      change (QueueReplay.replay capacity initial ([record] ++ rest)).1 +
          (QueueReplay.replay capacity initial ([record] ++ rest)).2 ≤ _
      rw [QueueReplay.replay_append]
      have hrest := ih (QueueReplay.transition capacity initial record) htail
      simp only [QueueReplay.replay] at hrest ⊢
      calc
        (QueueReplay.replay capacity (QueueReplay.transition capacity initial record)
          rest).1 +
            (QueueReplay.replay capacity (QueueReplay.transition capacity initial record)
              rest).2 ≤
            (QueueReplay.transition capacity initial record).1 +
              (QueueReplay.transition capacity initial record).2 +
                rest.length * arrivalBound := hrest
        _ ≤ initial.1 + initial.2 + record.2 + rest.length * arrivalBound :=
          Nat.add_le_add_right hstep _
        _ ≤ initial.1 + initial.2 + arrivalBound + rest.length * arrivalBound := by
          exact Nat.add_le_add_right (Nat.add_le_add_left hrecord _) _
        _ = initial.1 + initial.2 + (rest.length + 1) * arrivalBound := by
          rw [Nat.add_mul, Nat.one_mul]
          omega

private theorem transition_score_increment_le_capacity
    (capacity : ℕ) (registers : ℕ × ℕ) (record : Bool × ℕ) :
    (QueueReplay.transition capacity registers record).1 - registers.1 ≤ capacity := by
  cases record with
  | mk enabled amount =>
      cases enabled
      · simp [QueueReplay.transition]
      · have hmin : min capacity (registers.2 + amount) ≤ capacity :=
          Nat.min_le_left _ _
        simp only [QueueReplay.transition, Bool.true_eq, ↓reduceIte]
        omega

private theorem replay_prefix_bounds
    (capacity arrivalBound : ℕ) (initialQueue : ℕ)
    (records : List (Bool × ℕ))
    (harrival : ∀ record ∈ records, record.2 ≤ arrivalBound) :
    (∀ k, k ≤ records.length →
      let endpoint := QueueReplay.replay capacity (0, initialQueue) (records.take k)
      endpoint.1 ≤ initialQueue + k * arrivalBound ∧
        endpoint.2 ≤ initialQueue + k * arrivalBound) ∧
    (∀ k, k < records.length →
      (QueueReplay.replay capacity (0, initialQueue) (records.take (k + 1))).1 -
        (QueueReplay.replay capacity (0, initialQueue) (records.take k)).1 ≤ capacity) := by
  constructor
  · intro k hk
    let prefixRecords := records.take k
    have hprefixArrival : ∀ record ∈ prefixRecords, record.2 ≤ arrivalBound := by
      intro record hmem
      exact harrival record (List.mem_of_mem_take hmem)
    have hmass := replay_total_mass_bound capacity arrivalBound (0, initialQueue)
      prefixRecords hprefixArrival
    have hlength : prefixRecords.length = k := by
      simp [prefixRecords, List.length_take, Nat.min_eq_left hk]
    rw [hlength] at hmass
    dsimp only [prefixRecords] at hmass
    constructor <;> omega
  · intro k hk
    have hsplit : records.take (k + 1) = records.take k ++ [records[k]] := by
      simpa using List.take_succ_drop (l := records) (n := k) (stop := 0) (by omega)
    let before := QueueReplay.replay capacity (0, initialQueue) (records.take k)
    have hstep :
        QueueReplay.replay capacity (0, initialQueue) (records.take (k + 1)) =
          QueueReplay.transition capacity before records[k] := by
      rw [hsplit, QueueReplay.replay_append]
      simp [before, QueueReplay.replay]
    rw [hstep]
    exact transition_score_increment_le_capacity capacity before records[k]

/-- The actual selected input in the first collection window has a literal
calendar replay on the preceding physical records and on the pure current
candidate.  The existential initializer and ledger context are the same
actual ones produced by the enabled-history root.  No sender initial queue is
inferred here: numerical queue bounds quantify over an explicit local initial
queue parameter. -/
theorem actual_first_collection_calendar_prefix_replay
    (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∀ (n : Fin W.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice W[n].input = some c →
    let Pn := W.take n.val
    let u := start + w + 1
    let v := u + n.val
    let g := c.preLedger.freezeAt
    let windowChronology := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
      rate source rewards C_star C_h count hcross hspan hshort
    let hbound : u - 1 + n.val ≤ p.T := by
      have htime : W[n].input.time.val + 1 = u + n.val := by
        simpa [u] using (windowChronology n).2
      have hlast := W[n].input.time.isLt
      have hu : 1 ≤ u := by dsimp [u]; omega
      omega
    let indices := CoordinatorCollectionLedger.calendarIndices p.T (u - 1) n.val hbound
    let sequence := prefixDiagnosticSequence rate Pn
    let prefixRows := fun arm => Pn.map fun record =>
      (decide (record.input.time.val + 1 < g),
        if record.input.time.val + 1 < g then
          CoordinatorCollectionLedger.explicitArrival sequence arm record.input.time
        else 0)
    ∃ c0 : ReferenceCollectionSegmentExtraction.Choice rate,
      ∃ initializer : ReferenceCollectionSegmentExtraction.Initializer p,
      c.payload = c0.payload ∧
      c0.initializer = some initializer ∧
      initializer.checkedStart rate = .success c0.preLedger ∧
      CollectionBufferProvenance.collectionContext c.preLedger =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base) ∧
      (∀ time : Fin p.T, c.preLedger.enabledHistory time =
        if u ≤ time.val + 1 ∧ time.val + 1 < v then
          some (decide (time.val + 1 < g)) else none) ∧
      (∀ a time, c.preLedger.rawBuffer a time =
        if c.preLedger.currentRegisters a = none then
          ReferenceFirstCollectionRawCells.physicalRawCell Pn g a time
        else none) ∧
      (∀ record ∈ Pn, ∃ completed,
        ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
        completed.input.round = record.input.time ∧
        completed.input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic record) ∧
      (∀ left ∈ Pn, ∀ right ∈ Pn,
        left.input.time = right.input.time → left = right) ∧
      (∀ a time amount, c.preLedger.rawBuffer a time = some amount →
        u ≤ time.val + 1 ∧ time.val + 1 < v ∧ time.val + 1 < g ∧
          0 < amount ∧ amount ≤ ConstructorDimensions.D p) ∧
      (∀ a, c.preLedger.rawBuffer a W[n].input.time = none) ∧
      ∀ arm, c.preLedger.currentRegisters arm = none →
        (indices = Pn.map (fun record => record.input.time)) ∧
        indices.length = n.val ∧
        (∀ time ∈ indices, ∃ record ∈ Pn,
          record.input.time = time ∧
          ReferenceFirstCollectionRawCells.findPhysicalRecord? Pn time = some record ∧
          sequence time = ReferenceCollectionRawBufferHistory.rawDiagnostic record ∧
          ∃ completed,
            ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
            completed.input.round = record.input.time ∧
            completed.input.raw = sequence time) ∧
        (∀ time ∈ indices,
          c.preLedger.rawBuffer arm time =
            ReferenceFirstCollectionRawCells.physicalRawCell Pn g arm time) ∧
        CoordinatorCollectionLedger.replayRecords? c.preLedger arm indices = some (prefixRows arm) ∧
        (∀ record ∈ prefixRows arm, record.2 ≤ ConstructorDimensions.D p) ∧
        (∀ initialQueue k, k ≤ n.val →
          let endpoint := QueueReplay.replay (4 * rate.n) (0, initialQueue)
            ((prefixRows arm).take k)
          endpoint.1 ≤ initialQueue + k * ConstructorDimensions.D p ∧
            endpoint.2 ≤ initialQueue + k * ConstructorDimensions.D p) ∧
        (∀ initialQueue k, k < n.val →
          (QueueReplay.replay (4 * rate.n) (0, initialQueue)
            ((prefixRows arm).take (k + 1))).1 -
            (QueueReplay.replay (4 * rate.n) (0, initialQueue)
              ((prefixRows arm).take k)).1 ≤ ConstructorDimensions.D p) := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  change ∀ (n : Fin W.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
    ReferenceCollectionSegmentExtraction.choice W[n].input = some c → _
  intro n c hchoice
  let Pn := W.take n.val
  let u := start + w + 1
  let v := u + n.val
  let g := c.preLedger.freezeAt
  let windowChronology := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
    rate source rewards C_star C_h count hcross hspan hshort
  have htimeAll : ∀ i (hi : i < W.length), W[i].input.time.val + 1 = u + i := by
    intro i hi
    have h := windowChronology ⟨i, hi⟩
    simpa [start, execution, firstWindow, w, W, u] using h.2
  have htimeSelected : W[n].input.time.val + 1 = v := by
    have h := htimeAll n.val n.isLt
    simpa [v] using h
  have hbound : u - 1 + n.val ≤ p.T := by
    have hlt := W[n].input.time.isLt
    have htime := htimeSelected
    have hu : 1 ≤ u := by dsimp [u]; omega
    omega
  let indices := CoordinatorCollectionLedger.calendarIndices p.T (u - 1) n.val hbound
  let sequence := prefixDiagnosticSequence rate Pn
  let prefixRows := fun arm => Pn.map fun record =>
    (decide (record.input.time.val + 1 < g),
      if record.input.time.val + 1 < g then
        CoordinatorCollectionLedger.explicitArrival sequence arm record.input.time
      else 0)
  have hchron : ∀ i (hi : i < W.length),
      W[i].input.time.val = (u - 1) + i := by
    intro i hi
    have h := htimeAll i hi
    omega
  have hprefixCalendar : indices = Pn.map fun record => record.input.time := by
    simpa [indices, Pn] using
      calendarIndices_eq_map_take (records := W) (time := fun record => record.input.time)
        (origin := u - 1) (count := n.val) (Nat.le_of_lt n.isLt) hbound hchron
  have hmemPrefixPosition : ∀ record, record ∈ Pn →
      ∃ i, i < n.val ∧ ∃ hiW : i < W.length, W[i]'hiW = record := by
    intro record hmem
    exact mem_take_getElem W n.val hmem
  have huniquePrefix := by
    have hR := ReferenceFirstCollectionRawCells.actual_first_collection_raw_cells
      rate source rewards C_star C_h count hcross hspan hshort n c hchoice
    rcases hR with ⟨_, _, _, _, hunique, _, _⟩
    exact hunique
  have hcontextRoot := ReferenceFirstCollectionEnabledPrefix.actual_first_collection_enabled_history_prefix
    rate source rewards C_star C_h count hcross hspan hshort
  have hcontextSelected := hcontextRoot n c hchoice
  rcases hcontextSelected with ⟨hcontext, hhistory, _, _, henabledCurrent,
      hcandidateHistory⟩
  rcases hcontext with ⟨cut, suffix, registers, owned, base, c0,
      initializer, segment, hrunSplit, _, _, _, _, _, _, _, hinitializerPresent,
      hchecked, _, _, _, _, _, _, _, _, hpayload, hledgerContext, _⟩
  have hrawRoot := ReferenceFirstCollectionRawCells.actual_first_collection_raw_cells
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice
  rcases hrawRoot with ⟨_, hrawBuffer, _, hrecordProvenance, hrawUnique,
    hrawSupport, hrawCurrentEmpty⟩
  have hrawBuffer' : ∀ a time, c.preLedger.rawBuffer a time =
      if c.preLedger.currentRegisters a = none then
        ReferenceFirstCollectionRawCells.physicalRawCell Pn g a time else none := by
    exact hrawBuffer
  have hrawUnique' : ∀ left ∈ Pn, ∀ right ∈ Pn,
      left.input.time = right.input.time → left = right := by
    exact hrawUnique
  have hrecordProvenance' : ∀ record ∈ Pn, ∃ completed,
      ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
      completed.input.round = record.input.time ∧
      completed.input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic record := by
    exact hrecordProvenance
  have hrawSupport' : ∀ a time amount, c.preLedger.rawBuffer a time = some amount →
      u ≤ time.val + 1 ∧ time.val + 1 < v ∧ time.val + 1 < g ∧
        0 < amount ∧ amount ≤ ConstructorDimensions.D p := by
    exact hrawSupport
  have hrawCurrentEmpty' : ∀ a, c.preLedger.rawBuffer a W[n].input.time = none := by
    exact hrawCurrentEmpty
  have hhistory' : ∀ time : Fin p.T, c.preLedger.enabledHistory time =
      if u ≤ time.val + 1 ∧ time.val + 1 < v then
        some (decide (time.val + 1 < g)) else none := by
    exact hhistory
  have hprefixCell (arm : Fin p.K) (hunknown : c.preLedger.currentRegisters arm = none)
      (time : Fin p.T) :
      c.preLedger.rawBuffer arm time =
        ReferenceFirstCollectionRawCells.physicalRawCell Pn g arm time := by
    rw [hrawBuffer' arm time]
    simp [hunknown]
  have hprefixArrival (arm : Fin p.K) (hunknown : c.preLedger.currentRegisters arm = none)
      (time : Fin p.T) :
      CoordinatorCollectionLedger.bufferedArrival c.preLedger arm time =
        CoordinatorCollectionLedger.replayArrival sequence g arm time := by
    rw [CoordinatorCollectionLedger.bufferedArrival, hprefixCell arm hunknown]
    exact physicalRawCell_getD_eq_replayArrival rate Pn g arm time
  have hprefixPosition : ∀ record, record ∈ Pn →
      ∃ i, i < n.val ∧ ∃ hiW : i < W.length, W[i]'hiW = record := hmemPrefixPosition
  have hprefixFindAndDiagnostic : ∀ time ∈ indices, ∃ record ∈ Pn,
      record.input.time = time ∧
      ReferenceFirstCollectionRawCells.findPhysicalRecord? Pn time = some record ∧
      sequence time = ReferenceCollectionRawBufferHistory.rawDiagnostic record ∧
      ∃ completed,
        ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
        completed.input.round = record.input.time ∧ completed.input.raw = sequence time := by
    intro time hmem
    rw [hprefixCalendar] at hmem
    obtain ⟨record, hrecord, htime⟩ := List.mem_map.mp hmem
    have hfind := findPhysicalRecord_eq_some_of_unique rate Pn time record hrecord htime hrawUnique'
    have hsequence := prefixDiagnosticSequence_eq_of_find rate Pn time record hfind
    obtain ⟨completed, hextract, hround, hraw⟩ := hrecordProvenance' record hrecord
    refine ⟨record, hrecord, htime, hfind, hsequence, completed, hextract, hround, ?_⟩
    calc
      completed.input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic record := hraw
      _ = prefixDiagnosticSequence rate Pn time := hsequence.symm
      _ = sequence time := rfl
  have hprefixEnable : ∀ time ∈ indices,
      c.preLedger.enabledHistory time = some (decide (time.val + 1 < g)) := by
    intro time hmem
    obtain ⟨record, hrecord, htime, _, _, _⟩ := hprefixFindAndDiagnostic time hmem
    obtain ⟨i, hi, hiW, hget⟩ := hprefixPosition record hrecord
    have htime' := htimeAll i hiW
    rw [hget] at htime'
    have hinterval : u ≤ time.val + 1 ∧ time.val + 1 < v := by
      rw [← htime]
      dsimp [v]
      omega
    rw [hhistory' time, if_pos hinterval]
  have hprefixLength : indices.length = n.val := by
    rw [hprefixCalendar]
    simp [Pn]
  have hcapacity : 4 * rate.n ≤ ConstructorDimensions.D p :=
    ActiveFollowerDownAcceptance.four_n_le_D p rate
  refine ⟨c0, initializer, hpayload, hinitializerPresent, hchecked, hledgerContext,
    hhistory', hrawBuffer',
    hrecordProvenance', hrawUnique', hrawSupport', hrawCurrentEmpty', ?_⟩
  intro arm hunknown
  let actualPrefixRows := Pn.map fun record =>
      (decide (record.input.time.val + 1 < g),
        if record.input.time.val + 1 < g then
          CoordinatorCollectionLedger.explicitArrival sequence arm record.input.time
        else 0)
  have hprefixArrivalFields : ∀ record ∈ Pn,
      (if record.input.time.val + 1 < g then
        CoordinatorCollectionLedger.explicitArrival sequence arm record.input.time
       else 0) ≤ ConstructorDimensions.D p := by
    intro record hrecord
    have hfind := findPhysicalRecord_eq_some_of_unique rate Pn record.input.time
      record hrecord rfl hrawUnique'
    have hsequence := prefixDiagnosticSequence_eq_of_find rate Pn record.input.time record hfind
    have hsequence' : sequence record.input.time =
        ReferenceCollectionRawBufferHistory.rawDiagnostic record := by
      simpa [sequence] using hsequence
    by_cases hbefore : record.input.time.val + 1 < g
    · rw [if_pos hbefore]
      unfold CoordinatorCollectionLedger.explicitArrival
      rw [hsequence']
      cases hdiag : ReferenceCollectionRawBufferHistory.rawDiagnostic record with
      | none => exact Nat.zero_le _
      | some pair =>
          rcases pair with ⟨recordedArm, amount⟩
          by_cases harm : recordedArm = arm
          · simpa [harm] using rawDiagnostic_amount_le_D rate record recordedArm amount hdiag
          · simp [harm]
    · simp [hbefore]
  have hprefixRowsBound :
      ∀ row ∈ actualPrefixRows, row.2 ≤ ConstructorDimensions.D p := by
    intro row hrow
    rcases List.mem_map.mp hrow with ⟨record, hrecord, hrowEq⟩
    rw [← hrowEq]
    exact hprefixArrivalFields record hrecord
  have hprefixDirect := CoordinatorCollectionLedger.replayRecords?_equals_directRecords
    c.preLedger arm sequence (fun time => decide (time.val + 1 < g)) indices
    hprefixEnable (fun time hmem => hprefixArrival arm hunknown time)
  have hprefixDirectRows :
      CoordinatorCollectionLedger.directRecords sequence
        (fun time => decide (time.val + 1 < g)) g arm indices = actualPrefixRows := by
    rw [hprefixCalendar]
    unfold CoordinatorCollectionLedger.directRecords
    simp only [List.map_map, Function.comp_apply]
    apply List.map_congr_left
    intro record hrecord
    simp [actualPrefixRows, CoordinatorCollectionLedger.replayArrival,
      CoordinatorCollectionLedger.explicitArrival, CoordinatorCollectionLedger.sourceRound]
    constructor
    · intro hbefore
      simp [hbefore]
    · rfl
  have hprefixReplay :
      CoordinatorCollectionLedger.replayRecords? c.preLedger arm indices =
        some actualPrefixRows := by
    rw [hprefixDirectRows] at hprefixDirect
    exact hprefixDirect
  have hprefixRowsEq : actualPrefixRows = prefixRows arm := rfl
  have hprefixReplay' :
      CoordinatorCollectionLedger.replayRecords? c.preLedger arm indices =
        some (prefixRows arm) := by
    rw [← hprefixRowsEq]
    exact hprefixReplay
  have hprefixRowsBound' :
      ∀ row ∈ prefixRows arm, row.2 ≤ ConstructorDimensions.D p := by
    rw [← hprefixRowsEq]
    exact hprefixRowsBound
  have hprefixNumerical : ∀ initialQueue,
      (∀ k, k ≤ actualPrefixRows.length →
        let endpoint := QueueReplay.replay (4 * rate.n) (0, initialQueue)
          (actualPrefixRows.take k)
        endpoint.1 ≤ initialQueue + k * ConstructorDimensions.D p ∧
          endpoint.2 ≤ initialQueue + k * ConstructorDimensions.D p) ∧
      (∀ k, k < actualPrefixRows.length →
        (QueueReplay.replay (4 * rate.n) (0, initialQueue)
          (actualPrefixRows.take (k + 1))).1 -
          (QueueReplay.replay (4 * rate.n) (0, initialQueue)
            (actualPrefixRows.take k)).1 ≤ 4 * rate.n) := by
    intro initialQueue
    exact replay_prefix_bounds (4 * rate.n) (ConstructorDimensions.D p)
      initialQueue actualPrefixRows hprefixRowsBound
  have hprefixRowsLength : actualPrefixRows.length = n.val := by
    simp [actualPrefixRows, Pn, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt n.isLt)]
  refine ⟨hprefixCalendar, hprefixLength, hprefixFindAndDiagnostic,
    ?_, hprefixReplay', hprefixRowsBound', ?_, ?_⟩
  · intro time hmem
    exact hprefixCell arm hunknown time
  · intro initialQueue k hk
    obtain ⟨hscore, hqueue⟩ := (hprefixNumerical initialQueue).1 k (by
      rw [hprefixRowsLength]
      exact hk)
    exact ⟨hscore, hqueue⟩
  · intro initialQueue k hk
    have hservice := (hprefixNumerical initialQueue).2 k (by
      rw [hprefixRowsLength]
      exact hk)
    exact le_trans hservice hcapacity

/-- The pure current stage-one candidate keeps an unknown register unknown,
and its complete Boolean history includes the strict freeze test at the current
record. This is a candidate-state statement only. -/
theorem actual_first_collection_calendar_candidate_history
    (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∀ (n : Fin W.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice W[n].input = some c →
    let u := start + w + 1
    let v := u + n.val
    let g := c.preLedger.freezeAt
    let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger
      W[n].input.time
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger W[n].input.time)
      (ReferenceCollectionRawBufferHistory.rawDiagnostic W[n])
    ∀ arm, c.preLedger.currentRegisters arm = none →
      (∀ time : Fin p.T, candidate.enabledHistory time =
        if u ≤ time.val + 1 ∧ time.val + 1 < v + 1 then
          some (decide (time.val + 1 < g)) else none) ∧
      candidate.currentRegisters arm = none ∧
      ReferenceActivePhysicalStep.collectionEnabled c.preLedger W[n].input.time =
        decide (v < g) := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  change ∀ (n : Fin W.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
    ReferenceCollectionSegmentExtraction.choice W[n].input = some c → _
  intro n c hchoice
  let u := start + w + 1
  let v := u + n.val
  let g := c.preLedger.freezeAt
  let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger
    W[n].input.time
    (ReferenceActivePhysicalStep.collectionEnabled c.preLedger W[n].input.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic W[n])
  have hE := ReferenceFirstCollectionEnabledPrefix.actual_first_collection_enabled_history_prefix
    rate source rewards C_star C_h count hcross hspan hshort
  have hselected := hE n c hchoice
  rcases hselected with ⟨_, _, _, _, hcurrentEnabled, hcandidateHistory⟩
  have hhistory : ∀ time : Fin p.T, candidate.enabledHistory time =
      if u ≤ time.val + 1 ∧ time.val + 1 < v + 1 then
        some (decide (time.val + 1 < g)) else none := by
    intro time
    have h := hcandidateHistory
      (ReferenceCollectionRawBufferHistory.rawDiagnostic W[n]) time
    simpa [u, v, g, candidate] using h
  change ∀ arm, c.preLedger.currentRegisters arm = none → _
  intro arm hunknown
  refine ⟨hhistory, ?_, ?_⟩
  · simp [candidate, CoordinatorCollectionLedger.startRoundCandidate, hunknown]
  · simpa [u, v, g] using hcurrentEnabled

private theorem findPhysicalRecord_eq_some_of_append_prefix
    (rate : RateInput p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (current : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (time : Fin p.T)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : record ∈ records) (htime : record.input.time = time)
    (hunique : ∀ left ∈ records, ∀ right ∈ records,
      left.input.time = right.input.time → left = right)
    (hnoCurrent : ∀ row ∈ records, row.input.time ≠ current.input.time) :
    ReferenceFirstCollectionRawCells.findPhysicalRecord? (records ++ [current]) time =
      some record := by
  induction records with
  | nil => simp at hmem
  | cons head tail ih =>
      rcases List.mem_cons.mp hmem with heq | htail
      · subst record
        simp [ReferenceFirstCollectionRawCells.findPhysicalRecord?, htime]
      · have htailUnique : ∀ left ∈ tail, ∀ right ∈ tail,
            left.input.time = right.input.time → left = right := by
          intro left hleft right hright htimes
          exact hunique left (List.mem_cons_of_mem head hleft)
            right (List.mem_cons_of_mem head hright) htimes
        have htailNoCurrent : ∀ row ∈ tail, row.input.time ≠ current.input.time := by
          intro row hrow
          exact hnoCurrent row (List.mem_cons_of_mem head hrow)
        by_cases hhead : head.input.time = time
        · have heq : head = record :=
            hunique head (by simp) record (by simp [htail]) (hhead.trans htime.symm)
          subst record
          simp [ReferenceFirstCollectionRawCells.findPhysicalRecord?, hhead]
        · change List.find? (fun row => decide (row.input.time = time))
            (head :: (tail ++ [current])) = some record
          rw [List.find?_cons]
          have hpred : decide (head.input.time = time) = false := by simp [hhead]
          rw [hpred]
          change ReferenceFirstCollectionRawCells.findPhysicalRecord? (tail ++ [current])
            time = some record
          exact ih htail htailUnique htailNoCurrent

private theorem findPhysicalRecord_eq_some_of_append_last
    (rate : RateInput p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (current : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hnoCurrent : ∀ row ∈ records, row.input.time ≠ current.input.time) :
    ReferenceFirstCollectionRawCells.findPhysicalRecord? (records ++ [current])
      current.input.time = some current := by
  induction records with
  | nil => simp [ReferenceFirstCollectionRawCells.findPhysicalRecord?]
  | cons head tail ih =>
      have hhead := hnoCurrent head (by simp)
      have htail : ∀ row ∈ tail, row.input.time ≠ current.input.time := by
        intro row hrow
        exact hnoCurrent row (List.mem_cons_of_mem head hrow)
      change List.find? (fun row => decide (row.input.time = current.input.time))
        (head :: (tail ++ [current])) = some current
      rw [List.find?_cons]
      have hpred : decide (head.input.time = current.input.time) = false := by
        simp [hhead]
      rw [hpred]
      change ReferenceFirstCollectionRawCells.findPhysicalRecord? (tail ++ [current])
        current.input.time = some current
      exact ih htail

private theorem findPhysicalRecord_append_of_ne
    (rate : RateInput p)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (current : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (time : Fin p.T) (hnot : time ≠ current.input.time) :
    ReferenceFirstCollectionRawCells.findPhysicalRecord? (records ++ [current]) time =
      ReferenceFirstCollectionRawCells.findPhysicalRecord? records time := by
  induction records with
  | nil => simp [ReferenceFirstCollectionRawCells.findPhysicalRecord?, hnot.symm]
  | cons head tail ih =>
      change List.find? (fun row => decide (row.input.time = time))
        (head :: (tail ++ [current])) =
        List.find? (fun row => decide (row.input.time = time)) (head :: tail)
      rw [List.find?_cons, List.find?_cons]
      by_cases hhead : head.input.time = time
      · simp [hhead]
      · have hpred : decide (head.input.time = time) = false := by simp [hhead]
        rw [hpred]
        exact ih

/-- Calendar bound for the selected next physical record, derived from the
actual first-collection chronology. -/
theorem first_collection_current_end_bound
    (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∀ n : Fin W.length, start + w + 1 - 1 + (n.val + 1) ≤ p.T := by
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  change ∀ n : Fin W.length, start + w + 1 - 1 + (n.val + 1) ≤ p.T
  intro n
  have htime :=
    (ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
      rate source rewards C_star C_h count hcross hspan hshort n).2
  have htime' : W[n].input.time.val + 1 = start + w + 1 + n.val := by
    simpa [start, execution, firstWindow, w, W] using htime
  have hlast := W[n].input.time.isLt
  have hu : 1 ≤ start + w + 1 := by omega
  omega

/-- The current candidate's calendar is the chronological list consisting of
the complete physical prefix followed by the selected current record. -/
theorem actual_first_collection_calendar_candidate_calendar
    (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∀ (n : Fin W.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice W[n].input = some c →
    let Pn := W.take n.val
    let u := start + w + 1
    let v := u + n.val
    let g := c.preLedger.freezeAt
    let longer := Pn ++ [W[n]]
    let hlongerBound : u - 1 + (n.val + 1) ≤ p.T :=
      first_collection_current_end_bound rate source rewards C_star C_h count
        hcross hspan hshort n
    let longerIndices :=
      CoordinatorCollectionLedger.calendarIndices p.T (u - 1) (n.val + 1) hlongerBound
    longerIndices = longer.map (fun record => record.input.time) ∧
    longerIndices.length = n.val + 1 := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  change ∀ (n : Fin W.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
    ReferenceCollectionSegmentExtraction.choice W[n].input = some c → _
  intro n c hchoice
  let Pn := W.take n.val
  let u := start + w + 1
  let v := u + n.val
  let g := c.preLedger.freezeAt
  let longer := Pn ++ [W[n]]
  let hlongerBound : u - 1 + (n.val + 1) ≤ p.T :=
    first_collection_current_end_bound rate source rewards C_star C_h count
      hcross hspan hshort n
  let longerIndices :=
    CoordinatorCollectionLedger.calendarIndices p.T (u - 1) (n.val + 1) hlongerBound
  have htimeAll : ∀ i (hi : i < W.length), W[i].input.time.val + 1 = u + i := by
    intro i hi
    have h := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
      rate source rewards C_star C_h count hcross hspan hshort ⟨i, hi⟩
    simpa [start, execution, firstWindow, w, W, u] using h.2
  have htimeSelected : W[n].input.time.val + 1 = v := by
    have h := htimeAll n.val n.isLt
    simpa [v] using h
  have hchron : ∀ i (hi : i < W.length),
      W[i].input.time.val = (u - 1) + i := by
    intro i hi
    have h := htimeAll i hi
    omega
  have htakeAppend : W.take (n.val + 1) = longer := by
    simpa [longer, Pn] using
      (List.take_succ_drop (l := W) (n := n.val) (stop := 0) (by omega))
  have hlongerCalendar : longerIndices = longer.map (fun record => record.input.time) := by
    have h := calendarIndices_eq_map_take (records := W)
      (time := fun record => record.input.time) (origin := u - 1)
      (count := n.val + 1) (by omega) hlongerBound hchron
    simpa [longer, longerIndices, htakeAppend] using h
  have hlongerLength : longerIndices.length = n.val + 1 := by
    rw [hlongerCalendar]
    simp [longer, Pn]
  exact ⟨hlongerCalendar, hlongerLength⟩

private theorem first_collection_prefix_time_ne_selected
    (rate : RateInput p)
    (W : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (n : Fin W.length) (origin : ℕ)
    (htime : ∀ i (hi : i < W.length), W[i].input.time.val + 1 = origin + 1 + i)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ W.take n.val) :
    record.input.time ≠ W[n].input.time := by
  obtain ⟨i, hi, hiW, hget⟩ := mem_take_getElem W n.val hrecord
  have hprefix := htime i hiW
  rw [hget] at hprefix
  have hselected := htime n.val n.isLt
  intro heq
  have hval := congrArg Fin.val heq
  have hindices : i = n.val := by
    have htimeEq : origin + 1 + i = origin + 1 + n.val := by
      calc
        origin + 1 + i = record.input.time.val + 1 := hprefix.symm
        _ = W[n].input.time.val + 1 := by rw [hval]
        _ = origin + 1 + n.val := hselected
    omega
  omega

/-- The pure current candidate keeps an unknown arm unknown and its cells
agree with the actual lookup over the full physical prefix plus the selected
current record. The current record is included without asserting successful
recording, reception, or finish. -/
theorem actual_first_collection_calendar_candidate_raw_cells
    (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∀ (n : Fin W.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice W[n].input = some c →
    let Pn := W.take n.val
    let g := c.preLedger.freezeAt
    let longer := Pn ++ [W[n]]
    let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger
      W[n].input.time
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger W[n].input.time)
      (ReferenceCollectionRawBufferHistory.rawDiagnostic W[n])
    ∀ arm, c.preLedger.currentRegisters arm = none →
      candidate.currentRegisters arm = none ∧
      ∀ time, candidate.rawBuffer arm time =
        ReferenceFirstCollectionRawCells.physicalRawCell longer g arm time := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  change ∀ (n : Fin W.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
    ReferenceCollectionSegmentExtraction.choice W[n].input = some c → _
  intro n c hchoice
  let Pn := W.take n.val
  let g := c.preLedger.freezeAt
  let current := W[n]
  let longer := Pn ++ [current]
  let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger
    current.input.time
    (ReferenceActivePhysicalStep.collectionEnabled c.preLedger current.input.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic current)
  have htimeAll : ∀ i (hi : i < W.length), W[i].input.time.val + 1 = start + w + 1 + i := by
    intro i hi
    have h := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
      rate source rewards C_star C_h count hcross hspan hshort ⟨i, hi⟩
    simpa [start, execution, firstWindow, w, W] using h.2
  have hnoCurrent : ∀ record ∈ Pn, record.input.time ≠ current.input.time := by
    intro record hrecord
    exact first_collection_prefix_time_ne_selected rate W n (start + w) htimeAll
      record (by simpa [Pn] using hrecord)
  have hrawRoot := ReferenceFirstCollectionRawCells.actual_first_collection_raw_cells
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice
  rcases hrawRoot with ⟨_, hrawBuffer, _, _, hunique, _, hcurrentEmpty⟩
  have hrawUnique : ∀ left ∈ Pn, ∀ right ∈ Pn,
      left.input.time = right.input.time → left = right := hunique
  have hlongerUnique := time_unique_append_singleton Pn current
    (fun record => record.input.time) hrawUnique hnoCurrent
  have hunknownCell (arm : Fin p.K)
      (hunknown : c.preLedger.currentRegisters arm = none) (time : Fin p.T) :
      candidate.rawBuffer arm time =
        ReferenceFirstCollectionRawCells.physicalRawCell longer g arm time := by
    by_cases hcurrentTime : time = current.input.time
    · subst time
      have hinsert := CollectionBufferProvenance.startRoundCandidate_unknown_raw_buffer_cell
        c.preLedger current.input.time
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger current.input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic current) arm hunknown
      rw [show current = W[n] by rfl] at hinsert
      rw [hcurrentEmpty arm] at hinsert
      have hinsert' : candidate.rawBuffer arm current.input.time =
          match ReferenceCollectionRawBufferHistory.rawDiagnostic current with
          | none => none
          | some (b, amount) =>
              if b = arm ∧ 0 < amount ∧
                  CoordinatorCollectionLedger.sourceRound current.input.time < g then
                some amount else none := by
        change (CoordinatorCollectionLedger.startRoundCandidate c.preLedger
          current.input.time
          (ReferenceActivePhysicalStep.collectionEnabled c.preLedger current.input.time)
          (ReferenceCollectionRawBufferHistory.rawDiagnostic current)).rawBuffer arm
            current.input.time = _
        exact hinsert
      have hfind := findPhysicalRecord_eq_some_of_append_last rate Pn current hnoCurrent
      have hfind' : ReferenceFirstCollectionRawCells.findPhysicalRecord? longer
          current.input.time = some current := by
        simpa [longer] using hfind
      change candidate.rawBuffer arm current.input.time = _
      unfold ReferenceFirstCollectionRawCells.physicalRawCell
      rw [hfind']
      change candidate.rawBuffer arm current.input.time =
        (match ReferenceCollectionRawBufferHistory.rawDiagnostic current with
        | none => none
        | some (b, amount) =>
            if b = arm ∧ 0 < amount ∧
                CoordinatorCollectionLedger.sourceRound current.input.time < g then
              some amount else none)
      exact hinsert'
    · have hcandidateAway := startRoundCandidate_buffer_other_round rate c.preLedger
        current.input.time
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger current.input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic current) arm time
        hcurrentTime
      rw [hcandidateAway]
      rw [hrawBuffer arm time, if_pos hunknown]
      have hfindLonger := findPhysicalRecord_append_of_ne rate Pn current time
        hcurrentTime
      unfold ReferenceFirstCollectionRawCells.physicalRawCell
      rw [hfindLonger]
  change ∀ arm, c.preLedger.currentRegisters arm = none → _
  intro arm hunknown
  constructor
  · simp [candidate, CoordinatorCollectionLedger.startRoundCandidate, hunknown]
  · intro time
    exact hunknownCell arm hunknown time

/-- The pure current stage-one candidate replays every calendar row in the
physical prefix followed by the selected record. The output retains every
row, with the strict pre-freeze bit and zero arrival on disabled rows. Queue
bounds use an explicit local initial queue and do not assert a sender field. -/
theorem actual_first_collection_calendar_candidate_replay
    (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∀ (n : Fin W.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
      ReferenceCollectionSegmentExtraction.choice W[n].input = some c →
    let Pn := W.take n.val
    let u := start + w + 1
    let v := u + n.val
    let g := c.preLedger.freezeAt
    let longer := Pn ++ [W[n]]
    let hlongerBound : u - 1 + (n.val + 1) ≤ p.T :=
      first_collection_current_end_bound rate source rewards C_star C_h count
        hcross hspan hshort n
    let longerIndices :=
      CoordinatorCollectionLedger.calendarIndices p.T (u - 1) (n.val + 1) hlongerBound
    let sequence := prefixDiagnosticSequence rate longer
    let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger
      W[n].input.time
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger W[n].input.time)
      (ReferenceCollectionRawBufferHistory.rawDiagnostic W[n])
    let candidateRows := fun (arm : Fin p.K) => longer.map fun record =>
      (decide (record.input.time.val + 1 < g),
        if record.input.time.val + 1 < g then
          CoordinatorCollectionLedger.explicitArrival sequence arm record.input.time
        else 0)
    ∀ arm, c.preLedger.currentRegisters arm = none →
      candidate.currentRegisters arm = none ∧
      (∀ time, candidate.rawBuffer arm time =
        ReferenceFirstCollectionRawCells.physicalRawCell longer g arm time) ∧
      longerIndices = longer.map (fun record => record.input.time) ∧
      longerIndices.length = n.val + 1 ∧
      CoordinatorCollectionLedger.replayRecords? candidate arm longerIndices =
        some (candidateRows arm) ∧
      (∀ row, row ∈ candidateRows arm → row.2 ≤ ConstructorDimensions.D p) ∧
      (∀ initialQueue k, k ≤ n.val + 1 →
        let endpoint := QueueReplay.replay (4 * rate.n) (0, initialQueue)
          ((candidateRows arm).take k)
        endpoint.1 ≤ initialQueue + k * ConstructorDimensions.D p ∧
          endpoint.2 ≤ initialQueue + k * ConstructorDimensions.D p) ∧
      (∀ initialQueue k, k < n.val + 1 →
        (QueueReplay.replay (4 * rate.n) (0, initialQueue)
          ((candidateRows arm).take (k + 1))).1 -
          (QueueReplay.replay (4 * rate.n) (0, initialQueue)
            ((candidateRows arm).take k)).1 ≤ ConstructorDimensions.D p) := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let W := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  change ∀ (n : Fin W.length) (c : ReferenceCollectionSegmentExtraction.Choice rate),
    ReferenceCollectionSegmentExtraction.choice W[n].input = some c → _
  intro n c hchoice
  let Pn := W.take n.val
  let u := start + w + 1
  let v := u + n.val
  let g := c.preLedger.freezeAt
  let current := W[n]
  let longer := Pn ++ [current]
  let hlongerBound : u - 1 + (n.val + 1) ≤ p.T :=
    first_collection_current_end_bound rate source rewards C_star C_h count
      hcross hspan hshort n
  let longerIndices :=
    CoordinatorCollectionLedger.calendarIndices p.T (u - 1) (n.val + 1) hlongerBound
  let sequence := prefixDiagnosticSequence rate longer
  let candidate := CoordinatorCollectionLedger.startRoundCandidate c.preLedger
    current.input.time
    (ReferenceActivePhysicalStep.collectionEnabled c.preLedger current.input.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic current)
  let candidateRows : Fin p.K → List (Bool × ℕ) := fun chosenArm =>
    longer.map fun record =>
      (decide (record.input.time.val + 1 < g),
        if record.input.time.val + 1 < g then
          CoordinatorCollectionLedger.explicitArrival sequence chosenArm record.input.time
        else 0)
  have hcalendarResult := actual_first_collection_calendar_candidate_calendar
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice
  have hcalendar : longerIndices = longer.map (fun record => record.input.time) ∧
      longerIndices.length = n.val + 1 := by
    simpa [start, execution, firstWindow, w, W, Pn, u, v, g, current,
      longer, hlongerBound, longerIndices] using hcalendarResult
  rcases hcalendar with ⟨hindices, hindicesLength⟩
  have hrawCandidateResult := actual_first_collection_calendar_candidate_raw_cells
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice
  have hhistoryResult := actual_first_collection_calendar_candidate_history
    rate source rewards C_star C_h count hcross hspan hshort n c hchoice
  have htimeAll : ∀ i (hi : i < W.length), W[i].input.time.val + 1 = u + i := by
    intro i hi
    have h := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
      rate source rewards C_star C_h count hcross hspan hshort ⟨i, hi⟩
    simpa [start, execution, firstWindow, w, W, u] using h.2
  have hrowInterval : ∀ record ∈ longer,
      u ≤ record.input.time.val + 1 ∧ record.input.time.val + 1 < v + 1 := by
    intro record hrecord
    rcases List.mem_append.mp hrecord with hprefix | hlast
    · obtain ⟨i, hi, hiW, hget⟩ := mem_take_getElem W n.val hprefix
      have htime := htimeAll i hiW
      rw [hget] at htime
      dsimp [u, v]
      omega
    · have hcurrent : record = current := List.mem_singleton.mp hlast
      subst record
      have htime := htimeAll n.val n.isLt
      have htimeCurrent : current.input.time.val + 1 = start + w + 1 + n.val := by
        simpa [current, u] using htime
      constructor <;> dsimp [u, v] <;> omega
  have huniquePrefix : ∀ left ∈ Pn, ∀ right ∈ Pn,
      left.input.time = right.input.time → left = right := by
    have hroot := ReferenceFirstCollectionRawCells.actual_first_collection_raw_cells
      rate source rewards C_star C_h count hcross hspan hshort n c hchoice
    rcases hroot with ⟨_, _, _, _, hunique, _, _⟩
    exact hunique
  have hnoCurrent : ∀ record ∈ Pn, record.input.time ≠ current.input.time := by
    intro record hrecord
    exact first_collection_prefix_time_ne_selected rate W n (start + w) htimeAll
      record (by simpa [Pn] using hrecord)
  have huniqueLonger := time_unique_append_singleton Pn current
    (fun record => record.input.time) huniquePrefix hnoCurrent
  have hrowFind : ∀ record ∈ longer,
      ReferenceFirstCollectionRawCells.findPhysicalRecord? longer record.input.time =
        some record := by
    intro record hrecord
    rcases List.mem_append.mp hrecord with hprefix | hlast
    · exact findPhysicalRecord_eq_some_of_append_prefix rate Pn current
        record.input.time record hprefix rfl huniquePrefix hnoCurrent
    · have hcurrent : record = current := List.mem_singleton.mp hlast
      subst record
      exact findPhysicalRecord_eq_some_of_append_last rate Pn current hnoCurrent
  have hrowSequence : ∀ record ∈ longer,
      sequence record.input.time =
        ReferenceCollectionRawBufferHistory.rawDiagnostic record := by
    intro record hrecord
    exact prefixDiagnosticSequence_eq_of_find rate longer record.input.time record
      (hrowFind record hrecord)
  have hrowArrivalBound : ∀ (chosenArm : Fin p.K)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      record ∈ longer →
      (if record.input.time.val + 1 < g then
        CoordinatorCollectionLedger.explicitArrival sequence chosenArm record.input.time
       else 0) ≤ ConstructorDimensions.D p := by
    intro arm record hrecord
    have hsequence := hrowSequence record hrecord
    by_cases hbefore : record.input.time.val + 1 < g
    · rw [if_pos hbefore]
      unfold CoordinatorCollectionLedger.explicitArrival
      rw [hsequence]
      cases hdiag : ReferenceCollectionRawBufferHistory.rawDiagnostic record with
      | none => exact Nat.zero_le _
      | some pair =>
          rcases pair with ⟨recordedArm, amount⟩
          by_cases harm : recordedArm = arm
          · simpa [harm] using
              rawDiagnostic_amount_le_D rate record recordedArm amount hdiag
          · simp [harm]
    · simp [hbefore]
  have hrowsBound : ∀ (chosenArm : Fin p.K)
      (row : Bool × ℕ), row ∈ candidateRows chosenArm →
      row.2 ≤ ConstructorDimensions.D p := by
    intro chosenArm row hrow
    rcases List.mem_map.mp (by simpa [candidateRows] using hrow) with
      ⟨record, hrecord, hrowEq⟩
    rw [← hrowEq]
    exact hrowArrivalBound chosenArm record hrecord
  have hrowsLength : ∀ arm, (candidateRows arm).length = n.val + 1 := by
    intro chosenArm
    have hlongerLength : longer.length = n.val + 1 := by
      calc
        longer.length = (longer.map (fun record => record.input.time)).length := by simp
        _ = longerIndices.length := by rw [← hindices]
        _ = n.val + 1 := hindicesLength
    simpa [candidateRows] using hlongerLength
  have hcandidateCell : ∀ arm (hunknown : c.preLedger.currentRegisters arm = none)
      (time : Fin p.T),
      candidate.rawBuffer arm time =
        ReferenceFirstCollectionRawCells.physicalRawCell longer g arm time := by
    intro arm hunknown time
    exact (hrawCandidateResult arm hunknown).2 time
  have hcandidateHistory : ∀ arm (hunknown : c.preLedger.currentRegisters arm = none)
      (time : Fin p.T),
      candidate.enabledHistory time =
        if u ≤ time.val + 1 ∧ time.val + 1 < v + 1 then
          some (decide (time.val + 1 < g)) else none := by
    intro arm hunknown time
    exact (hhistoryResult arm hunknown).1 time
  have hcapacity : 4 * rate.n ≤ ConstructorDimensions.D p :=
    ActiveFollowerDownAcceptance.four_n_le_D p rate
  refine fun (chosenArm : Fin p.K)
      (hunknown : c.preLedger.currentRegisters chosenArm = none) => ?_
  let rows := candidateRows chosenArm
  have hcandidateUnknown : candidate.currentRegisters chosenArm = none :=
    (hrawCandidateResult chosenArm hunknown).1
  have henabled : ∀ time ∈ longerIndices,
      candidate.enabledHistory time = some (decide (time.val + 1 < g)) := by
    intro time htime
    rw [hindices] at htime
    obtain ⟨record, hrecord, htimeEq⟩ := List.mem_map.mp htime
    have hinterval := hrowInterval record hrecord
    have hintervalTime : u ≤ time.val + 1 ∧ time.val + 1 < v + 1 := by
      have hval := congrArg Fin.val htimeEq
      constructor <;> omega
    rw [hcandidateHistory chosenArm hunknown time, if_pos hintervalTime]
  have harrival : ∀ time ∈ longerIndices,
      CoordinatorCollectionLedger.bufferedArrival candidate chosenArm time =
        CoordinatorCollectionLedger.replayArrival sequence g chosenArm time := by
    intro time htime
    rw [CoordinatorCollectionLedger.bufferedArrival,
      hcandidateCell chosenArm hunknown time]
    exact physicalRawCell_getD_eq_replayArrival rate longer g chosenArm time
  have hdirect := CoordinatorCollectionLedger.replayRecords?_equals_directRecords
    candidate chosenArm sequence (fun time => decide (time.val + 1 < g)) longerIndices
    henabled harrival
  have hdirectRows : CoordinatorCollectionLedger.directRecords sequence
      (fun time => decide (time.val + 1 < g)) g chosenArm longerIndices = rows := by
    rw [hindices]
    unfold CoordinatorCollectionLedger.directRecords
    simp only [List.map_map, Function.comp_apply]
    apply List.map_congr_left
    intro record hrecord
    simp [rows, candidateRows, CoordinatorCollectionLedger.replayArrival,
      CoordinatorCollectionLedger.explicitArrival, CoordinatorCollectionLedger.sourceRound]
    constructor
    · intro hbefore
      simp [hbefore]
    · rfl
  have hreplay : CoordinatorCollectionLedger.replayRecords? candidate chosenArm longerIndices =
      some rows := by
    have hdirect' := hdirect
    change CoordinatorCollectionLedger.replayRecords? candidate chosenArm longerIndices =
      some (CoordinatorCollectionLedger.directRecords sequence
        (fun time => decide (time.val + 1 < g)) g chosenArm longerIndices) at hdirect'
    rw [hdirectRows] at hdirect'
    exact hdirect'
  have hnumerical : ∀ initialQueue,
      (∀ k, k ≤ rows.length →
        let endpoint := QueueReplay.replay (4 * rate.n) (0, initialQueue)
          (rows.take k)
        endpoint.1 ≤ initialQueue + k * ConstructorDimensions.D p ∧
          endpoint.2 ≤ initialQueue + k * ConstructorDimensions.D p) ∧
      (∀ k, k < rows.length →
        (QueueReplay.replay (4 * rate.n) (0, initialQueue)
          (rows.take (k + 1))).1 -
          (QueueReplay.replay (4 * rate.n) (0, initialQueue)
            (rows.take k)).1 ≤ 4 * rate.n) := by
    intro initialQueue
    exact replay_prefix_bounds (4 * rate.n) (ConstructorDimensions.D p)
      initialQueue rows (hrowsBound chosenArm)
  refine ⟨hcandidateUnknown, ?_, hindices, hindicesLength, hreplay,
    hrowsBound chosenArm,
    ?_, ?_⟩
  · exact fun time => hcandidateCell chosenArm hunknown time
  · intro initialQueue k hk
    obtain ⟨hscore, hqueue⟩ := (hnumerical initialQueue).1 k (by
      rw [hrowsLength chosenArm]
      exact hk)
    exact ⟨hscore, hqueue⟩
  · intro initialQueue k hk
    have hservice := (hnumerical initialQueue).2 k (by
      rw [hrowsLength chosenArm]
      exact hk)
    exact le_trans hservice hcapacity

end Bandits.Support.ReferenceFirstCollectionCalendarReplay

end
