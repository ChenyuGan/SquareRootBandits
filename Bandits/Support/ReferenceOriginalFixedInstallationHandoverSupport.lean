/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalStoppedTransferPhaseIntervals
public import Bandits.Support.ReferencePostReplacementCollectionHandoverWaitingCost

import Mathlib.Tactic

open MeasureTheory

/-!
# Fixed-calendar H support for an actual original installation

This module projects one actual installation date on the original physical
run. The initial `.first` branch uses the accepted initial raw window. A later
birth uses the actual empty-collection record and that record's own
continuing H segment. The first-bad mask retains its detecting update.

Sources: ZIP4 `05_binary_transport.tex:244-289`, `06_interruptions.tex:431-490,493-533`, and
`appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceActivePhysicalStep
open scoped Classical

namespace Bandits.Support.ReferenceOriginalFixedInstallationHandoverSupport

open ReferenceOriginalInitialTransferWindowGeometry
open ReferencePostReplacementCollectionHandoverDecoderCorrespondence
open ReferenceCompleteLaterLiveComplementPrefixReplay
open ReferenceCompleteLaterInstallationChoiceHistory
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix sourcePrefixFiltration)
open ReferenceActivePhysicalStepMeasurability (encodeCoordinator encodeState encodeLive CoordinatorCode StateCode LiveDiscrete)
open ReferenceCollectionOutcomeMeasurability (optionalElim measurable_optionalElim)
open ReferenceFirstReplacementCollectionPredictableStages (preRoundStart preRoundStart_factor preRoundStart_measurable preRoundStart_actual_choice)
open ReferenceAssignmentPayloadPersistence (InstallationBirth storedPayload)
open CoordinatorLiveChoiceRecorderStep (Registers)
open CoordinatorLiveServiceFinish (OwnedRegisters)
open FollowerDownMeasurability (followerStateCode followerStatusCode)

abbrev Parameters := ConstructorDimensions.Parameters
variable {p : Parameters}
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p
abbrev Record (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "R" z => ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "W" z => rawInitialTransferWindow rate rewards C_star C_h z
-- Literal same-source calendar projections used below.
local notation "S" z:arg => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "lookup" => ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
local notation "Handover" => actualHandoverRecords rate rewards C_star C_h
local notation "bad" => ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h
/-- The initial fixed-calendar birth is the actual `.first` record at the
physical launch date. No nonempty-window or successful-selection premise is
part of the declaration: those facts are consequences of this actual branch. -/
public def initialBirthAt (ell : Fin p.T) (z : SourceInput p) : Prop :=
  ∃ r : Record rate, lookup ell z = some r ∧ r.input.state.coordinator = .first ∧
    r.input.time = ell ∧ S z = ell.val

/-- The later fixed-calendar birth is read at its actual suffix index
`ell - physicalStart`. Its incoming collection is empty and the exact installed
payload is witnessed by the source's `InstallationBirth` relation. -/
public def laterBirthAt (ell : Fin p.T) (z : SourceInput p) : Prop := ∃ b : Fin (R z).length,
    b.val = ell.val - S z ∧ (R z)[b.val].input.time = ell ∧ lookup ell z = some (R z)[b.val] ∧
    ∃ payload : Payload rate, ∃ ledger : Ledger rate, ∃ saved : Option (Fin p.T × Bool),
          (R z)[b.val].input.state.coordinator = .collection payload ledger saved ∧
          ledger.pending = ∅ ∧ ∃ installedPayload : Payload rate,
            InstallationBirth (R z)[b.val] installedPayload

/-- A fixed installation is present precisely on the actual initial `.first`
branch or an actual empty-collection installation. -/
public def installationBirthAt (ell : Fin p.T) (z : SourceInput p) : Prop :=
  initialBirthAt rate rewards C_star C_h ell z ∨ laterBirthAt rate rewards C_star C_h ell z

/-- The later segment located by the uniquely determined original suffix
index of `ell`. The empty list is the source absence convention when no
actual empty-collection installation is present at that date. -/
public def laterBirthSegment (ell : Fin p.T) (z : SourceInput p) : List (Record rate) :=
  if hn : ell.val - S z < (R z).length then
    let b : Fin (R z).length := ⟨_, hn⟩
    if lookup ell z = some (R z)[b.val] ∧
        ∃ (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool)),
          (R z)[b.val].input.state.coordinator = .collection payload ledger saved ∧
          ledger.pending = ∅ then
      Handover z b
    else []
  else []

/-- Raw H support for one fixed actual installation. On the initial branch it
is the initial raw missing prefix. On a later branch it is the same actual
`actualHandoverRecords` list born at the exact suffix index. -/
public def rawPending (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) : Prop :=
  (∃ birth : Record rate, lookup ell z = some birth ∧ birth.input.state.coordinator = .first ∧
      birth.input.time = ell ∧ S z = ell.val ∧ ∃ j : Fin (W z).length,
        j.val < rawMissingPrefixLength rate rewards C_star C_h z ∧ (W z)[j.val].input.time = t ∧
        ∃ selected : Selection ((W z)[j.val]).input,
          (W z)[j.val].output.preparation.coordinator.selection = some selected ∧
          i ∈ selected.view.pendingAtChoice) ∨
    (∃ b : Fin (R z).length, b.val = ell.val - S z ∧ (R z)[b.val].input.time = ell ∧
      lookup ell z = some (R z)[b.val] ∧ ∃ payload : Payload rate, ∃ ledger : Ledger rate,
          ∃ saved : Option (Fin p.T × Bool),
            (R z)[b.val].input.state.coordinator = .collection payload ledger saved ∧
            ledger.pending = ∅ ∧ ∃ installedPayload : Payload rate,
              InstallationBirth (R z)[b.val] installedPayload ∧
              ∃ j : Fin (Handover z b).length, (Handover z b)[j.val].input.time = t ∧
                ∃ selected : Selection ((Handover z b)[j.val]).input,
                  (Handover z b)[j.val].output.preparation.coordinator.selection = some selected ∧
                  i ∈ selected.view.pendingAtChoice)

/-- The analytic H mask uses only the inclusive first-bad-date test. In
particular the update that detects failure remains in the support. -/
public def pending (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) : Prop :=
  t.val + 1 ≤ bad z ∧ rawPending rate rewards C_star C_h ell t i z

public def rawPendingSet (ell t : Fin p.T) (z : SourceInput p) : Finset (Fin (p.m - 1)) :=
  Finset.univ.filter fun i => rawPending rate rewards C_star C_h ell t i z

public def pendingSet (ell t : Fin p.T) (z : SourceInput p) : Finset (Fin (p.m - 1)) :=
  Finset.univ.filter fun i => pending rate rewards C_star C_h ell t i z

/-- The original raw left endpoint is the fixed birth date, or the terminal
sentinel when this date is not an actual installation. -/
public def rawSigma (ell : Fin p.T) (z : SourceInput p) : ℕ :=
  if installationBirthAt rate rewards C_star C_h ell z then ell.val + 1 else p.T + 1

/-- The raw right endpoint is one beyond the original actual missing-at-choice
prefix. It is computed before the first-bad mask, so an earlier failure can
erase every task without moving either raw endpoint. -/
public def rawTheta (ell : Fin p.T) (z : SourceInput p) : ℕ :=
  if initialBirthAt rate rewards C_star C_h ell z then
    ell.val + rawMissingPrefixLength rate rewards C_star C_h z + 1
  else if laterBirthAt rate rewards C_star C_h ell z then
    ell.val + (laterBirthSegment rate rewards C_star C_h ell z).length + 1
  else p.T + 1

local notation "initialAt" => initialBirthAt rate rewards C_star C_h
local notation "laterAt" => laterBirthAt rate rewards C_star C_h
local notation "birthAt" => installationBirthAt rate rewards C_star C_h
local notation "birthSegment" => laterBirthSegment rate rewards C_star C_h
local notation "rawTask" => rawPending rate rewards C_star C_h
local notation "task" => pending rate rewards C_star C_h
local notation "rawTasks" => rawPendingSet rate rewards C_star C_h
local notation "tasks" => pendingSet rate rewards C_star C_h
local notation "sigmaH" => rawSigma rate rewards C_star C_h
local notation "thetaH" => rawTheta rate rewards C_star C_h

public theorem mem_rawPendingSet_iff (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    i ∈ rawTasks ell t z ↔ rawTask ell t i z := by
  simp only [rawPendingSet, Finset.mem_filter, Finset.mem_univ, true_and]

public theorem mem_pendingSet_iff (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    i ∈ tasks ell t z ↔ t.val + 1 ≤ bad z ∧ rawTask ell t i z := by
  simp [pendingSet, pending]

/-- Empty incoming pending at an actual later collection row is the actual later-installation. -/
public theorem laterBirthAt_is_laterChosen (z : SourceInput p) (b : Fin (R z).length)
    (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : (R z)[b.val].input.state.coordinator = .collection payload ledger saved)
    (hempty : ledger.pending = ∅) :
    ReferenceCollectionPhaseHistory.laterChosen (R z)[b.val].input = true := by
  exact (ReferencePostReplacementCollectionHandoverSourcePrefix.actual_collection_laterChosen_iff_pending_empty
    rate rewards C_star C_h z b payload ledger saved hstate).2 hempty

private theorem handover_prefix (z : SourceInput p) (b : Fin (R z).length) :
    (Handover z b).IsPrefix ((R z).drop b.val) := by
  unfold actualHandoverRecords
  apply (List.takeWhile_prefix _).trans
  rw [List.drop_eq_getElem_cons b.isLt]
  exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩

private theorem actualHandover_index (z : SourceInput p) (b : Fin (R z).length)
    (j : Fin (Handover z b).length) :
    ∃ hk : b.val + j.val < (R z).length, (Handover z b)[j.val] = (R z)[b.val + j.val]'hk := by
  have hp := handover_prefix rate rewards C_star C_h z b
  have hlen := hp.length_le
  simp only [List.length_drop] at hlen
  have hk : b.val + j.val < (R z).length := by have := j.isLt; omega
  refine ⟨hk, ?_⟩
  rw [hp.getElem j.isLt, List.getElem_drop]

private theorem actual_at_index (z : SourceInput p) (k : Fin (R z).length) : lookup
      (R z)[k.val].input.time z = some (R z)[k.val] := by
  have ht := completeSuffixRecord_time rate rewards C_star C_h z k
  have hs : S z ≤ (R z)[k.val].input.time.val := by omega
  have hi : (R z)[k.val].input.time.val - S z = k.val := by omega
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ite_eq_left hs, hi]
  exact List.getElem?_eq_getElem k.isLt

/-- Every later H row is the same original date-indexed record. -/
public theorem actualHandover_actualRecord (z : SourceInput p) (b : Fin (R z).length)
    (j : Fin (Handover z b).length) :
    lookup (Handover z b)[j.val].input.time z = some (Handover z b)[j.val] := by
  obtain ⟨hk, heq⟩ := actualHandover_index rate rewards C_star C_h z b j
  rw [heq]
  exact actual_at_index rate rewards C_star C_h z ⟨b.val + j.val, hk⟩

private theorem actualRecord_index (ell : Fin p.T) (z : SourceInput p) (r : Record rate)
    (hr : lookup ell z = some r) : ∃ b : Fin (R z).length,
      b.val = ell.val - S z ∧ (R z)[b.val] = r ∧ r.input.time = ell := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split at hr
  · rename_i hs
    obtain ⟨hb, he⟩ := List.getElem?_eq_some_iff.mp hr
    let b : Fin (R z).length := ⟨_, hb⟩
    refine ⟨b, rfl, he, ?_⟩
    have ht := completeSuffixRecord_time rate rewards C_star C_h z b
    rw [he] at ht
    exact Fin.ext (by dsimp only [b] at ht; omega)
  · cases hr

private theorem first_index_zero (z : SourceInput p) (b : Fin (R z).length)
    (hf : (R z)[b.val].input.state.coordinator = .first) : b.val = 0 := by
  by_contra hn
  have he : b.val - 1 + 1 = b.val := by omega
  have hadj := complete_adjacent
    (rate := rate) rewards C_star C_h z (b.val - 1) (by rw [he]; exact b.isLt)
  have hphase := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
    rate rewards C_star C_h z).1 ⟨b.val - 1, by omega⟩
  apply hphase.2.2.2.1
  simpa only [he, hf] using (congrArg State.coordinator hadj).symm

/-- The initial birth is recognized solely from the actual incoming first constructor. -/
public theorem initialBirthAt_iff_actual_first (ell : Fin p.T) (z : SourceInput p) : initialAt ell z ↔
      ∃ r : Record rate, lookup ell z = some r ∧ r.input.state.coordinator = .first := by
  constructor
  · rintro ⟨r, hr, hf, _⟩
    exact ⟨r, hr, hf⟩
  · rintro ⟨r, hr, hf⟩
    obtain ⟨b, _hb, he, ht⟩ := actualRecord_index rate rewards C_star C_h ell z r hr
    have hz := first_index_zero rate rewards C_star C_h z b (he ▸ hf)
    have htime := completeSuffixRecord_time rate rewards C_star C_h z b
    rw [he, ht, hz, Nat.add_zero] at htime
    exact ⟨r, hr, hf, ht, htime.symm⟩

/-- Empty COLLECTION is exactly later birth on this original physical row. -/
public theorem laterBirthAt_iff_actual_empty_collection (ell : Fin p.T) (z : SourceInput p) :
    laterAt ell z ↔ ∃ (r : Record rate) (payload : Payload rate) (ledger : Ledger rate)
        (saved : Option (Fin p.T × Bool)),
        lookup ell z = some r ∧ r.input.state.coordinator = .collection payload ledger saved ∧
          ledger.pending = ∅ := by
  constructor
  · rintro ⟨b, _hb, _ht, hr, payload, ledger, saved, hc, hp, _⟩
    exact ⟨(R z)[b.val], payload, ledger, saved, hr, hc, hp⟩
  · rintro ⟨r, payload, ledger, saved, hr, hc, hp⟩
    obtain ⟨b, hb, he, ht⟩ := actualRecord_index rate rewards C_star C_h ell z r hr
    have hc' : (R z)[b.val].input.state.coordinator = .collection payload ledger saved := he ▸ hc
    have hl := laterBirthAt_is_laterChosen rate rewards C_star C_h z b payload ledger saved hc' hp
    obtain ⟨installed, hi, _⟩ :=
      ReferenceOriginalTransferPhysicalIntervals.actual_later_installation_missing_date_iff
        rate rewards C_star C_h z b hl
    exact ⟨b, hb, by rw [he, ht], by rw [he]; exact hr, payload, ledger, saved, hc', hp, installed, hi⟩

/-- The two actual incoming birth constructors are disjoint. -/
public theorem initialBirthAt_not_laterBirthAt (ell : Fin p.T) (z : SourceInput p)
    (hi : initialAt ell z) : ¬ laterAt ell z := by
  obtain ⟨r, hr, hf⟩ := (initialBirthAt_iff_actual_first rate rewards C_star C_h ell z).mp hi
  rintro hl
  obtain ⟨q, payload, ledger, saved, hq, hc, _⟩ :=
    (laterBirthAt_iff_actual_empty_collection rate rewards C_star C_h ell z).mp hl
  have he := Option.some.inj (hr.symm.trans hq)
  subst q
  rw [hf] at hc
  cases hc

/-- The later segment selector returns the same actual handover records. -/
public theorem laterBirthSegment_eq (ell : Fin p.T) (z : SourceInput p) (b : Fin (R z).length)
    (hb : b.val = ell.val - S z) (hr : lookup ell z = some (R z)[b.val])
    (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hc : (R z)[b.val].input.state.coordinator = .collection payload ledger saved)
    (hp : ledger.pending = ∅) : birthSegment ell z = Handover z b := by
  unfold laterBirthSegment
  dsimp only
  have hn : ell.val - S z < (R z).length := hb ▸ b.isLt
  rw [dite_eq_left hn]
  simp only [← hb]
  exact ite_eq_left ⟨hr, payload, ledger, saved, hc, hp⟩

/-- Original endpoints retain their full bounds even when an earlier failure erases every task. -/
public theorem rawEndpoints_bounds (ell : Fin p.T) (z : SourceInput p) :
    1 ≤ sigmaH ell z ∧ sigmaH ell z ≤ thetaH ell z ∧ thetaH ell z ≤ p.T + 1 := by
  have hR := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  by_cases hi : initialAt ell z
  · have hiCopy := hi
    obtain ⟨_r, _hr, _hf, _ht, hstart⟩ := hiCopy
    have hW : (W z).length ≤ (R z).length := by
      rw [raw_window_eq_complete_suffix_takeWhile]
      exact (List.takeWhile_prefix _).length_le
    have hm : rawMissingPrefixLength rate rewards C_star C_h z ≤ (W z).length :=
      (List.takeWhile_prefix _).length_le
    simp only [rawSigma, rawTheta, installationBirthAt, hi, true_or, ite_true]
    omega
  · by_cases hl : laterAt ell z
    · have hlCopy := hl
      obtain ⟨b, hb, ht, hr, payload, ledger, saved, hc, hp, _⟩ := hlCopy
      have hseg := laterBirthSegment_eq rate rewards C_star C_h ell z b hb hr payload ledger saved hc hp
      have hlen := (handover_prefix rate rewards C_star C_h z b).length_le
      simp only [List.length_drop] at hlen
      have htime := completeSuffixRecord_time rate rewards C_star C_h z b
      rw [ht] at htime
      simp only [rawSigma, rawTheta, installationBirthAt, hi, hl, false_or, ite_true, ite_false, hseg]
      omega
    · simp only [rawSigma, rawTheta, installationBirthAt, hi, hl, false_or, ite_false]
      omega

public def birthReadyCode : CoordinatorCode p rate → Bool
  | .inl _ => true
  | .inr (.inr (.inl (_, ledger, _))) => decide (ledger.pending = ∅)
  | _ => false

public def birthReady (ell : Fin p.T) (z : SourceInput p) : Bool := optionalElim false
    (fun code : StateCode p rate =>
      birthReadyCode rate code.1)
    (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h ell z)

/-- Readiness recognizes both actual birth constructors on the same source. -/
public theorem birthReady_iff (ell : Fin p.T) (z : SourceInput p) :
    birthReady rate rewards C_star C_h ell z = true ↔ birthAt ell z := by
  rw [installationBirthAt, initialBirthAt_iff_actual_first,
    laterBirthAt_iff_actual_empty_collection]
  unfold birthReady ReferenceSourcePrefixHistoryFiltration.incoming
  cases hr : lookup ell z with
  | none => simp [optionalElim]
  | some r =>
      cases hc : r.input.state.coordinator <;>
        simp [optionalElim, encodeState, encodeCoordinator, birthReadyCode, hc]

private theorem birthReadyCode_measurable : Measurable (birthReadyCode (p := p) rate) := by
  exact measurable_const.sumElim (measurable_const.sumElim
      (((measurable_of_countable (fun q : Ledger rate × Option (Fin p.T × Bool) =>
          decide (q.1.pending = ∅))).comp measurable_snd).sumElim measurable_const))

public theorem birthReady_factor (control0 : ContinuousLearningRows.TimeControl p)
    (ell : Fin p.T) (z : SourceInput p) :
    birthReady rate rewards C_star C_h ell z = birthReady rate rewards C_star C_h ell
        (sourcePrefix control0 ell.val z) := by
  unfold birthReady
  rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 ell z]

public theorem birthReady_measurable (control0 : ContinuousLearningRows.TimeControl p) (ell : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (ell.val + 1)]
      (birthReady rate rewards C_star C_h ell) := by
  exact (measurable_optionalElim false
    _ ((birthReadyCode_measurable rate).comp measurable_fst)).comp
      (ReferenceSourcePrefixHistoryFiltration.incoming_measurable rate rewards C_star C_h control0 ell)

/-- Raw sigma is tested by original birth readiness, independently of masking. -/
public theorem rawSigma_le_iff (ell : Fin p.T) (z : SourceInput p) (n : ℕ) : sigmaH ell z ≤ n ↔
      p.T + 1 ≤ n ∨ ell.val + 1 ≤ n ∧ birthReady rate rewards C_star C_h ell z = true := by
  by_cases hb : birthAt ell z
  · rw [rawSigma, ite_eq_left hb]
    rw [← birthReady_iff] at hb
    simp only [hb, and_true]
    omega
  · rw [rawSigma, ite_eq_right hb]
    have hn := mt (birthReady_iff rate rewards C_star C_h ell z).mp hb
    simp only [hn, Bool.false_eq_true, and_false, or_false]

/-- Raw sigma is a stopping time in the analytical source-prefix filtration. -/
public theorem rawSigma_preRoundStoppingTime
    (control0 : ContinuousLearningRows.TimeControl p) (ell : Fin p.T) :
    PhaseServiceWaiting.IsPreRoundStoppingTime (sourcePrefixFiltration control0) (sigmaH ell) := by
  intro n
  by_cases hT : p.T + 1 ≤ n
  · convert @MeasurableSet.univ _ (sourcePrefixFiltration control0 n) using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_univ, rawSigma_le_iff, hT, true_or]
  · by_cases he : ell.val + 1 ≤ n
    · convert ((birthReady_measurable rate rewards C_star C_h control0 ell).mono
        ((sourcePrefixFiltration control0).mono he) le_rfl) (measurableSet_singleton true) using 1
      ext z
      simp only [Set.mem_ofPred_eq, rawSigma_le_iff, hT, he, false_or, true_and,
        Set.mem_preimage, Set.mem_singleton_iff]
    · convert @MeasurableSet.empty _ (sourcePrefixFiltration control0 n) using 1
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, rawSigma_le_iff,
        hT, he, false_or, false_and]

private theorem mem_missing_iff (r : Record rate) (i : Fin (p.m - 1)) :
    i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate r ↔
      ∃ selected : Selection r.input, r.output.preparation.coordinator.selection = some selected ∧
          i ∈ selected.view.pendingAtChoice := by
  unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
    ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
  cases r.output.preparation.coordinator.selection <;> simp [Option.map, Option.getD]
  rfl

private theorem handover_calendar (z : SourceInput p) (b : Fin (R z).length)
    (j : Fin (Handover z b).length) :
    (Handover z b)[j.val].input.time.val = S z + b.val + j.val := by
  obtain ⟨hk, he⟩ := actualHandover_index rate rewards C_star C_h z b j
  rw [he]
  have ht := completeSuffixRecord_time rate rewards C_star C_h z ⟨b.val + j.val, hk⟩
  exact ht.trans (Nat.add_assoc _ _ _).symm

/-- A raw task uses the actual selected pending label at or after its birth. -/
public theorem rawPending_actual_choice (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : SourceInput p) (hp : rawTask ell t i z) : ell.val ≤ t.val ∧ birthAt ell z ∧
      ∃ r : Record rate, lookup t z = some r ∧ ∃ selected : Selection r.input,
          r.output.preparation.coordinator.selection = some selected ∧
          i ∈ selected.view.pendingAtChoice := by
  rcases hp with ⟨birth, hb, hf, htBirth, hstart, j, _hj, ht, selected, hs, hi⟩ |
    ⟨b, hb, htBirth, hlookup, payload, ledger, saved, hc, he, installed, hinst,
      j, ht, selected, hs, hi⟩
  · have hcal := raw_window_record_calendar rate rewards C_star C_h z j
    have hdate : (W z)[j.val].input.time.val = ell.val + j.val := by
      simpa only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart, hstart] using hcal.1
    refine ⟨by rw [ht] at hdate; omega, Or.inl ⟨birth, hb, hf, htBirth, hstart⟩,
      (W z)[j.val], ?_, selected, hs, hi⟩
    exact ht ▸ hcal.2
  · have htime := completeSuffixRecord_time rate rewards C_star C_h z b
    rw [htBirth] at htime
    have hcal := handover_calendar rate rewards C_star C_h z b j
    rw [ht] at hcal
    refine ⟨by omega, Or.inr ⟨b, hb, htBirth, hlookup, payload, ledger, saved,
      hc, he, installed, hinst⟩, _, ?_, selected, hs, hi⟩
    exact ht ▸ actualHandover_actualRecord rate rewards C_star C_h z b j

/-- Pending labels shrink backwards within the SAME raw installation. -/
public theorem rawPending_backward (ell u t : Fin p.T) (i : Fin (p.m - 1))
    (z : SourceInput p) (heu : ell.val ≤ u.val) (hut : u.val ≤ t.val) (hp : rawTask ell t i z) :
    rawTask ell u i z := by
  rcases hp with ⟨birth, hb, hf, htBirth, hstart, j, hj, ht, selected, hs, hi⟩ |
    ⟨b, hb, htBirth, hlookup, payload, ledger, saved, hc, he, installed, hinst,
      j, ht, selected, hs, hi⟩
  · have hcal := (raw_window_record_calendar rate rewards C_star C_h z j).1
    change (W z)[j.val].input.time.val = S z + j.val at hcal
    rw [ht, hstart] at hcal
    have hk : u.val - ell.val < (W z).length := by have := j.isLt; omega
    let k : Fin (W z).length := ⟨u.val - ell.val, hk⟩
    have hkj : k.val ≤ j.val := by dsimp only [k]; omega
    have hsub := raw_missing_antitone rate rewards C_star C_h z k j hkj
    have him := (mem_missing_iff rate _ i).mpr ⟨selected, hs, hi⟩
    obtain ⟨choice, hchoice, hi'⟩ := (mem_missing_iff rate _ i).mp (hsub him)
    have hdate := (raw_window_record_calendar rate rewards C_star C_h z k).1
    have hdate' : (W z)[k.val].input.time = u := by
      apply Fin.ext
      change (W z)[k.val].input.time.val = S z + k.val at hdate
      rw [hstart] at hdate
      dsimp only [k] at hdate ⊢
      omega
    exact Or.inl ⟨birth, hb, hf, htBirth, hstart, k,
      lt_of_le_of_lt hkj hj, hdate', choice, hchoice, hi'⟩
  · let H := Handover z b
    let V := (R z)[b.val] :: continuingPrefix rate rewards C_star C_h z (b.val + 1)
    have hprefix : H.IsPrefix V := List.takeWhile_prefix _
    have htime := completeSuffixRecord_time rate rewards C_star C_h z b
    rw [htBirth] at htime
    have hcal := handover_calendar rate rewards C_star C_h z b j
    rw [ht] at hcal
    have hk : u.val - ell.val < H.length := by
      change u.val - ell.val < (Handover z b).length
      have := j.isLt
      omega
    let k : Fin H.length := ⟨u.val - ell.val, hk⟩
    have hkj : k.val ≤ j.val := by dsimp only [k]; omega
    let kV : Fin V.length := ⟨k.val, lt_of_lt_of_le k.isLt hprefix.length_le⟩
    let jV : Fin V.length := ⟨j.val, lt_of_lt_of_le j.isLt hprefix.length_le⟩
    have hgetK : H[k.val] = V[kV.val] := hprefix.getElem k.isLt
    have hgetJ : H[j.val] = V[jV.val] := hprefix.getElem j.isLt
    have hl := laterBirthAt_is_laterChosen rate rewards C_star C_h z b payload ledger saved hc he
    have hsub := ReferenceOriginalTransferPhysicalIntervals.actual_later_installation_missing_nested
      rate rewards C_star C_h z b hl kV jV hkj
    have him := (mem_missing_iff rate _ i).mpr ⟨selected, hs, hi⟩
    change i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate H[j.val] at him
    rw [hgetJ] at him
    have himK := hsub him
    rw [← hgetK] at himK
    obtain ⟨choice, hchoice, hi'⟩ := (mem_missing_iff rate _ i).mp himK
    have hdate := handover_calendar rate rewards C_star C_h z b k
    have hdate' : H[k.val].input.time = u := by
      apply Fin.ext
      dsimp only [k] at hdate ⊢
      change (Handover z b)[u.val - ell.val].input.time.val = u.val
      omega
    exact Or.inr ⟨b, hb, htBirth, hlookup, payload, ledger, saved, hc, he,
      installed, hinst, k, hdate', choice, hchoice, hi'⟩

/-- Inclusive masking preserves backward nesting and the detecting UPDATE. -/
public theorem pending_backward (ell u t : Fin p.T) (i : Fin (p.m - 1))
    (z : SourceInput p) (heu : ell.val ≤ u.val) (hut : u.val ≤ t.val) (hp : task ell t i z) :
    task ell u i z :=
  ⟨by have := hp.1; omega, rawPending_backward rate rewards C_star C_h ell u t i z heu hut hp.2⟩

/-- Nonempty raw support has exactly the original half-open date interval. -/
public theorem rawPending_nonempty_iff_interval (ell t : Fin p.T) (z : SourceInput p) :
    (∃ i : Fin (p.m - 1), rawTask ell t i z) ↔ sigmaH ell z ≤ t.val + 1 ∧
        t.val + 1 < thetaH ell z := by
  constructor
  · rintro ⟨i, hp⟩
    have ⟨hle, hbirth, _⟩ := rawPending_actual_choice rate rewards C_star C_h ell t i z hp
    rw [rawSigma, ite_eq_left hbirth]
    refine ⟨by omega, ?_⟩
    rcases hp with ⟨birth, hb, hf, htBirth, hstart, j, hj, ht, _⟩ |
      ⟨b, hb, htBirth, hlookup, payload, ledger, saved, hc, he, installed, hinst, j, ht, _⟩
    · have hi : initialAt ell z := ⟨birth, hb, hf, htBirth, hstart⟩
      have hcal := (raw_window_record_calendar rate rewards C_star C_h z j).1
      change (W z)[j.val].input.time.val = S z + j.val at hcal
      rw [ht, hstart] at hcal
      rw [rawTheta, ite_eq_left hi]
      omega
    · have hl : laterAt ell z :=
        ⟨b, hb, htBirth, hlookup, payload, ledger, saved, hc, he, installed, hinst⟩
      have hn : ¬ initialAt ell z :=
        fun hi => initialBirthAt_not_laterBirthAt rate rewards C_star C_h ell z hi hl
      have hseg := laterBirthSegment_eq rate rewards C_star C_h ell z b hb hlookup
        payload ledger saved hc he
      have htime := completeSuffixRecord_time rate rewards C_star C_h z b
      rw [htBirth] at htime
      have hcal := handover_calendar rate rewards C_star C_h z b j
      rw [ht] at hcal
      rw [rawTheta, ite_eq_right hn, ite_eq_left hl, hseg]
      have := j.isLt
      omega
  · rintro ⟨hsigma, htheta⟩
    by_cases hi : initialAt ell z
    · have hbirth : birthAt ell z := Or.inl hi
      rw [rawSigma, ite_eq_left hbirth] at hsigma
      rw [rawTheta, ite_eq_left hi] at htheta
      obtain ⟨birth, hb, hf, htBirth, hstart⟩ := hi
      have hj : t.val - ell.val < rawMissingPrefixLength rate rewards C_star C_h z := by omega
      have hlen : rawMissingPrefixLength rate rewards C_star C_h z ≤ (W z).length := (List.takeWhile_prefix _).length_le
      let j : Fin (W z).length := ⟨t.val - ell.val, lt_of_lt_of_le hj hlen⟩
      have hnonempty := (raw_missing_prefix_iff rate rewards C_star C_h z j).mpr hj
      obtain ⟨i, him⟩ := hnonempty
      obtain ⟨selected, hs, hi⟩ := (mem_missing_iff rate _ i).mp him
      have hcal := (raw_window_record_calendar rate rewards C_star C_h z j).1
      have ht : (W z)[j.val].input.time = t := by
        apply Fin.ext
        calc (W z)[j.val].input.time.val = S z + j.val := hcal
          _ = ell.val + j.val := congrArg (fun n => n + j.val) hstart
          _ = t.val := Nat.add_sub_of_le (by omega)
      exact ⟨i, Or.inl ⟨birth, hb, hf, htBirth, hstart, j, hj, ht, selected, hs, hi⟩⟩
    · by_cases hl : laterAt ell z
      · have hbirth : birthAt ell z := Or.inr hl
        rw [rawSigma, ite_eq_left hbirth] at hsigma
        rw [rawTheta, ite_eq_right hi, ite_eq_left hl] at htheta
        obtain ⟨b, hb, htBirth, hlookup, payload, ledger, saved, hc, he, installed, hinst⟩ := hl
        have hseg := laterBirthSegment_eq rate rewards C_star C_h ell z b hb hlookup
          payload ledger saved hc he
        rw [hseg] at htheta
        let H := Handover z b
        have hj : t.val - ell.val < H.length := by dsimp only [H]; omega
        let j : Fin H.length := ⟨t.val - ell.val, hj⟩
        have hm : missingAtChoice H[j.val] = true :=
          List.mem_takeWhile_imp (List.getElem_mem j.isLt)
        unfold missingAtChoice at hm
        cases hs : H[j.val].output.preparation.coordinator.selection with
        | none => simp only [hs, Bool.false_eq_true] at hm
        | some selected =>
            rw [hs] at hm
            obtain ⟨i, him⟩ := of_decide_eq_true hm
            have htime := completeSuffixRecord_time rate rewards C_star C_h z b
            rw [htBirth] at htime
            have hcal := handover_calendar rate rewards C_star C_h z b j
            have ht : H[j.val].input.time = t := by
              apply Fin.ext
              dsimp only [j, H] at hcal ⊢
              omega
            exact ⟨i, Or.inr ⟨b, hb, htBirth, hlookup, payload, ledger, saved, hc, he,
              installed, hinst, j, ht, selected, hs, him⟩⟩
      · have hn : ¬ birthAt ell z := by
          simpa only [installationBirthAt, not_or] using And.intro hi hl
        rw [rawSigma, ite_eq_right hn] at hsigma
        have := t.isLt
        omega

/-- After birth, raw theta has occurred exactly when the current raw task set is empty. -/
public theorem rawTheta_le_iff_current_empty (ell : Fin p.T) (z : SourceInput p)
    (n : ℕ) (hn : 1 ≤ n) (hnT : n ≤ p.T) : thetaH ell z ≤ n ↔ sigmaH ell z ≤ n ∧
        ¬ ∃ i : Fin (p.m - 1), rawTask ell ⟨n - 1, by omega⟩ i z := by
  have hinterval := rawPending_nonempty_iff_interval rate rewards C_star C_h ell ⟨n - 1, by omega⟩ z
  have horder := (rawEndpoints_bounds rate rewards C_star C_h ell z).2.1
  simp only [Nat.sub_add_cancel hn] at hinterval
  rw [hinterval]
  omega

open ReferencePostReplacementCollectionHandoverPredictableSupport

private theorem live_continues_eq_notCutoff (z : SourceInput p) (t : Fin p.T)
    (k : Fin (R z).length) (hr : lookup t z = some (R z)[k.val])
    (ht : (R z)[k.val].input.time = t) (r : Registers p rate.eta)
    (q : OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hc : (R z)[k.val].input.state.coordinator = .live r q base) :
    handoverIncomingLiveContinues rate rewards C_star C_h t z =
      decide (ReferenceCollectionPhaseHistory.cutoffChosen (R z)[k.val].input = false) := by
  let current := liveInput (R z)[k.val].input r q base
  have hquery : handoverIncomingLiveContinues rate rewards C_star C_h t z =
      (match CoordinatorPhaseClock.startRound p rate.eta.val t r.priorClock r.pendingAtChoice with
       | .error _ => false | .ok result => decide (result.clock.u = none)) := by
    unfold handoverIncomingLiveContinues ReferenceSourcePrefixHistoryFiltration.incoming
    rw [hr]
    simp only [Option.map_some, optionalElim, encodeState, hc, encodeCoordinator,
      encodeLive, handoverIncomingLiveContinuesCode]
    rfl
  rw [hquery]
  obtain ⟨hprep, hb⟩ := ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
    rate rewards C_star C_h z k r q base hc
  change (prepare (R z)[k.val].input).coordinator =
    .live r q base (CoordinatorRoundDispatch.dispatchLive current) at hprep
  cases hd : CoordinatorRoundDispatch.dispatchLive current with
  | continuingChosen dispatched hs continuation selected =>
      rw [hd] at hb
      have hs' : CoordinatorPhaseClock.startRound p rate.eta.val t r.priorClock r.pendingAtChoice =
          .ok dispatched.startResult := by
        simpa only [current, liveInput, liveRegistersAt, Registers.clockPending_eq, ht] using hs
      have hcut : ReferenceCollectionPhaseHistory.cutoffChosen (R z)[k.val].input = false := by
        simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hprep, hd]
      rw [hs']
      change decide (dispatched.startResult.clock.u = none) = decide (_ = false)
      rw [hb.2.1, hcut]
      rfl
  | cutoffChosen dispatched hs ledger hinit hledger hdomains hclock hpending hnoStart selected =>
      rw [hd] at hb
      have hs' : CoordinatorPhaseClock.startRound p rate.eta.val t r.priorClock r.pendingAtChoice =
          .ok dispatched.startResult := by
        simpa only [current, liveInput, liveRegistersAt, Registers.clockPending_eq, ht] using hs
      have hu : dispatched.startResult.clock.u = some t := by
        have he := congrArg CoordinatorPhaseClock.ClockRegisters.u hb.2.1
        simpa only [current, liveInput, liveRegistersAt, ht] using he
      have hcut : ReferenceCollectionPhaseHistory.cutoffChosen (R z)[k.val].input = true := by
        simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hprep, hd]
      rw [hs']
      change decide (dispatched.startResult.clock.u = none) = decide (_ = false)
      rw [hu, hcut]
      rfl
  | clockFailure _ => rw [hd] at hb; exact hb.elim
  | initializerFailure _ _ _ => rw [hd] at hb; exact hb.elim
  | localFailure _ _ _ => rw [hd] at hb; exact hb.elim

public def liveRequestCode (ell : Fin p.T) (i : Fin (p.m - 1)) : CoordinatorCode p rate → Bool
  | .inr (.inl (payload, live)) => decide (payload.sigma = ell ∧ i ∈ live.pending)
  | _ => false

public def liveRequest (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) : Bool :=
  optionalElim false (fun code : StateCode p rate =>
      liveRequestCode rate ell i code.1)
    (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z)

/-- The local pre-round fixed-installation query: readiness at birth, then
the SAME LIVE stamp and pending label with the current cutoff excluded. -/
public def preRoundRequest (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) : Prop :=
  (ell = t ∧ birthReady rate rewards C_star C_h ell z = true) ∨
    (ell.val < t.val ∧ liveRequest rate rewards C_star C_h ell t i z = true ∧
      handoverIncomingLiveContinues rate rewards C_star C_h t z = true)

private theorem liveRequestCode_measurable (ell : Fin p.T) (i : Fin (p.m - 1)) :
    Measurable (liveRequestCode (p := p) rate ell i) := by
  have hσ : Measurable (fun payload : Payload rate => payload.sigma) :=
    measurable_fst.comp (measurable_snd.comp
      (comap_measurable LaterAssignmentStartMeasurability.payloadObservation))
  have hLive : Measurable (fun pair : Payload rate × LiveDiscrete p =>
        decide (pair.1.sigma = ell ∧ i ∈ pair.2.pending)) :=
    (measurable_of_countable (fun q : Fin p.T × Finset (Fin (p.m - 1)) =>
      decide (q.1 = ell ∧ i ∈ q.2))).comp ((hσ.comp measurable_fst).prodMk
          ((measurable_of_countable (fun live :
            LiveDiscrete p => live.pending)).comp measurable_snd))
  exact measurable_const.sumElim (hLive.sumElim (measurable_const.sumElim measurable_const))

public theorem liveRequest_factor (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    liveRequest rate rewards C_star C_h ell t i z = liveRequest rate rewards C_star C_h ell t i
        (sourcePrefix control0 t.val z) := by
  unfold liveRequest
  rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 t z]

public theorem liveRequest_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) : Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (liveRequest rate rewards C_star C_h ell t i) :=
  (measurable_optionalElim false
    _ ((liveRequestCode_measurable rate ell i).comp measurable_fst)).comp
      (ReferenceSourcePrefixHistoryFiltration.incoming_measurable rate rewards C_star C_h control0 t)

public theorem preRoundRequest_factor (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    preRoundRequest rate rewards C_star C_h ell t i z ↔
      preRoundRequest rate rewards C_star C_h ell t i (sourcePrefix control0 t.val z) := by
  unfold preRoundRequest
  by_cases he : ell = t
  · subst ell
    rw [birthReady_factor rate rewards C_star C_h control0 t z,
      liveRequest_factor rate rewards C_star C_h control0 t t i z,
      handoverIncomingLiveContinues_factor rate rewards C_star C_h control0 t z]
  · simp only [he, false_and, false_or]
    rw [liveRequest_factor rate rewards C_star C_h control0 ell t i z,
      handoverIncomingLiveContinues_factor rate rewards C_star C_h control0 t z]

public theorem preRoundRequest_measurableSet (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      {z | preRoundRequest rate rewards C_star C_h ell t i z} := by
  by_cases he : ell = t
  · subst ell
    convert (birthReady_measurable rate rewards C_star C_h control0 t)
      (measurableSet_singleton true) using 1
    ext z
    simp only [preRoundRequest, lt_self_iff_false, false_and, or_false, true_and, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  · by_cases hlt : ell.val < t.val
    · convert ((liveRequest_measurable rate rewards C_star C_h control0 ell t i)
        (measurableSet_singleton true)).inter
        ((handoverIncomingLiveContinues_measurable rate rewards C_star C_h control0 t)
          (measurableSet_singleton true)) using 1
      ext z
      simp only [preRoundRequest, he, hlt, false_and, false_or, true_and,
        Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    · convert @MeasurableSet.empty _ (sourcePrefixFiltration control0 (t.val + 1)) using 1
      ext z
      simp only [preRoundRequest, he, hlt, false_and, or_self, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false]

private theorem live_request_of_actual (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : SourceInput p) (r : Record rate) (hr : lookup t z = some r)
    (registers : Registers p rate.eta) (owned : OwnedRegisters registers) (base : Fin (p.m - 1) → ℕ)
    (hc : r.input.state.coordinator = .live registers owned base)
    (hσ : registers.payload.sigma = ell) (hi : i ∈ registers.pendingAtChoice)
    (hlt : ell.val < t.val) (hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input = false) :
    preRoundRequest rate rewards C_star C_h ell t i z := by
  obtain ⟨k, _hk, he, ht⟩ := actualRecord_index rate rewards C_star C_h t z r hr
  have hclock := live_continues_eq_notCutoff rate rewards C_star C_h z t k
    (by rw [he]; exact hr) (by rw [he]; exact ht) registers owned base (by rw [he]; exact hc)
  have hcut' : ReferenceCollectionPhaseHistory.cutoffChosen (R z)[k.val].input = false := he ▸ hcut
  rw [hcut'] at hclock
  refine Or.inr ⟨hlt, ?_, hclock⟩
  unfold liveRequest ReferenceSourcePrefixHistoryFiltration.incoming
  rw [hr]
  simp only [Option.map_some, optionalElim, encodeState, hc, encodeCoordinator,
    encodeLive, liveRequestCode, decide_eq_true_eq]
  exact ⟨hσ, hi⟩

private theorem continuing_not_cutoff (r : Record rate) (hc : continuingTest r = true) :
    ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
  unfold ReferenceCollectionPhaseHistory.cutoffChosen
  rw [← ReferenceFirstReplacementCollectionPendingFoundation.preparation_eq r]
  cases hprep : r.output.preparation.coordinator with
  | live registers owned base outcome =>
      cases outcome <;> simp [continuingTest, hprep] at hc ⊢
  | _ => simp [continuingTest, hprep] at hc

/-- Every completed-list raw H task passes the genuine pre-round test. -/
public theorem rawPending_preRoundRequest (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : SourceInput p) (hp : rawTask ell t i z) :
    preRoundRequest rate rewards C_star C_h ell t i z := by
  have hactive := rawPending_actual_choice rate rewards C_star C_h ell t i z hp
  by_cases heq : ell = t
  · exact Or.inl ⟨heq, (birthReady_iff rate rewards C_star C_h ell z).mpr hactive.2.1⟩
  have hlt : ell.val < t.val := by
    have hne : ell.val ≠ t.val := fun h => heq (Fin.ext h)
    omega
  rcases hp with ⟨birth, hb, hf, htBirth, hstart, j, _hj, ht, selected, hs, hi⟩ |
    ⟨b, hb, htBirth, hlookup, payload, ledger, saved, hc, he, installed, hinst, j, ht,
      selected, hs, hi⟩
  · have hprov := raw_initial_transfer_window_provenance rate rewards C_star C_h z
    rcases hprov with hzero | ⟨hW, firstInstalled, firstSelected, _hfirstSelected,
      hinstall, _hfirstPayload, _hfirstPending, _hpayload0, hrows⟩
    · have := j.isLt
      omega
    · obtain ⟨choice, hchoice, hpayload, hphase, _⟩ := hrows j
      have hselected : choice = selected := Option.some.inj (hchoice.symm.trans hs)
      subst choice
      simp only [List.get_eq_getElem] at hphase
      have hσ : firstInstalled.registers.payload.sigma = (W z)[0].input.time := by
        rw [hinstall]
        rfl
      have hzeroDate := (raw_window_record_calendar rate rewards C_star C_h z ⟨0, hW⟩).1
      have hσell : selected.view.payload.sigma = ell := by
        apply Fin.ext
        rw [hpayload, hσ]
        change (W z)[0].input.time.val = S z + 0 at hzeroDate
        omega
      have hr : lookup t z = some (W z)[j.val] :=
        ht ▸ (raw_window_record_calendar rate rewards C_star C_h z j).2
      cases hcoord : (W z)[j.val].input.state.coordinator with
      | first =>
          have hborn := (initialBirthAt_iff_actual_first rate rewards C_star C_h t z).mpr
            ⟨_, hr, hcoord⟩
          obtain ⟨_r, _hr, _hf, _ht, hstart'⟩ := hborn
          omega
      | live registers owned base =>
          rw [hcoord] at hphase
          exact live_request_of_actual rate rewards C_star C_h ell t i z _ hr
            registers owned base hcoord (hphase.1 ▸ hσell) (hphase.2 ▸ hi) hlt
            (raw_window_no_collection_choice rate rewards C_star C_h z j)
      | collection _ _ _ => rw [hcoord] at hphase; exact hphase.elim
      | dagger => rw [hcoord] at hphase; exact hphase.elim
  · let Wlive := continuingPrefix rate rewards C_star C_h z (b.val + 1)
    let H := Handover z b
    have hlater := laterBirthAt_is_laterChosen rate rewards C_star C_h z b payload ledger saved hc he
    have hhistory := actual_later_installation_choice_history rate rewards C_star C_h z b
    rw [ite_eq_left hlater] at hhistory
    obtain ⟨rb, _qb, beta, _birthSelected, _hnext, hbirth, _hlater, _hbs, _hbp,
      _hbPending, _hrbPending, _hnoEvent, _hfollowers, _htail, _hnoRelease, hframes⟩ := hhistory
    have hσ : rb.payload.sigma = ell := by
      apply Fin.ext
      exact (ReferenceAssignmentPayloadChronology.installationBirth_time_eq
        (R z)[b.val] rb.payload hbirth).trans (congrArg Fin.val htBirth)
    have htime := completeSuffixRecord_time rate rewards C_star C_h z b
    rw [htBirth] at htime
    have hcal := handover_calendar rate rewards C_star C_h z b j
    rw [ht] at hcal
    have hjpos : 0 < j.val := by omega
    have hprefix : H.IsPrefix ((R z)[b.val] :: Wlive) := List.takeWhile_prefix _
    have hjV := lt_of_lt_of_le j.isLt hprefix.length_le
    have hn : j.val - 1 < Wlive.length := by simp only [List.length_cons] at hjV; omega
    let n : Fin Wlive.length := ⟨j.val - 1, hn⟩
    have hget : H[j.val] = Wlive[n.val] := by
      rw [hprefix.getElem j.isLt]
      have hj : j.val = n.val + 1 := by dsimp only [n]; omega
      simp only [hj, List.getElem_cons_succ]
    obtain ⟨registers, owned, choice, _next, _nextOwned, _states, _memories,
      hstate, hpay, hchoice, _hchoicePayload, hpending, _⟩ := hframes n
    have him : i ∈ ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate H[j.val] :=
      (mem_missing_iff rate _ i).mpr ⟨selected, hs, hi⟩
    rw [hget] at him
    have hmissing : ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing rate Wlive[n.val] =
        registers.pendingAtChoice := by
      unfold ReferenceFirstLiveSourceStoppedHandoverEndpoint.missing
        ReferenceFirstLiveSourceStoppedHandoverEndpoint.actualSelection
      rw [hchoice]
      exact hpending
    have ht' : Wlive[n.val].input.time = t := by rw [← hget]; exact ht
    have hr : lookup t z = some Wlive[n.val] := by
      have hrecord := actualHandover_actualRecord rate rewards C_star C_h z b j
      change lookup H[j.val].input.time z = some H[j.val] at hrecord
      rw [hget, ht'] at hrecord
      exact hrecord
    have hcontinue : continuingTest Wlive[n.val] = true :=
      List.mem_takeWhile_imp (List.getElem_mem n.isLt)
    exact live_request_of_actual rate rewards C_star C_h ell t i z _ hr
      registers owned beta hstate ((congrArg (fun P : Payload rate => P.sigma) hpay).trans hσ) (hmissing ▸ him) hlt
      (continuing_not_cutoff rate _ hcontinue)

public def startStatusCode :
    Unit ⊕ FollowerLifecycleMeasurability.StartRoundResultCode p rate → Option (Fin 3)
  | .inr (.success state _) => some state.status
  | _ => none

public def preRoundStatus (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) : Option (Fin 3) :=
  startStatusCode rate (preRoundStart rate rewards C_star C_h t i z)

public theorem preRoundStatus_factor (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    preRoundStatus rate rewards C_star C_h t i z = preRoundStatus rate rewards C_star C_h t i
        (sourcePrefix control0 t.val z) := by
  unfold preRoundStatus
  rw [preRoundStart_factor rate rewards C_star C_h control0 t i z]

public theorem preRoundStatus_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) : Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (preRoundStatus rate rewards C_star C_h t i) := by
  let : MeasurableSingletonClass (FollowerLifecycleMeasurability.StartRoundResultCode p rate) :=
    ⟨fun _ => trivial⟩
  have hstatus : Measurable (fun code : FollowerLifecycleMeasurability.StartRoundResultCode p rate =>
      match code with
      | .success state _ => some state.status
      | _ => (none : Option (Fin 3))) := measurable_of_countable _
  have hc : Measurable (startStatusCode (p := p) rate) := measurable_const.sumElim hstatus
  exact hc.comp (preRoundStart_measurable rate rewards C_star C_h control0 t i)

/-- The pre-round code is the genuine ordinary CHOICE status on every raw H task. -/
public theorem rawPending_actual_status (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : SourceInput p) (hp : rawTask ell t i z) :
    ∃ (r : Record rate) (choice : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p), lookup t z = some r ∧
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary choice memory ∧
      preRoundStatus rate rewards C_star C_h t i z = some (followerStatusCode choice.status) := by
  obtain ⟨_hle, _hb, r, hr, _⟩ := rawPending_actual_choice rate rewards C_star C_h ell t i z hp
  obtain ⟨k, _hk, he, _ht⟩ := actualRecord_index rate rewards C_star C_h t z r hr
  obtain ⟨state, memory, _choice, hin, _⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h z k i
  rw [he] at hin
  obtain ⟨actual, hactual, hcode⟩ :=
    preRoundStart_actual_choice rate rewards C_star C_h t i z r state memory hr hin
  exact ⟨r, actual, memory, hr, hactual, congrArg (startStatusCode rate) hcode⟩

/-- Later birth has universal pending and unoccupied CHOICE status. -/
public theorem laterBirthAt_unoccupied_pending_univ (ell : Fin p.T) (z : SourceInput p)
    (hb : laterAt ell z) :
    ∃ (r : Record rate) (selected : Selection r.input), lookup ell z = some r ∧
      r.output.preparation.coordinator.selection = some selected ∧
      selected.view.pendingAtChoice = Finset.univ ∧ ∀ i : Fin (p.m - 1),
        preRoundStatus rate rewards C_star C_h ell i z = some 0 ∧
        ∃ (choice : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary choice memory ∧
          choice.status = .unoccupied := by
  obtain ⟨b, _hb, _ht, hr, payload, ledger, saved, hc, hp, _⟩ := hb
  have hl := laterBirthAt_is_laterChosen rate rewards C_star C_h z b payload ledger saved hc hp
  have hh := actual_later_installation_choice_history rate rewards C_star C_h z b
  rw [ite_eq_left hl] at hh
  obtain ⟨_rb, _qb, _beta, selected, _hnext, _hbirth, _hlater, hs, _hpay, hpend,
    _hrbPend, _hnoEvent, hfollowers, _⟩ := hh
  refine ⟨(R z)[b.val], selected, hr, hs, hpend, fun i => ?_⟩
  obtain ⟨before, beforeMemory, choice, choiceMemory, hin, _hunoccupied,
    hchoice, hstatus, _⟩ := hfollowers i
  obtain ⟨actual, ha, hcode⟩ :=
    preRoundStart_actual_choice rate rewards C_star C_h ell i z (R z)[b.val] before beforeMemory hr hin
  have hsame := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (ha.symm.trans hchoice)
  have hstatus' : actual.status = .unoccupied := hsame.1 ▸ hstatus
  constructor
  · unfold preRoundStatus
    rw [hcode]
    simp only [startStatusCode, followerStateCode, hstatus', followerStatusCode]
  · exact ⟨choice, choiceMemory, hchoice, hstatus⟩

private theorem takeWhile_index {α : Type*} (xs : List α) (test : α → Bool)
    (n : ℕ) (hn : n < xs.length) (hall : ∀ j : Fin xs.length, j.val ≤ n → test xs[j.val] = true) :
    n < (xs.takeWhile test).length := by
  induction xs generalizing n with
  | nil => simp only [List.length_nil] at hn; omega
  | cons x xs ih =>
      have hx : test x = true := hall ⟨0, by simp⟩ (Nat.zero_le n)
      rw [List.takeWhile_cons_of_pos hx, List.length_cons]
      cases n with
      | zero => omega
      | succ n =>
          apply Nat.succ_lt_succ
          exact ih n (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hn)
            (fun j hj => by
              simpa only [List.getElem_cons_succ] using
                hall ⟨j.val + 1, by have := j.isLt; simp only [List.length_cons]; omega⟩
                  (show j.val + 1 ≤ n + 1 by omega))

private theorem incoming_continues_of_start (z : SourceInput p) (k : Fin (R z).length)
    (r : Registers p rate.eta) (q : OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hc : (R z)[k.val].input.state.coordinator = .live r q base)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val (R z)[k.val].input.time
      r.priorClock r.pendingAtChoice = .ok started) (hu : started.clock.u = none) :
    handoverIncomingLiveContinues rate rewards C_star C_h (R z)[k.val].input.time z = true := by
  unfold handoverIncomingLiveContinues ReferenceSourcePrefixHistoryFiltration.incoming
  rw [actual_at_index rate rewards C_star C_h z k]
  simp only [Option.map_some, optionalElim, encodeState, hc, encodeCoordinator,
    encodeLive, handoverIncomingLiveContinuesCode]
  change (match CoordinatorPhaseClock.startRound p rate.eta.val (R z)[k.val].input.time
    r.priorClock r.pendingAtChoice with
    | .error _ => false | .ok result => decide (result.clock.u = none)) = true
  rw [hs]
  exact decide_eq_true hu

private theorem actual_live_birth (z : SourceInput p) (ell : Fin p.T)
    (k : Fin (R z).length) (r : Registers p rate.eta) (q : OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (hc : (R z)[k.val].input.state.coordinator = .live r q base)
    (hσ : r.payload.sigma = ell) : r.priorClock.u = none ∧
    ∃ b : Fin (R z).length, (R z)[b.val].input.time = ell ∧ InstallationBirth (R z)[b.val] r.payload := by
  obtain ⟨crossing, hspan, hrecord⟩ :=
    ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h z k
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h crossing
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h crossing
  have hstored : storedPayload (ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (S z) k.val
      (by omega) seed.activeAtStart).finalState.coordinator = some r.payload := by
    change storedPayload (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (S z) k.val hspan
      seed.activeAtStart).input.state.coordinator = some r.payload
    rw [← hrecord, List.get_eq_getElem, hc]
    rfl
  have hseed : ReferenceCoordinatorClockDomains.clockAt z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) (S z) initial := by
    have hf : initial.coordinator = .first := seed.coordinatorFirst
    simp only [ReferenceCoordinatorClockDomains.clockAt, hf]
  have hclock := (ReferenceRunClockPreservation.run_clockAt initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (S z) k.val
    (by omega) seed.activeAtStart hseed).1
  change ReferenceCoordinatorClockDomains.clockAt _ _ _
    (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (S z) k.val hspan
      seed.activeAtStart).input.state at hclock
  rw [← hrecord, List.get_eq_getElem] at hclock
  simp only [ReferenceCoordinatorClockDomains.clockAt, hc] at hclock
  refine ⟨hclock.2.2.2.1, ?_⟩
  obtain ⟨birth, hm, hb, ht, _hlo, _hhi⟩ :=
    ReferenceAssignmentPayloadChronology.run_prefix_storedPayload_has_birth initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (S z) k.val (by omega)
      seed.activeAtStart seed.coordinatorFirst k.val le_rfl r.payload hstored
  have htotal := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch rate z rewards
    C_star C_h initial (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate z rewards C_star C_h crossing)
  have hsT := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hrem : k.val + (p.T - S z - k.val) = p.T - S z := by omega
  obtain ⟨tail, hrecords⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (S z) k.val
    (p.T - S z - k.val) (by omega) seed.activeAtStart
  have hfull : (R z) = (ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (S z) k.val
      (by omega) seed.activeAtStart).records ++ tail := by
    simpa only [hrem, htotal] using hrecords
  have hmR : birth ∈ R z := by rw [hfull]; exact List.mem_append_left _ hm
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hmR
  refine ⟨⟨j, hj⟩, ?_, he ▸ hb⟩
  apply Fin.ext
  change (R z)[j].input.time.val = ell.val
  rw [he, ht, hσ]

private theorem past_live_tests (z : SourceInput p) (ell : Fin p.T) (i : Fin (p.m - 1))
    (n : ℕ) (hn : n < (R z).length) (r : Registers p rate.eta) (q : OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (hc : (R z)[n].input.state.coordinator = .live r q base)
    (hσ : r.payload.sigma = ell) (hi : i ∈ r.pendingAtChoice)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen (R z)[n].input = false)
    (v : Fin (R z).length) (hv : v.val ≤ n) (hb : ell.val < (R z)[v.val].input.time.val) :
    continuingTest (R z)[v.val] = true ∧ missingAtChoice (R z)[v.val] = true := by
  induction n using Nat.strong_induction_on generalizing r q base with
  | h n ih =>
    obtain ⟨ht, selected, hs, _hp, hm⟩ :=
      ReferencePostReplacementCollectionHandoverSourcePrefix.actual_live_continuing_pending
        rate rewards C_star C_h z ⟨n, hn⟩ r q base hc hcut
    by_cases hvn : v.val = n
    · have hm' : missingAtChoice (R z)[n] = true := by
        simp only [missingAtChoice, hs]
        exact decide_eq_true ⟨i, hm ▸ hi⟩
      simpa only [hvn] using And.intro ht hm'
    have hprev : n - 1 < (R z).length := by omega
    have hsucc : n - 1 + 1 = n := by omega
    have hadj := complete_adjacent (rate := rate) rewards C_star C_h z (n - 1) (by omega)
    have hadj' : (R z)[n].input.state = (R z)[n - 1].output.next := by
      simpa only [hsucc] using hadj
    have hout : (step (R z)[n - 1].input).next.coordinator = .live r q base := by
      rw [← (R z)[n - 1].output_eq]
      exact (congrArg State.coordinator hadj').symm.trans hc
    have htime := completeSuffixRecord_time rate rewards C_star C_h z ⟨n - 1, hprev⟩
    change (R z)[n - 1].input.time.val = S z + (n - 1) at htime
    have hvtime := completeSuffixRecord_time rate rewards C_star C_h z v
    obtain ⟨old, owned, oldBase, hstate, hstamp, started, hstart, hframe,
        _hclock, hsub, _hσclock, hu⟩ :=
      ReferenceLocalReleaseGateChronology.step_old_live_predecessor
        (R z)[n - 1].input ell.val r q base hout (congrArg Fin.val hσ) (by omega)
    have hnone := (actual_live_birth rate rewards C_star C_h z ell ⟨n, hn⟩ r q base hc hσ).1
    have hstarted : started.clock.u = none :=
      (congrArg CoordinatorPhaseClock.ClockRegisters.u hframe.1).trans (hu.symm.trans hnone)
    have hcont := incoming_continues_of_start rate rewards C_star C_h z ⟨n - 1, hprev⟩
      old owned oldBase hstate started
      (by simpa only [Registers.clockPending_eq] using hstart) hstarted
    have hcode := live_continues_eq_notCutoff rate rewards C_star C_h z (R z)[n - 1].input.time
      ⟨n - 1, hprev⟩ (actual_at_index rate rewards C_star C_h z ⟨n - 1, hprev⟩) rfl old owned oldBase hstate
    exact ih (n - 1) (by omega) hprev old owned oldBase hstate (Fin.ext hstamp) (hsub hi)
      (of_decide_eq_true (hcode.symm.trans hcont)) (by omega) hb

private theorem birth_selection_univ (ell : Fin p.T) (z : SourceInput p) (hb : birthAt ell z) :
    ∃ (record : Record rate) (selected : Selection record.input),
      lookup ell z = some record ∧ record.output.preparation.coordinator.selection = some selected ∧
      selected.view.pendingAtChoice = Finset.univ := by
  rcases hb with hi | hl
  · obtain ⟨record, hr, hf, _ht, _hs⟩ := hi
    refine ⟨record, ReferenceFirstDispatchMeasurability.firstSelectionAt record.input, hr, ?_, rfl⟩
    rw [ReferenceFirstReplacementCollectionPendingFoundation.preparation_eq]
    exact ReferenceFirstDispatchMeasurability.dispatch_first_selection record.input hf
  · obtain ⟨record, selected, hr, hs, hp, _⟩ :=
      laterBirthAt_unoccupied_pending_univ rate rewards C_star C_h ell z hl
    exact ⟨record, selected, hr, hs, hp⟩

private theorem birth_of_record (ell : Fin p.T) (z : SourceInput p) (b : Fin (R z).length)
    (ht : (R z)[b.val].input.time = ell) (payload : Payload rate)
    (hb : InstallationBirth (R z)[b.val] payload) : birthAt ell z := by
  have hr : lookup ell z = some (R z)[b.val] := ht ▸ actual_at_index rate rewards C_star C_h z b
  by_cases hf : (R z)[b.val].input.state.coordinator = .first
  · exact Or.inl ((initialBirthAt_iff_actual_first rate rewards C_star C_h ell z).mpr ⟨_, hr, hf⟩)
  have hp := ReferenceFirstReplacementCollectionPendingFoundation.preparation_eq (R z)[b.val]
  have hl : ReferenceCollectionPhaseHistory.laterChosen (R z)[b.val].input = true := by
    cases hpc : (R z)[b.val].output.preparation.coordinator with
    | first outcome =>
        have hd : dispatch (R z)[b.val].input = .first outcome := by
          rw [← (prepare (R z)[b.val].input).coordinator_eq, ← hp, hpc]
        cases hc : (R z)[b.val].input.state.coordinator with
        | first => exact (hf hc).elim
        | live _ _ _ => simp only [dispatch, hc, CoordinatorRoundDispatch.dispatch] at hd; cases hd
        | collection _ _ _ => simp only [dispatch, hc] at hd; split at hd <;> cases hd
        | dagger => simp only [dispatch, hc] at hd; cases hd
    | collection old ledger clock cutoff outcome =>
        cases outcome <;> simp only [InstallationBirth, hpc] at hb
        unfold ReferenceCollectionPhaseHistory.laterChosen
        rw [← hp, hpc]
    | live _ _ _ _ => simp only [InstallationBirth, hpc] at hb
    | invalidCollectionCutoff => simp only [InstallationBirth, hpc] at hb
    | dagger => simp only [InstallationBirth, hpc] at hb
  cases hc : (R z)[b.val].input.state.coordinator with
  | collection old ledger saved =>
      have he := (ReferencePostReplacementCollectionHandoverSourcePrefix.actual_collection_laterChosen_iff_pending_empty
        rate rewards C_star C_h z b old ledger saved hc).mp hl
      exact Or.inr ((laterBirthAt_iff_actual_empty_collection rate rewards C_star C_h ell z).mpr
        ⟨_, old, ledger, saved, hr, hc, he⟩)
  | first => exact (hf hc).elim
  | live _ _ _ => simp only [ReferenceCollectionPhaseHistory.laterChosen, prepare, dispatch, hc,
      CoordinatorRoundDispatch.dispatch] at hl; cases hl
  | dagger => simp only [ReferenceCollectionPhaseHistory.laterChosen, prepare, dispatch, hc] at hl; cases hl

/-- Every actual birth starts with every follower missing. -/
public theorem installationBirthAt_rawPending (ell : Fin p.T) (z : SourceInput p)
    (hb : birthAt ell z) (i : Fin (p.m - 1)) : rawTask ell ell i z := by
  obtain ⟨record, selected, hr, hs, hpend⟩ := birth_selection_univ rate rewards C_star C_h ell z hb
  have hi : i ∈ selected.view.pendingAtChoice := hpend ▸ Finset.mem_univ i
  have hm : missingAtChoice record = true := by
    simp only [missingAtChoice, hs]
    exact decide_eq_true ⟨i, hi⟩
  rcases hb with hb | hb
  · obtain ⟨birth, hbirth, hf, ht, hstart⟩ := hb
    have he : record = birth := Option.some.inj (hr.symm.trans hbirth)
    subst birth
    obtain ⟨b, _hb, he, _ht⟩ := actualRecord_index rate rewards C_star C_h ell z record hr
    have hz := first_index_zero rate rewards C_star C_h z b (he ▸ hf)
    have hR : 0 < (R z).length := by have := b.isLt; omega
    have hzero : (R z)[0] = record := by simpa only [hz] using he
    have hcut : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
      unfold ReferenceCollectionPhaseHistory.cutoffChosen
      rw [(prepare record.input).coordinator_eq, dispatch_first record.input hf]
    have hW : 0 < (W z).length := by
      rw [raw_window_eq_complete_suffix_takeWhile]
      change 0 < ((R z).takeWhile _).length
      exact takeWhile_index _ _ 0 hR (fun j hj => by
        have hj0 : j.val = 0 := by omega
        simp only [hj0, hzero, hcut, Bool.not_false])
    have hget : (W z)[0] = record := by
      have hprefix : (W z).IsPrefix (R z) := by
        rw [raw_window_eq_complete_suffix_takeWhile]; exact List.takeWhile_prefix _
      exact (hprefix.getElem hW).trans hzero
    have hmissing : 0 < rawMissingPrefixLength rate rewards C_star C_h z :=
      takeWhile_index (W z) missingAtChoice 0 hW (fun j hj => by
        have hj0 : j.val = 0 := by omega
        simpa only [hj0, hget] using hm)
    refine Or.inl ⟨record, hr, hf, ht, hstart, ⟨0, hW⟩, hmissing, ?_⟩
    change (W z)[0].input.time = ell ∧ _
    rw [hget]
    exact ⟨ht, selected, hs, hi⟩
  · obtain ⟨b, hb, ht, hlookup, old, ledger, saved, hc, he, installed, hinst⟩ := hb
    have hrecord : (R z)[b.val] = record := Option.some.inj (hlookup.symm.trans hr)
    have hm' : missingAtChoice (R z)[b.val] = true := hrecord ▸ hm
    have hlen : 0 < (Handover z b).length := by
      simp only [actualHandoverRecords, List.takeWhile_cons, hm', ↓reduceIte, List.length_cons]
      omega
    have hget : (Handover z b)[0] = record := by
      simp only [actualHandoverRecords, List.takeWhile_cons, hm', ↓reduceIte, List.getElem_cons_zero]
      exact hrecord
    refine Or.inr ⟨b, hb, ht, hlookup, old, ledger, saved, hc, he, installed, hinst, ⟨0, hlen⟩, ?_⟩
    change (Handover z b)[0].input.time = ell ∧ _
    rw [hget]
    exact ⟨hrecord ▸ ht, selected, hs, hi⟩

/-- The genuine pre-round query reconstructs its own birth and completed-list H membership on. -/
public theorem preRoundRequest_rawPending (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : SourceInput p) (hrequest : preRoundRequest rate rewards C_star C_h ell t i z) :
    rawTask ell t i z := by
  rcases hrequest with ⟨rfl, hb⟩ | ⟨hlt, hlive, hcontinue⟩
  · exact installationBirthAt_rawPending rate rewards C_star C_h ell z
      ((birthReady_iff rate rewards C_star C_h ell z).mp hb) i
  unfold liveRequest ReferenceSourcePrefixHistoryFiltration.incoming at hlive
  cases hr : lookup t z with
  | none => simp only [hr, optionalElim] at hlive; cases hlive
  | some record =>
    rw [hr] at hlive
    cases hc : record.input.state.coordinator with
    | first => simp [optionalElim, encodeState, encodeCoordinator, liveRequestCode, hc] at hlive
    | collection _ _ _ => simp [optionalElim, encodeState,
        encodeCoordinator, liveRequestCode, hc] at hlive
    | dagger => simp [optionalElim, encodeState, encodeCoordinator, liveRequestCode, hc] at hlive
    | live r owned base =>
      simp only [optionalElim, Option.map_some, encodeState, hc, encodeCoordinator,
        encodeLive, liveRequestCode, decide_eq_true_eq] at hlive
      obtain ⟨k, _hk, he, ht⟩ := actualRecord_index rate rewards C_star C_h t z record hr
      have hstate : (R z)[k.val].input.state.coordinator = .live r owned base := he ▸ hc
      have hclock := live_continues_eq_notCutoff rate rewards C_star C_h z t k
        (by rw [he]; exact hr) (by rw [he]; exact ht) r owned base hstate
      have hcut := of_decide_eq_true (hclock.symm.trans hcontinue)
      obtain ⟨_hnone, b₀, hb₀, hborn⟩ := actual_live_birth rate rewards C_star C_h z ell k r owned base hstate hlive.1
      have hbirth := birth_of_record rate rewards C_star C_h ell z b₀ hb₀ r.payload hborn
      have hpast := past_live_tests rate rewards C_star C_h z ell i k.val k.isLt
        r owned base hstate hlive.1 hlive.2 hcut
      obtain ⟨hct, current, hcurrent, _hpayload, hpending⟩ :=
        ReferencePostReplacementCollectionHandoverSourcePrefix.actual_live_continuing_pending
          rate rewards C_star C_h z k r owned base hstate hcut
      have him : i ∈ current.view.pendingAtChoice := hpending ▸ hlive.2
      have htime := completeSuffixRecord_time rate rewards C_star C_h z k
      rw [he, ht] at htime
      have hbirthTask := installationBirthAt_rawPending rate rewards C_star C_h ell z hbirth i
      rcases hbirthTask with ⟨birth, hb, hf, hbt, hstart, j₀, _hj₀, _ht₀, _⟩ |
        ⟨b, hb, hbt, hlookup, old, ledger, saved, hcollection, hempty, installed, hinst, j₀, _ht₀, _⟩
      · have hprefix : (W z).IsPrefix (R z) := by
          rw [raw_window_eq_complete_suffix_takeWhile]; exact List.takeWhile_prefix _
        have hbornIndex := actualRecord_index rate rewards C_star C_h ell z birth hb
        obtain ⟨b, _hbi, hbe, _⟩ := hbornIndex
        have hbzero := first_index_zero rate rewards C_star C_h z b (hbe ▸ hf)
        have hzero : (R z)[0]'(by have := b.isLt; omega) = birth := by simpa only [hbzero] using hbe
        have hfirstCut : ReferenceCollectionPhaseHistory.cutoffChosen birth.input = false := by
          unfold ReferenceCollectionPhaseHistory.cutoffChosen
          rw [(prepare birth.input).coordinator_eq, dispatch_first birth.input hf]
        have hWk : k.val < (W z).length := by
          rw [raw_window_eq_complete_suffix_takeWhile]
          change k.val < ((R z).takeWhile _).length
          apply takeWhile_index _ _ k.val k.isLt
          intro q hq
          by_cases hq0 : q.val = 0
          · simp only [hq0, hzero, hfirstCut, Bool.not_false]
          · have hqtime := completeSuffixRecord_time rate rewards C_star C_h z q
            have hcq := (hpast q hq (by omega)).1
            rw [continuing_not_cutoff rate _ hcq]
            rfl
        have hmissing : k.val < rawMissingPrefixLength rate rewards C_star C_h z := by
          apply takeWhile_index (W z) missingAtChoice k.val hWk
          intro q hq
          have hqR : q.val < (R z).length := lt_of_lt_of_le q.isLt hprefix.length_le
          rw [hprefix.getElem q.isLt]
          by_cases hq0 : q.val = 0
          · simp only [hq0, hzero]
            obtain ⟨born, selected, hborn, hs, hm⟩ := birth_selection_univ rate rewards C_star C_h ell z hbirth
            have hbornEq := Option.some.inj (hb.symm.trans hborn)
            subst born
            simp only [missingAtChoice, hs, hm]
            exact decide_eq_true ⟨i, Finset.mem_univ i⟩
          · have hqtime := completeSuffixRecord_time rate rewards C_star C_h z ⟨q.val, hqR⟩
            change (R z)[q.val].input.time.val = S z + q.val at hqtime
            exact (hpast ⟨q.val, hqR⟩ hq (by change ell.val < (R z)[q.val].input.time.val; omega)).2
        refine Or.inl ⟨birth, hb, hf, hbt, hstart, ⟨k.val, hWk⟩, hmissing, ?_⟩
        rw [hprefix.getElem hWk]
        exact ⟨he ▸ ht, current, hcurrent, him⟩
      · have hlookup₀ : lookup ell z = some (R z)[b₀.val] :=
          hb₀ ▸ actual_at_index rate rewards C_star C_h z b₀
        have hsameBirth := Option.some.inj (hlookup.symm.trans hlookup₀)
        have hactualBirth : InstallationBirth (R z)[b.val] r.payload := by rw [hsameBirth]; exact hborn
        have hactualPayload := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
          (R z)[b.val] installed r.payload hinst hactualBirth
        have hbtime := completeSuffixRecord_time rate rewards C_star C_h z b
        rw [hbt] at hbtime
        have hbk : b.val < k.val := by omega
        let tail := (R z).drop (b.val + 1)
        let n := k.val - b.val - 1
        have hn : n < tail.length := by dsimp only [n, tail]; simp only [List.length_drop]; omega
        have htests : n < (tail.takeWhile (fun row => missingAtChoice row && continuingTest row)).length := by
          apply takeWhile_index tail _ n hn
          intro q hq
          have hqR : b.val + 1 + q.val < (R z).length := by
            have := q.isLt
            dsimp only [tail] at this
            simp only [List.length_drop] at this
            omega
          have hqtime := completeSuffixRecord_time rate rewards C_star C_h z ⟨b.val + 1 + q.val, hqR⟩
          have hqk : b.val + 1 + q.val ≤ k.val := by dsimp only [n] at hq; omega
          change (R z)[b.val + 1 + q.val].input.time.val = S z + (b.val + 1 + q.val) at hqtime
          have hs := hpast ⟨b.val + 1 + q.val, hqR⟩ hqk
            (by change ell.val < (R z)[b.val + 1 + q.val].input.time.val; omega)
          change (missingAtChoice ((R z).drop (b.val + 1))[q.val] &&
            continuingTest ((R z).drop (b.val + 1))[q.val]) = true
          simpa only [List.getElem_drop, Bool.and_eq_true] using And.intro hs.2 hs.1
        obtain ⟨born, selected, hborn, hs, hm⟩ := birth_selection_univ rate rewards C_star C_h ell z hbirth
        have hbornEq := Option.some.inj (hlookup.symm.trans hborn)
        have hmBirth : missingAtChoice (R z)[b.val] = true := by
          rw [hbornEq]
          simp only [missingAtChoice, hs, hm]
          exact decide_eq_true ⟨i, Finset.mem_univ i⟩
        have hj : k.val - b.val < (Handover z b).length := by
          simp only [actualHandoverRecords, List.takeWhile_cons, hmBirth, ↓reduceIte,
            continuingPrefix, List.takeWhile_takeWhile, Bool.decide_and, Bool.decide_coe, List.length_cons]
          change k.val - b.val < (tail.takeWhile (fun row => missingAtChoice row && continuingTest row)).length + 1
          dsimp only [n] at htests
          omega
        let j : Fin (Handover z b).length := ⟨k.val - b.val, hj⟩
        obtain ⟨_hk, hget⟩ := actualHandover_index rate rewards C_star C_h z b j
        have hsum : b.val + j.val = k.val := by dsimp only [j]; omega
        have hget' : (Handover z b)[j.val] = (R z)[k.val] := by
          simpa only [hsum] using hget
        refine Or.inr ⟨b, hb, hbt, hlookup, old, ledger, saved, hcollection, hempty, r.payload, hactualPayload ▸ hinst, j, ?_⟩
        rw [hget']
        exact ⟨he ▸ ht, current, hcurrent, him⟩

/-- Completed-list support and the genuine row-free pre-round test coincide. -/
public theorem rawPending_iff_preRoundRequest (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    rawTask ell t i z ↔ preRoundRequest rate rewards C_star C_h ell t i z :=
  ⟨rawPending_preRoundRequest rate rewards C_star C_h ell t i z,
    preRoundRequest_rawPending rate rewards C_star C_h ell t i z⟩

public theorem rawPending_factor (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    rawTask ell t i z ↔ rawTask ell t i (sourcePrefix control0 t.val z) := by
  rw [rawPending_iff_preRoundRequest, rawPending_iff_preRoundRequest]
  exact preRoundRequest_factor rate rewards C_star C_h control0 ell t i z

public theorem rawPending_measurableSet (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] {z | rawTask ell t i z} := by
  simp_rw [rawPending_iff_preRoundRequest]
  exact preRoundRequest_measurableSet rate rewards C_star C_h control0 ell t i

public theorem pending_factor (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    task ell t i z ↔ task ell t i (sourcePrefix control0 t.val z) := by
  unfold pending
  rw [ReferenceOriginalFirstBadStrictPrefix.firstBadDate_inclusive_prefix_factor
    rate rewards C_star C_h control0 t z, rawPending_factor rate rewards C_star C_h control0 ell t i z]

public theorem pending_measurableSet (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] {z | task ell t i z} := by
  have hm := ReferenceOriginalFirstBadStrictPrefix.noBadEventStrictlyBefore_strictPrefix_measurable
    rate rewards C_star C_h control0 t
  have hbad : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      {z | t.val + 1 ≤ bad z} := by
    simpa only [ReferenceOriginalFirstBadStrictPrefix.firstBadDate_prefix_iff] using hm
  exact hbad.inter (rawPending_measurableSet rate rewards C_star C_h control0 ell t i)

public theorem pending_replaceSourceControl (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) : task ell t i z ↔ task ell t i
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) := by
  rw [pending_factor rate rewards C_star C_h control0 ell t i z,
    pending_factor rate rewards C_star C_h control0 ell t i
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)]
  rw [ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current control0 t z control]

/-- Raw theta is a stopping time before masking, including absence and the horizon sentinel. -/
public theorem rawTheta_preRoundStoppingTime (control0 : ContinuousLearningRows.TimeControl p)
    (ell : Fin p.T) : PhaseServiceWaiting.IsPreRoundStoppingTime (sourcePrefixFiltration control0)
      (thetaH ell) := by
  intro n
  by_cases hT : p.T + 1 ≤ n
  · have heq : {z | thetaH ell z ≤ n} = Set.univ := by
      ext z
      exact iff_true_intro ((rawEndpoints_bounds rate rewards C_star C_h ell z).2.2.trans hT)
    rw [heq]
    exact MeasurableSet.univ
  by_cases hn : 1 ≤ n
  · let t : Fin p.T := ⟨n - 1, by omega⟩
    have hdate : t.val + 1 = n := Nat.sub_add_cancel hn
    have hm : MeasurableSet[sourcePrefixFiltration control0 n] {z | ∃ i, rawTask ell t i z} := by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun i =>
        ((sourcePrefixFiltration control0).mono (Nat.le_of_eq hdate))
          _ (rawPending_measurableSet rate rewards C_star C_h control0 ell t i)
    have hσ := rawSigma_preRoundStoppingTime rate rewards C_star C_h control0 ell n
    convert hσ.inter hm.compl using 1
    ext z
    exact rawTheta_le_iff_current_empty rate rewards C_star C_h ell z n hn (by omega)
  · have heq : {z | thetaH ell z ≤ n} = ∅ := by
      ext z
      have hb := rawEndpoints_bounds rate rewards C_star C_h ell z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      exact iff_false_intro (by intro h; have hlo := hb.1.trans hb.2.1; omega)
    rw [heq]
    exact @MeasurableSet.empty _ (sourcePrefixFiltration control0 n)

/-- BEFORE and AFTER use the actual lifecycle status at CHOICE. -/
public def before (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) : Prop :=
  task ell t i z ∧ preRoundStatus rate rewards C_star C_h t i z = some 0

public def after (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) : Prop :=
  task ell t i z ∧ preRoundStatus rate rewards C_star C_h t i z = some 1

public theorem stages_factor (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    (before rate rewards C_star C_h ell t i z ↔ before rate rewards C_star C_h ell t i
      (sourcePrefix control0 t.val z)) ∧
    (after rate rewards C_star C_h ell t i z ↔ after rate rewards C_star C_h ell t i
      (sourcePrefix control0 t.val z)) := by
  unfold before after
  rw [pending_factor rate rewards C_star C_h control0 ell t i z,
    preRoundStatus_factor rate rewards C_star C_h control0 t i z]
  exact ⟨Iff.rfl, Iff.rfl⟩

public theorem stages_measurableSet (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      {z | before rate rewards C_star C_h ell t i z} ∧
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      {z | after rate rewards C_star C_h ell t i z} :=
  ⟨(pending_measurableSet rate rewards C_star C_h control0 ell t i).inter
      ((preRoundStatus_measurable rate rewards C_star C_h control0 t i) (measurableSet_singleton (some 0))),
    (pending_measurableSet rate rewards C_star C_h control0 ell t i).inter
      ((preRoundStatus_measurable rate rewards C_star C_h control0 t i) (measurableSet_singleton (some 1)))⟩

public theorem stages_replaceSourceControl (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    (before rate rewards C_star C_h ell t i z ↔ before rate rewards C_star C_h ell t i
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)) ∧
    (after rate rewards C_star C_h ell t i z ↔ after rate rewards C_star C_h ell t i
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)) := by
  have hp := ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current control0 t z control
  have h₁ := stages_factor rate rewards C_star C_h control0 ell t i z
  have h₂ := stages_factor rate rewards C_star C_h control0 ell t i
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)
  rw [hp] at h₂
  exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩

/-- Initial birth has universal pending and actual unoccupied CHOICE status. -/
public theorem initialBirthAt_unoccupied_pending_univ (ell : Fin p.T) (z : SourceInput p)
    (hb : initialAt ell z) :
    ∃ (record : Record rate) (selected : Selection record.input), lookup ell z = some record ∧
      record.output.preparation.coordinator.selection = some selected ∧
      selected.view.pendingAtChoice = Finset.univ ∧
      ∀ i : Fin (p.m - 1), preRoundStatus rate rewards C_star C_h ell i z = some 0 := by
  obtain ⟨record, selected, hr, hs, hpend⟩ :=
    birth_selection_univ rate rewards C_star C_h ell z (Or.inl hb)
  obtain ⟨birth, hbirth, hf, _ht, _hstart⟩ := hb
  have he := Option.some.inj (hr.symm.trans hbirth)
  subst birth
  obtain ⟨k, _hk, hrecord, _ht⟩ := actualRecord_index rate rewards C_star C_h ell z record hr
  have hkzero := first_index_zero rate rewards C_star C_h z k (hrecord ▸ hf)
  obtain ⟨crossing, _hspan, hprefix⟩ :=
    ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h z k
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h crossing
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h crossing
  have hstate : record.input.state = initial := by
    rw [← hrecord, ← List.get_eq_getElem, hprefix]
    change (ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (S z) k.val
      _ seed.activeAtStart).finalState = initial
    simpa only [hkzero] using ReferenceActivePhysicalHorizon.run_zero_final initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards (S z)
      (by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h; omega)
      seed.activeAtStart
  refine ⟨record, selected, hr, hs, hpend, fun i => ?_⟩
  have hin : record.input.state.followers i = .ordinary (seed.followers i) (seed.memory i) := by
    rw [hstate]
    exact seed.configuration i
  unfold preRoundStatus
  rw [ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_at_ordinary
    rate rewards C_star C_h ell i z record (seed.followers i) (seed.memory i) hr hin,
    ActiveFollowerLifecycle.startRound_unoccupied rate.eta ell (seed.followers i) (seed.memory i)
      (seed.localStateDomain i) (seed.unoccupied i)]
  change some (followerStatusCode (seed.followers i).status) = some 0
  rw [seed.unoccupied i]
  rfl

public theorem pending_nonempty_iff_interval (ell t : Fin p.T) (z : SourceInput p) :
    (∃ i, task ell t i z) ↔ t.val + 1 ≤ bad z ∧ sigmaH ell z ≤ t.val + 1 ∧
      t.val + 1 < thetaH ell z := by
  simp only [pending, exists_and_left, rawPending_nonempty_iff_interval]

/-- Original transfer rank, actual collection exit, and this fixed-calendar
H projection share the same birth, payload, raw endpoints and stopped dates.
The absent and terminal-collection branches are retained explicitly. -/
public theorem retained_transfer_handover (k : Fin (p.T + 1)) (z : SourceInput p) :
    let start := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z
    let E := ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
      rate rewards C_star C_h k z
    start > p.T ∨ ∃ a : Fin (R z).length, start = S z + a.val + 1 ∧
      (initialAt (R z)[a.val].input.time z ∨
       ∃ seg : ReferenceCollectionSegmentExtraction.Segment rate,
        ReferenceCollectionSegmentExtraction.segmentAt (R z) a.val = some seg ∧
        (a.val + seg.records.length = (R z).length ∨
         ∃ b : Fin (R z).length, b.val = a.val + seg.records.length ∧ laterAt (R z)[b.val].input.time z ∧
          ∃ newPayload : Payload rate, InstallationBirth (R z)[b.val] newPayload ∧
           sigmaH (R z)[b.val].input.time z = S z + b.val + 1 ∧
           thetaH (R z)[b.val].input.time z = S z + b.val + (Handover z b).length + 1 ∧
           ∀ t : Fin p.T, ((∃ i, task (R z)[b.val].input.time t i z) ∧ t.val + 1 < E) ↔
             sigmaH (R z)[b.val].input.time z ≤ t.val + 1 ∧
               t.val + 1 < min (thetaH (R z)[b.val].input.time z) E)) := by
  intro start E
  by_cases hk : start ≤ p.T
  · obtain ⟨a, ha, hbranch⟩ :=
      ReferenceOriginalStoppedTransferPhaseIntervals.present_stopped_transfer_collection_intervals
        rate rewards C_star C_h k z hk
    refine Or.inr ⟨a, ha, ?_⟩
    rcases hbranch with ⟨_ha0, hf, _hc⟩ |
      ⟨registers, owned, base, seg, _hstate, hseg, _hentry, _hpay, _hne,
        _hrows, _hlookups, _hdates, hboundary⟩
    · exact Or.inl ((initialBirthAt_iff_actual_first rate rewards C_star C_h _ z).mpr
        ⟨_, actual_at_index rate rewards C_star C_h z a, hf⟩)
    · refine Or.inr ⟨seg, hseg, ?_⟩
      rcases hboundary with hterminal | ⟨b, hb, _hlater, _hexit, ⟨saved, hcoord⟩, hempty,
          _hV, _hE, hcut, _hmask, newPayload, hnew, _hrows, _hlookup, _hH, _hR, _hnull, _hclear⟩
      · exact Or.inl hterminal.1
      · have hlookup := actual_at_index rate rewards C_star C_h z b
        have htime := completeSuffixRecord_time rate rewards C_star C_h z b
        have hindex : b.val = (R z)[b.val].input.time.val - S z := by omega
        have hl : laterAt (R z)[b.val].input.time z :=
          ⟨b, hindex, rfl, hlookup, registers.payload, seg.final, saved,
            hcoord, hempty, newPayload, hnew⟩
        have hn := fun hi => initialBirthAt_not_laterBirthAt rate rewards C_star C_h _ z hi hl
        have hsegment := laterBirthSegment_eq rate rewards C_star C_h _ z b hindex hlookup
          registers.payload seg.final saved hcoord hempty
        refine Or.inr ⟨b, hb, hl, newPayload, hnew, ?_, ?_, ?_⟩
        · rw [rawSigma, ite_eq_left (show birthAt _ z from Or.inr hl), htime]
        · rw [rawTheta, ite_eq_right hn, ite_eq_left hl, hsegment, htime]
        · intro t
          rw [pending_nonempty_iff_interval]
          have hbad := (hcut (t.val + 1)).mp
          simp only [lt_min_iff]
          constructor
          · rintro ⟨⟨_hbad, hs, ht⟩, hE⟩
            exact ⟨hs, ht, hE⟩
          · rintro ⟨hs, ht, hE⟩
            exact ⟨⟨(hbad hE).2, hs, ht⟩, hE⟩
  · exact Or.inl (Nat.lt_of_not_ge hk)

end Bandits.Support.ReferenceOriginalFixedInstallationHandoverSupport

end
