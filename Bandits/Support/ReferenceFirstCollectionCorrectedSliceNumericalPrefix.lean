/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedNextRetainedMoment

import Mathlib.Tactic

/-!
# Original-source corrected numerical slice

The optional prefix uses every original physical record from launch. The
endpoint includes the continuing LIVE tail after the first replacement birth
and, only when its actual constructor is selected, the first cutoff update.
The queue is inherited from launch and is never reset at the replacement.

Sources: `04_slow_fast_learner.tex:140-188,245-290`,
`05_binary_transport.tex:354-431`, and `06_interruptions.tex:9-14,31-100,355-426`
under `sources/zip4/manuscript/`. These are internal deterministic results.
-/

@[expose] public section
noncomputable section

open Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open ReferenceSourcePrefixHistoryFiltration (actualLaunchBy actualRecord)
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCorrectedSliceNumericalPrefix

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
local notation "Input" => RecordedQueueRun.RoundInput p.K
local notation "Readout" => ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K

/-- The original corrected first-call event, including its actual old freeze witness. -/
def correctedCell (u t : Fin p.T) : Set X :=
  {x | x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t ∧
    ∃ g, ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
      rate rewards C_star C_h t x = some g ∧ t.val + 1 < g}

/-- The entire original suffix, retaining the original private source and whole rewards. -/
def sourceRecords (x : X) : List Record :=
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h

/-- The original launch origin, including the no-launch terminal convention. -/
def sourceStart (x : X) : ℕ :=
  ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h

/-- The first replacement index in the original physical suffix. -/
def birthIndex (x : X) : ℕ :=
  let R := sourceRecords rate rewards C_star C_h x
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length

/-- The actual finite continuing LIVE tail, with no assumed successful endpoint. -/
def liveTail (x : X) : List Record :=
  ReferenceFirstReplacementLiveFollowerPrefix.continuingTail
    (sourceRecords rate rewards C_star C_h x) (birthIndex rate rewards C_star C_h x)

/-- Exactly one extra update for an actual first selected cutoff, zero for all other outcomes. -/
def cutoffDelta (x : X) : ℕ :=
  match (sourceRecords rate rewards C_star C_h x)[birthIndex rate rewards C_star C_h x +
      1 + (liveTail rate rewards C_star C_h x).length]? with
  | some r => match r.output.preparation.coordinator with
    | .live _ _ _ (.cutoffChosen ..) => 1
    | _ => 0
  | none => 0

/-- The numerical boundary after the continuing tail and at most its first cutoff update. -/
def endDate (t : Fin p.T) (x : X) : ℕ :=
  t.val + 1 + (liveTail rate rewards C_star C_h x).length +
    cutoffDelta rate rewards C_star C_h x

/-- Every original slot must be present; absent optional cells are never dropped. -/
def prefixInputs (n : ℕ) (x : X) : Option (List Input) :=
  if actualLaunchBy rate rewards C_star C_h n x then
    (((sourceRecords rate rewards C_star C_h x).take
      (n - sourceStart rate rewards C_star C_h x)).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id
  else none

/-- The existing initialized stopped run, observed only on a fully present prefix. -/
def prefixReadout (n : ℕ) (x : X) : Option Readout :=
  (prefixInputs rate rewards C_star C_h n x).map
    (fun inputs => stateReadout (RecordedQueueRun.run Q inputs))

/-- Literal arm-specific threshold event on this finite original-source slice. -/
def overflowEvent (u t : Fin p.T) (a : Fin p.K) : Set X :=
  {x | x ∈ correctedCell rate rewards C_star C_h u t ∧
    ∃ n, t.val + 1 ≤ n ∧ n ≤ endDate rate rewards C_star C_h t x ∧
      ∃ on, prefixReadout rate rewards C_star C_h n x = some on ∧
        ((on.1 a).2 : ℝ) / ((Q).n : ℝ) > 1 / (32 * rate.eta.val)}

private theorem live_baseline_zero (r : Record) (s : ℕ) (c : Input)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
  obtain ⟨selected, ho, hselection, hbase, hlive, hcell⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some s r c hc
  have hz : 0 < selected.view.payload.sigma.val := by omega
  unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
  simp only [hselection, hz, hlive, and_self, ite_true, dite_eq_left ho]
  exact congrArg some hcell.symm

private theorem mapM_map_some {α : Type*} (L : List α) :
    (L.map some).mapM id = some L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [List.mapM_cons, ih]

private theorem prefix_map_eq_of_coverage {α β : Type*} (R : List α)
    (f : α → Option β) (L : List β) (hN : L.length ≤ R.length)
    (h : ∀ k : Fin L.length, ∃ r, R[k.val]? = some r ∧ f r = some L[k.val]) :
    (R.take L.length).map f = L.map some := by
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left hN]
  · intro k hk hk'
    have hkL : k < L.length := by simpa using hk'
    obtain ⟨r, hr, hf⟩ := h ⟨k, hkL⟩
    have he : R[k]'(by omega) = r := (List.getElem?_eq_some_iff.mp hr).2
    simpa only [List.getElem_map, List.getElem_take, he] using hf

/-- Birth and calendar time are joined on the original first-call source. -/
theorem firstCell_birth_time (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    sourceStart rate rewards C_star C_h x + birthIndex rate rewards C_star C_h x = t.val := by
  obtain ⟨r, hr, _, ht, _⟩ :=
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_firstReplacement_record
      rate rewards C_star C_h u t x hx.1
  have htime := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate x rewards C_star C_h _ r hr
  rw [ht] at htime
  exact htime.symm

/-- The endpoint is finite, including empty tails, other endpoint constructors,
and a birth in the final physical round. -/
theorem endDate_bounds (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    t.val + 1 ≤ endDate rate rewards C_star C_h t x ∧
      endDate rate rewards C_star C_h t x ≤ p.T := by
  have htime := firstCell_birth_time rate rewards C_star C_h u t x hx
  obtain ⟨birth, hb, _, _, _⟩ :=
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_firstReplacement_record
      rate rewards C_star C_h u t x hx.1
  have hv : birthIndex rate rewards C_star C_h x <
      (sourceRecords rate rewards C_star C_h x).length :=
    (List.getElem?_eq_some_iff.mp hb).1
  have htail : (liveTail rate rewards C_star C_h x).length ≤
      (sourceRecords rate rewards C_star C_h x).length -
        (birthIndex rate rewards C_star C_h x + 1) := by
    exact (List.takeWhile_prefix _).length_le.trans (by rw [List.length_drop])
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate x rewards C_star C_h
  change (sourceRecords rate rewards C_star C_h x).length =
    p.T - sourceStart rate rewards C_star C_h x at hlen
  constructor
  · unfold endDate
    omega
  · unfold endDate cutoffDelta
    split
    · rename_i r hr
      have hi := (List.getElem?_eq_some_iff.mp hr).1
      split <;> omega
    · omega

/-- The prefix at the call successor contains the initialized strict past and
actual current cell, including a terminal successor boundary. -/
theorem firstCell_initial_inputs (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    ∃ (L : List Input) (c : Input),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t x = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t x = some c ∧
      prefixInputs rate rewards C_star C_h (t.val + 1) x = some (L ++ [c]) ∧
      L.length = t.val - sourceStart rate rewards C_star C_h x := by
  obtain ⟨birth, hb, har, ht, hchosen⟩ :=
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_firstReplacement_record
      rate rewards C_star C_h u t x hx.1
  have hlaunch : actualLaunchBy rate rewards C_star C_h t.val x := by
    by_contra hn
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t x hn] at har
    cases har
  have hlaunch' : actualLaunchBy rate rewards C_star C_h (t.val + 1) x :=
    ⟨hlaunch.1, hlaunch.2.trans (Nat.le_succ _)⟩
  obtain ⟨hc, hs, hshort, f, head, valid, D, L, _hsu, _hut, _hu, _ht,
      _hp, _hlast, _hhead, _hDlen, _hD0, _hDread, _hjoin, hL, hLlen, hcoverage⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
      rate rewards C_star C_h u t x hx.1
  have hcurrent :=
    ReferenceFirstCollectionCorrectedNextRetainedGate.firstCell_current_eq_calendar
      rate rewards C_star C_h u t x hx.1
  have hpresent := (ReferenceFirstCollectionCurrentNumericalCell.currentCell_isSome_iff
    rate rewards C_star C_h u t x hx.1).mpr ⟨birth, har, hchosen⟩
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hpresent
  have hbcell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate birth = some c := by
    simpa only [har, Option.bind_some] using hcurrent.symm.trans hc
  have htime := firstCell_birth_time rate rewards C_star C_h u t x hx
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate x rewards C_star C_h
  have hmap := prefix_map_eq_of_coverage
    (sourceRecords rate rewards C_star C_h x)
    (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) L (by
      have hs0 := hlaunch.2
      change sourceStart rate rewards C_star C_h x ≤ t.val at hs0
      change L.length = t.val - sourceStart rate rewards C_star C_h x at hLlen
      change (sourceRecords rate rewards C_star C_h x).length =
        p.T - sourceStart rate rewards C_star C_h x at hlen
      omega) (fun k => by
        obtain ⟨r, hr, _, hf⟩ := hcoverage k
        exact ⟨r, hr, hf⟩)
  have hv : birthIndex rate rewards C_star C_h x = L.length := by
    change L.length = t.val - sourceStart rate rewards C_star C_h x at hLlen
    omega
  have hget : (sourceRecords rate rewards C_star C_h x)[L.length]? = some birth := by
    rw [← hv]
    exact hb
  have hi : t.val + 1 - sourceStart rate rewards C_star C_h x = L.length + 1 := by
    change L.length = t.val - sourceStart rate rewards C_star C_h x at hLlen
    omega
  refine ⟨L, c, hL, hc, ?_, hLlen⟩
  rw [prefixInputs, ite_eq_left hlaunch', hi, List.take_add_one, hget]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
    hbcell, List.mapM_append, hmap, mapM_map_some, List.mapM_cons,
    List.mapM_nil, id_eq]
  rfl

/-- The numerical slice starts at the inherited AFTER queue, which can be nonzero. -/
theorem firstCell_readout_after (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    prefixReadout rate rewards C_star C_h (t.val + 1) x =
      ReferenceFirstCollectionCurrentQueueReadout.after? rate rewards C_star C_h t x := by
  obtain ⟨L, c, hL, hc, hinputs, _⟩ :=
    firstCell_initial_inputs rate rewards C_star C_h u t x hx
  simp only [prefixReadout, hinputs, Option.map_some,
    ReferenceFirstCollectionCurrentQueueReadout.after?, hL, hc, Option.bind_some]
  rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]

/-- Every continuing LIVE record and the selected first cutoff, when present,
produces its actual optional calendar cell. No following phase is included. -/
theorem firstCell_tail_cells (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    ∀ k < (liveTail rate rewards C_star C_h x).length + cutoffDelta rate rewards C_star C_h x,
      ∃ (r : Record) (c : Input),
        (sourceRecords rate rewards C_star C_h x)[birthIndex rate rewards C_star C_h x + 1 + k]? =
          some r ∧ ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
  obtain ⟨birth, hb, _har, _ht, hchosen⟩ :=
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_firstReplacement_record
      rate rewards C_star C_h u t x hx.1
  have hread :=
    ReferenceFirstReplacementFollowerBoundary.complete_first_replacement_continuing_live_readout
      rate x rewards C_star C_h
  have hcut :=
    ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
      rate x rewards C_star C_h
  dsimp only at hread hcut
  simp only [hb] at hread hcut
  have hp : birth.output.preparation = ReferenceActivePhysicalStep.prepare birth.input := by
    rw [birth.output_eq]
    rfl
  unfold ReferenceCollectionPhaseHistory.laterChosen at hchosen
  rw [← hp] at hchosen
  cases hcoord : birth.output.preparation.coordinator <;>
    simp only [hcoord, Bool.false_eq_true] at hchosen
  rename_i outcome
  cases outcome <;> simp only at hchosen <;> try contradiction
  rw [hcoord] at hread hcut
  dsimp only at hread hcut
  intro k hk
  by_cases hklive : k < (liveTail rate rewards C_star C_h x).length
  · obtain ⟨hr, cell, _hpay, hc, _henabled, _hrows, _hJ, _hrewards⟩ :=
      hread ⟨k, hklive⟩
    have hc0 := live_baseline_zero rate _ _ cell.input hc
    refine ⟨_, cell.input, hr, ?_⟩
    simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hc0, Option.some_or]
  · have hbound : cutoffDelta rate rewards C_star C_h x ≤ 1 := by
      unfold cutoffDelta
      split
      · split <;> omega
      · omega
    have hdelta : cutoffDelta rate rewards C_star C_h x = 1 := by omega
    have hkEq : k = (liveTail rate rewards C_star C_h x).length := by omega
    subst k
    unfold cutoffDelta at hdelta
    cases he : (sourceRecords rate rewards C_star C_h x)[birthIndex rate rewards C_star C_h x +
        1 + (liveTail rate rewards C_star C_h x).length]? with
    | none => simp only [he, reduceCtorEq] at hdelta
    | some r =>
      rw [he] at hdelta
      change (match r.output.preparation.coordinator with
        | .live _ _ _ (.cutoffChosen ..) => 1
        | _ => 0) = 1 at hdelta
      change (match (sourceRecords rate rewards C_star C_h x)[birthIndex rate rewards C_star C_h x +
          1 + (liveTail rate rewards C_star C_h x).length]? with
        | none => True
        | some r => _) at hcut
      simp only [he] at hcut
      cases hr : r.output.preparation.coordinator <;> simp only [hr, Nat.zero_ne_one] at hdelta
      rename_i registers owned base result
      cases result <;> simp only [Nat.zero_ne_one] at hdelta
      rw [hr] at hcut
      dsimp only at hcut
      obtain ⟨_hnon, _hpay, _htime, _hdate, _hrows, _hJ, _hrewards,
        _hsigma, hstart, _hfirst, _hgrid, _halt, selected, _hsel, _hpayload,
        _hpending, _hcutoff, hfollowers⟩ := hcut
      have hunoccupied : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied r := by
        intro i
        obtain ⟨old, memory, _hinput, _hvalid, _hbound, _hzero, _hbefore, _hoccupied,
          _hdecision, _hprep, hconfig, _hrest⟩ := hfollowers i
        simp only [hconfig]
      have hsigma : 0 < registers.payload.sigma.val := by
        rw [_hpay]
        omega
      have hc : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).isSome = true :=
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 r).mpr
          ⟨hunoccupied, by simpa only [hr] using hsigma⟩
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hc
      have hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none := by
        apply (ReferenceLaterLiveNumericalReadout.laterLiveReadout_eq_none_iff 0 r).mpr
        rintro ⟨other, hother, _hbase, hlive, _ho⟩
        have heq : other = selected := Option.some.inj (hother.symm.trans (by rw [hr]; exact _hsel))
        subst other
        simp [CoordinatorLocalArmChoice.assignmentIsLive, _hcutoff,
          CoordinatorLocalArmChoice.cutoffRound, CoordinatorLocalArmChoice.sourceRound,
          CoordinatorCollectionUpRoundStep.localCutoff,
          CoordinatorCollectionUpRoundStep.sourceCutoff] at hlive
      refine ⟨r, c, rfl, ?_⟩
      simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hlive, Option.none_or, hc]

/-- Presence of the actual optional prefix includes a genuine launch. -/
theorem prefixInputs_launch (n : ℕ) (x : X) (L : List Input)
    (hL : prefixInputs rate rewards C_star C_h n x = some L) :
    actualLaunchBy rate rewards C_star C_h n x := by
  by_contra hn
  simp only [prefixInputs, ite_eq_right hn, reduceCtorEq] at hL

/-- One actual original record appends one actual cell to the same initialized run. -/
theorem prefixInputs_append_one (n : ℕ) (x : X) (L : List Input)
    (hL : prefixInputs rate rewards C_star C_h n x = some L)
    (r : Record) (c : Input)
    (hr : (sourceRecords rate rewards C_star C_h x)[n - sourceStart rate rewards C_star C_h x]? = some r)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c) :
    prefixInputs rate rewards C_star C_h (n + 1) x = some (L ++ [c]) := by
  have hlaunch := prefixInputs_launch rate rewards C_star C_h n x L hL
  have hlaunch' : actualLaunchBy rate rewards C_star C_h (n + 1) x :=
    ⟨hlaunch.1, hlaunch.2.trans (Nat.le_succ _)⟩
  have hs : sourceStart rate rewards C_star C_h x ≤ n := hlaunch.2
  have hindex : n + 1 - sourceStart rate rewards C_star C_h x =
      (n - sourceStart rate rewards C_star C_h x) + 1 := by omega
  simp only [prefixInputs, ite_eq_left hlaunch] at hL
  rw [prefixInputs, ite_eq_left hlaunch', hindex, List.take_add_one, hr]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
    hc, List.mapM_append, hL, List.mapM_cons, List.mapM_nil, id_eq]
  rfl

/-- Every boundary of the finite corrected slice has all its original inputs.
The induction starts with the inherited queue after the actual call cell. -/
theorem firstCell_prefix_inputs (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t)
    (n : ℕ) (hn : t.val + 1 ≤ n) (hne : n ≤ endDate rate rewards C_star C_h t x) :
    ∃ inputs : List Input,
      prefixInputs rate rewards C_star C_h n x = some inputs ∧
      inputs.length = n - sourceStart rate rewards C_star C_h x ∧
      prefixReadout rate rewards C_star C_h n x =
        some (stateReadout (RecordedQueueRun.run Q inputs)) := by
  have htime := firstCell_birth_time rate rewards C_star C_h u t x hx
  have htail := firstCell_tail_cells rate rewards C_star C_h u t x hx
  obtain ⟨L, c, _hL, _hc, hbase, hlen⟩ :=
    firstCell_initial_inputs rate rewards C_star C_h u t x hx
  have hall : ∀ j, j ≤ (liveTail rate rewards C_star C_h x).length + cutoffDelta rate rewards C_star C_h x →
      ∃ inputs : List Input,
        prefixInputs rate rewards C_star C_h (t.val + 1 + j) x = some inputs ∧
        inputs.length = t.val + 1 + j - sourceStart rate rewards C_star C_h x := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨L ++ [c], by simpa only [Nat.add_zero] using hbase, ?_⟩
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
      change L.length = t.val - sourceStart rate rewards C_star C_h x at hlen
      omega
    | succ j ih =>
      intro hj
      obtain ⟨inputs, hinputs, hlen⟩ := ih (by omega)
      obtain ⟨r, cell, hr, hcell⟩ := htail j (by omega)
      have hi : t.val + 1 + j - sourceStart rate rewards C_star C_h x =
          birthIndex rate rewards C_star C_h x + 1 + j := by omega
      have happ := prefixInputs_append_one rate rewards C_star C_h
        (t.val + 1 + j) x inputs hinputs r cell (by rw [hi]; exact hr) hcell
      refine ⟨inputs ++ [cell], by simpa only [Nat.add_assoc] using happ, ?_⟩
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  obtain ⟨inputs, hinputs, hlen⟩ := hall (n - (t.val + 1)) (by
    unfold endDate at hne
    omega)
  have he : t.val + 1 + (n - (t.val + 1)) = n := by omega
  rw [he] at hinputs hlen
  exact ⟨inputs, hinputs, hlen, by simp only [prefixReadout, hinputs, Option.map_some]⟩

private theorem mapM_prefix {α : Type*} {xs ys : List (Option α)}
    {out : List α} (hxy : xs <+: ys) (hout : ys.mapM id = some out) :
    ∃ early suffix, xs.mapM id = some early ∧ out = early ++ suffix := by
  obtain ⟨tail, htail⟩ := hxy
  subst ys
  rw [List.mapM_append] at hout
  cases hx : xs.mapM id with
  | none => simp [hx] at hout
  | some early =>
    cases ht : tail.mapM id with
    | none => simp [hx, ht] at hout
    | some suffix =>
      have he : early ++ suffix = out := by simpa [hx, ht] using hout
      exact ⟨early, suffix, rfl, he.symm⟩

/-- Any two produced input lists in the interval are exact prefixes, with
one input per calendar date and no replacement of the original records. -/
theorem firstCell_prefix_append (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t)
    (n m : ℕ) (hn : t.val + 1 ≤ n) (hnm : n ≤ m)
    (hme : m ≤ endDate rate rewards C_star C_h t x)
    (inputsN inputsM : List Input)
    (hN : prefixInputs rate rewards C_star C_h n x = some inputsN)
    (hM : prefixInputs rate rewards C_star C_h m x = some inputsM) :
    ∃ suffix, inputsM = inputsN ++ suffix ∧ suffix.length = m - n := by
  have hlaunchN := prefixInputs_launch rate rewards C_star C_h n x inputsN hN
  have hlaunchM := prefixInputs_launch rate rewards C_star C_h m x inputsM hM
  have hN' := hN
  have hM' := hM
  simp only [prefixInputs, ite_eq_left hlaunchN] at hN'
  simp only [prefixInputs, ite_eq_left hlaunchM] at hM'
  have hp : ((sourceRecords rate rewards C_star C_h x).take
      (n - sourceStart rate rewards C_star C_h x)).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) <+:
      ((sourceRecords rate rewards C_star C_h x).take
        (m - sourceStart rate rewards C_star C_h x)).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) :=
    ((List.take_isPrefix_take).mpr (Or.inl (Nat.sub_le_sub_right hnm _))).map _
  obtain ⟨early, suffix, hearly, hsuffix⟩ := mapM_prefix hp hM'
  have heq : early = inputsN := Option.some.inj (hearly.symm.trans hN')
  subst early
  obtain ⟨actualN, haN, hlenN, _⟩ := firstCell_prefix_inputs
    rate rewards C_star C_h u t x hx n hn (hnm.trans hme)
  obtain ⟨actualM, haM, hlenM, _⟩ := firstCell_prefix_inputs
    rate rewards C_star C_h u t x hx m (hn.trans hnm) hme
  have heN : actualN = inputsN := Option.some.inj (haN.symm.trans hN)
  have heM : actualM = inputsM := Option.some.inj (haM.symm.trans hM)
  rw [heN] at hlenN
  rw [heM] at hlenM
  refine ⟨suffix, hsuffix, ?_⟩
  have hlen := congrArg List.length hsuffix
  simp only [List.length_append] at hlen
  have hs : sourceStart rate rewards C_star C_h x ≤ n := hlaunchN.2
  omega

private theorem execute_overflow_records (suffix : List Input)
    (state : RecordedQueueRun.RunState p.K) (hf : state.overflow = true) :
    ∀ a, (RecordedQueueRun.execute Q suffix state).records a =
      state.records a ++ List.replicate suffix.length (false, 0) := by
  induction suffix generalizing state with
  | nil => simp [RecordedQueueRun.execute]
  | cons c suffix ih =>
    have hstep := ReferenceFirstCollectionRenewalFutureNumericalPrefix.overflow_step_records
      rate state c hf
    intro a
    rw [RecordedQueueRun.execute, ih _ hstep.2]
    rw [hstep.1]
    simp only [List.length_cons, List.replicate_succ, List.append_assoc,
      List.singleton_append]

/-- An incoming true overflow flag freezes the endpoint registers and appends
one disabled history entry for every remaining original date. -/
theorem firstCell_overflow_endpoint (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t)
    (n : ℕ) (hn : t.val + 1 ≤ n) (hne : n ≤ endDate rate rewards C_star C_h t x)
    (on : Readout) (hon : prefixReadout rate rewards C_star C_h n x = some on)
    (hflag : on.2.1 = true) :
    ∃ oe : Readout,
      prefixReadout rate rewards C_star C_h (endDate rate rewards C_star C_h t x) x = some oe ∧
      oe.1 = on.1 ∧ oe.2.1 = true ∧
      ∀ a, oe.2.2 a = on.2.2 a ++
        List.replicate (endDate rate rewards C_star C_h t x - n) (false, 0) := by
  obtain ⟨inputsN, hN, _hlenN, hreadN⟩ :=
    firstCell_prefix_inputs rate rewards C_star C_h u t x hx n hn hne
  obtain ⟨inputsE, hE, _hlenE, hreadE⟩ :=
    firstCell_prefix_inputs rate rewards C_star C_h u t x hx
      (endDate rate rewards C_star C_h t x)
      (endDate_bounds rate rewards C_star C_h u t x hx).1 le_rfl
  have hOn : stateReadout (RecordedQueueRun.run Q inputsN) = on :=
    Option.some.inj (hreadN.symm.trans hon)
  have hf : (RecordedQueueRun.run Q inputsN).overflow = true := by
    have he := congrArg (fun z : Readout => z.2.1) hOn
    exact he.trans hflag
  obtain ⟨suffix, hjoin, hlen⟩ := firstCell_prefix_append rate rewards C_star C_h u t x hx
    n (endDate rate rewards C_star C_h t x) hn hne le_rfl inputsN inputsE hN hE
  have hrun : RecordedQueueRun.run Q inputsE =
      RecordedQueueRun.execute Q suffix (RecordedQueueRun.run Q inputsN) := by
    rw [hjoin, RecordedQueueRun.run, RecordedEpisodeStability.execute_append]
    rfl
  have hpres := RecordedQueueRun.execute_after_overflow_preserves Q suffix _ hf
  have hrecords := execute_overflow_records rate suffix _ hf
  refine ⟨stateReadout (RecordedQueueRun.run Q inputsE), hreadE, ?_, ?_, ?_⟩
  · change (RecordedQueueRun.run Q inputsE).registers = on.1
    rw [hrun]
    exact (funext hpres.2).trans (congrArg Prod.fst hOn)
  · change (RecordedQueueRun.run Q inputsE).overflow = true
    rw [hrun]
    exact hpres.1
  · intro a
    change (RecordedQueueRun.run Q inputsE).records a = _
    rw [hrun, hrecords a, hlen]
    have he := congrArg (fun z : Readout => z.2.2 a) hOn
    change (RecordedQueueRun.run Q inputsN).records a = on.2.2 a at he
    rw [he]

/-- A threshold crossing in a present initialized prefix sets the actual
absorbing flag. The crossing update has already been retained. -/
theorem prefix_threshold_overflow (n : ℕ) (x : X) (a : Fin p.K)
    (on : Readout) (hon : prefixReadout rate rewards C_star C_h n x = some on)
    (hcross : ((on.1 a).2 : ℝ) / ((Q).n : ℝ) > 1 / (32 * rate.eta.val)) :
    on.2.1 = true := by
  unfold prefixReadout at hon
  cases hi : prefixInputs rate rewards C_star C_h n x with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hon
  | some inputs =>
    have he : stateReadout (RecordedQueueRun.run Q inputs) = on := by
      simpa only [hi, Option.map_some, Option.some.injEq] using hon
    have hcut : 32 * (on.1 a).2 > (Q).D :=
      (RecordedQueueRun.overflowCutoff_iff Q _).mp hcross
    have hreg : (RecordedQueueRun.run Q inputs).registers = on.1 := congrArg Prod.fst he
    have hf := (RecordedQueueRun.run_overflow_iff_cutoff Q inputs).mpr
      ⟨a, by rw [hreg]; exact hcut⟩
    exact (congrArg (fun z : Readout => z.2.1) he).symm.trans hf

/-- The literal early-crossing event equals the same-arm endpoint threshold
on the corrected original-source slice. This is deterministic, with no tail-law claim. -/
theorem overflowEvent_iff_endpoint (u t : Fin p.T) (a : Fin p.K) (x : X) :
    x ∈ overflowEvent rate rewards C_star C_h u t a ↔
      x ∈ correctedCell rate rewards C_star C_h u t ∧
        ∃ oe : Readout,
          prefixReadout rate rewards C_star C_h (endDate rate rewards C_star C_h t x) x = some oe ∧
          ((oe.1 a).2 : ℝ) / ((Q).n : ℝ) > 1 / (32 * rate.eta.val) := by
  constructor
  · rintro ⟨hx, n, hn, hne, on, hon, hcross⟩
    have hf := prefix_threshold_overflow rate rewards C_star C_h n x a on hon hcross
    obtain ⟨oe, hoe, hreg, _hf, _hhistory⟩ :=
      firstCell_overflow_endpoint rate rewards C_star C_h u t x hx n hn hne on hon hf
    exact ⟨hx, oe, hoe, by rw [hreg]; exact hcross⟩
  · rintro ⟨hx, oe, hoe, hcross⟩
    exact ⟨hx, endDate rate rewards C_star C_h t x,
      (endDate_bounds rate rewards C_star C_h u t x hx).1, le_rfl, oe, hoe, hcross⟩

/-- At a crossing endpoint its exponential energy strictly exceeds the cap
energy. No probability or measurability conclusion is inferred here. -/
theorem endpoint_exp_gt_cap (u t : Fin p.T) (a : Fin p.K) (x : X)
    (hx : x ∈ overflowEvent rate rewards C_star C_h u t a) :
    ∃ oe : Readout,
      prefixReadout rate rewards C_star C_h (endDate rate rewards C_star C_h t x) x = some oe ∧
      Real.exp (CanonicalRecordingRates.beta p rate.eta.val / (32 * rate.eta.val)) <
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          (((oe.1 a).2 : ℝ) / ((Q).n : ℝ))) := by
  obtain ⟨_hcell, oe, hoe, hcross⟩ :=
    (overflowEvent_iff_endpoint rate rewards C_star C_h u t a x).mp hx
  refine ⟨oe, hoe, Real.exp_lt_exp.mpr ?_⟩
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hmul := mul_lt_mul_of_pos_left hcross hb
  simpa only [mul_one_div] using hmul

private theorem gridBoundary_eq_of_within (sigma t : Fin p.T)
    (hst : sigma.val ≤ t.val)
    (htg : t.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val sigma) :
    FollowerCutoffScan.gridBoundary p rate.eta.val t =
      FollowerCutoffScan.gridBoundary p rate.eta.val sigma := by
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hupper : t.val + 1 < H * ((sigma.val + 1) / H + 1) :=
    lt_of_lt_of_le htg (Nat.min_le_right _ _)
  have hlower : ((sigma.val + 1) / H) * H ≤ t.val + 1 :=
    (Nat.div_mul_le_self _ _).trans (by omega)
  have hdiv : (t.val + 1) / H = (sigma.val + 1) / H :=
    Nat.div_eq_of_lt_le hlower (by simpa only [Nat.mul_comm] using hupper)
  change min (p.T + 1) (H * ((t.val + 1) / H + 1)) =
    min (p.T + 1) (H * ((sigma.val + 1) / H + 1))
  rw [hdiv]

/-- Corrected initialization stays in the old grid interval. The actual
incoming collection clock and literal division formula identify its boundary. -/
theorem firstCell_old_grid (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h t x =
      some (FollowerCutoffScan.gridBoundary p rate.eta.val t) ∧
      t.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val t := by
  obtain ⟨n, r, theta, hr, ht, _har, hcall, _hrest⟩ :=
    ReferenceFirstCollectionCurrentNumericalCell.firstCell_record
      rate rewards C_star C_h u t x hx.1
  obtain ⟨old, ledger, saved, hcoord, _⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcall
  have hf := ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record
    rate rewards C_star C_h t x r (List.mem_of_getElem? hr) ht old ledger saved hcoord
  have hclock := ReferenceFirstReplacementNextFollowerStep.complete_suffix_record_clock
    rate x rewards C_star C_h ⟨n, (List.getElem?_eq_some_iff.mp hr).1⟩
  have hget : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate x rewards C_star C_h).get ⟨n, (List.getElem?_eq_some_iff.mp hr).1⟩ = r :=
    (List.getElem?_eq_some_iff.mp hr).2
  rw [hget] at hclock
  simp only [ReferenceCoordinatorClockDomains.clockAt, hcoord] at hclock
  obtain ⟨_hsigma, hcut, _hcutpos, _hcutT, hbefore, hfreeze, _hcutg, _hgT⟩ := hclock
  obtain ⟨g, hg, htg⟩ := hx.2
  have hgEq : ledger.freezeAt = g := Option.some.inj (hf.symm.trans hg)
  have hst : old.sigma.val ≤ t.val := by
    rw [ht] at hbefore
    omega
  have hlt : t.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val old.sigma := by
    rw [← hfreeze, hgEq]
    exact htg
  have he := gridBoundary_eq_of_within rate old.sigma t hst hlt
  have hnew : FollowerCutoffScan.gridBoundary p rate.eta.val t = g :=
    he.trans (hfreeze.symm.trans hgEq)
  exact ⟨by rw [hnew]; exact hg, by rw [hnew]; exact htg⟩

/-- Each actual continuing LIVE cell retains the whole rewards, original row
and private index, its installed payload, and the strict old-grid geometry. -/
theorem firstCell_continuing_cells (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    ∀ k : Fin (liveTail rate rewards C_star C_h x).length,
      let r := (liveTail rate rewards C_star C_h x).get k
      (sourceRecords rate rewards C_star C_h x)[birthIndex rate rewards C_star C_h x + 1 + k.val]? = some r ∧
      r.input.time.val = t.val + 1 + k.val ∧
      r.input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val t ∧
      r.input.rows = x.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p x ∧
      r.input.rewards = rewards ∧
      ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
        ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some cell.input ∧
        cell.input.enabled = true ∧
        cell.selected.view.payload.sigma = t ∧
        cell.input.reward = (fun a => ((rewards r.input.time a).val : ℝ) / (D p : ℝ)) := by
  obtain ⟨birth, hb, _har, ht, hchosen⟩ :=
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_firstReplacement_record
      rate rewards C_star C_h u t x hx.1
  have hread :=
    ReferenceFirstReplacementFollowerBoundary.complete_first_replacement_continuing_live_readout
      rate x rewards C_star C_h
  have hgeo := ReferenceFirstReplacementLiveFollowerPrefix.complete_first_replacement_continuing_geometry
    rate x rewards C_star C_h
  dsimp only at hread hgeo
  simp only [hb] at hread hgeo
  have hp : birth.output.preparation = ReferenceActivePhysicalStep.prepare birth.input := by
    rw [birth.output_eq]
    rfl
  unfold ReferenceCollectionPhaseHistory.laterChosen at hchosen
  rw [← hp] at hchosen
  cases hcoord : birth.output.preparation.coordinator <;>
    simp only [hcoord, Bool.false_eq_true] at hchosen
  rename_i outcome
  cases outcome <;> simp only at hchosen <;> try contradiction
  rw [hcoord] at hread hgeo
  dsimp only at hread hgeo
  intro k
  let r := (liveTail rate rewards C_star C_h x).get k
  obtain ⟨hr, cell, hpay, hc, henabled, hrows, hJ, hrewards⟩ := hread k
  obtain ⟨_hr, htime, _hrows, _hJ, _hrewards, selected, _hsel,
    _hpay, _hlive, hgrid, _hbits⟩ := hgeo.2 k
  have hsigma : cell.selected.view.payload.sigma = t := by
    apply Fin.ext
    rw [hpay, hgeo.1, ht]
  have hinstalled : _ = t := Fin.ext (hgeo.1.trans (congrArg Fin.val ht))
  have hc0 := live_baseline_zero rate _ _ cell.input hc
  refine ⟨hr, by simpa only [liveTail, birthIndex, sourceRecords, ht] using htime, ?_, hrows, hJ, hrewards,
    cell, ?_, henabled, hsigma, ?_⟩
  · simpa only [liveTail, birthIndex, sourceRecords, hinstalled] using hgrid
  · simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, liveTail, birthIndex, sourceRecords,
      hc0, Option.some_or]
  · rw [cell.input_eq]
    change (fun a => ((r.input.rewards r.input.time a).val : ℝ) / (D p : ℝ)) = _
    have hrew : r.input.rewards = rewards := by
      simpa only [r, liveTail, birthIndex, sourceRecords] using hrewards
    rw [hrew]

private theorem dispatch_live_origin (input : ReferenceActivePhysicalStep.RoundInput p rate) :
    match ReferenceActivePhysicalStep.dispatch input with
    | .live r q base _ => input.state.coordinator = .live r q base
    | _ => True := by
  unfold ReferenceActivePhysicalStep.dispatch
  cases hs : input.state.coordinator with
  | first => trivial
  | live r q base =>
    simp only [CoordinatorRoundDispatch.dispatch]
    cases CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput input r q base) <;> rfl
  | collection payload ledger saved =>
    by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · simp only [dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
      cases CoordinatorRoundDispatch.dispatchCollection
        (ReferenceActivePhysicalStep.collectionInput input payload ledger
          (ReferenceActivePhysicalStep.collectionClock payload ledger saved ⟨ledger.cutoff - 1, by omega⟩)
          ⟨ledger.cutoff - 1, by omega⟩) <;> trivial
    · simp only [dite_eq_right hc]
  | dagger => trivial

/-- The first excluded record is inspected by its actual constructor. Only a
selected cutoff supplies this cell; the grid boundary disables its service. -/
theorem firstCell_cutoff_cell (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    match (sourceRecords rate rewards C_star C_h x)[birthIndex rate rewards C_star C_h x +
        1 + (liveTail rate rewards C_star C_h x).length]? with
    | none => True
    | some r => match r.output.preparation.coordinator with
      | .live registers _ _ (.cutoffChosen ..) =>
        r.input.time.val = t.val + 1 + (liveTail rate rewards C_star C_h x).length ∧
        r.input.time.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val t ∧
        (FollowerCutoffScan.gridBoundary p rate.eta.val t = r.input.time.val + 1 ∨
          ∃ stamp : Fin p.T, registers.priorClock.lastProposal = some (stamp, true) ∧
            stamp.val + 1 = r.input.time.val ∧
            FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row stamp = true) ∧
        r.input.rows = x.1.2 ∧
        r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p x ∧
        r.input.rewards = rewards ∧
        ∃ c : Input,
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
          c.enabled = decide (r.input.time.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val t) ∧
          c.reward = (fun a => ((rewards r.input.time a).val : ℝ) / (D p : ℝ))
      | _ => True := by
  obtain ⟨birth, hb, _har, ht, hchosen⟩ :=
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_firstReplacement_record
      rate rewards C_star C_h u t x hx.1
  have hcut :=
    ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
      rate x rewards C_star C_h
  dsimp only at hcut
  simp only [hb] at hcut
  have hp : birth.output.preparation = ReferenceActivePhysicalStep.prepare birth.input := by
    rw [birth.output_eq]
    rfl
  unfold ReferenceCollectionPhaseHistory.laterChosen at hchosen
  rw [← hp] at hchosen
  cases hcoord : birth.output.preparation.coordinator <;>
    simp only [hcoord, Bool.false_eq_true] at hchosen
  rename_i outcome
  cases outcome <;> simp only at hchosen <;> try contradiction
  rw [hcoord] at hcut
  dsimp only at hcut
  cases he : (sourceRecords rate rewards C_star C_h x)[birthIndex rate rewards C_star C_h x +
      1 + (liveTail rate rewards C_star C_h x).length]? with
  | none => trivial
  | some r =>
    dsimp only
    change (match (sourceRecords rate rewards C_star C_h x)[birthIndex rate rewards C_star C_h x +
        1 + (liveTail rate rewards C_star C_h x).length]? with
      | none => True
      | some r => _) at hcut
    simp only [he] at hcut
    cases hr : r.output.preparation.coordinator <;> try trivial
    rename_i registers owned base result
    cases result <;> try trivial
    rename_i dispatched hstart ledger hinit hledger hdomain hcutclock hpending hnone arm
    rw [hr] at hcut
    dsimp only at hcut
    obtain ⟨_hnon, hpay, htime, _hdate, hrows, hJ, hrewards,
      hsigma, hbase, _hfirst, hgrid, hcause, selected, hsel, hpayload,
      _hpending, hcutoff, hfollowers⟩ := hcut
    have hsigmaT : registers.payload.sigma = t := by
      apply Fin.ext
      rw [hpay, hsigma, ht]
    have hunoccupied : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied r := by
      intro i
      obtain ⟨old, memory, _hinput, _hvalid, _hbound, _hzero, _hbefore, _hoccupied,
        _hdecision, _hprep, hconfig, _hrest⟩ := hfollowers i
      simp only [hconfig]
    have hzero : 0 < registers.payload.sigma.val := by rw [hpay]; omega
    have hsome : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).isSome = true :=
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 r).mpr
        ⟨hunoccupied, by simpa only [hr] using hzero⟩
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
    have hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none := by
      apply (ReferenceLaterLiveNumericalReadout.laterLiveReadout_eq_none_iff 0 r).mpr
      rintro ⟨other, hother, _hbase, hlive, _ho⟩
      have heq : other = selected := Option.some.inj (hother.symm.trans (by rw [hr]; exact hsel))
      subst other
      simp [CoordinatorLocalArmChoice.assignmentIsLive, hcutoff,
        CoordinatorLocalArmChoice.cutoffRound, CoordinatorLocalArmChoice.sourceRound,
        CoordinatorCollectionUpRoundStep.localCutoff, CoordinatorCollectionUpRoundStep.sourceCutoff] at hlive
    obtain ⟨payload, ledger', started, weights, _out, hcall, _hpost, _hrun,
      _henabled, henabled, _hrate, hreward, _hrest⟩ :=
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 r c hc
    have hcall' : ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r =
        some ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
          dispatched.startResult, (ReferenceActivePhysicalStep.liveRegistersAt registers r.input.time).complementWeights⟩ := by
      simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall, hunoccupied,
        ite_true, hr, hzero]
    have hargs := Option.some.inj (hcall'.symm.trans hcall)
    have hstarted : dispatched.startResult = started := congrArg (fun args => args.2.2.1) hargs
    have horigin := dispatch_live_origin rate r.input
    have hdispatch : ReferenceActivePhysicalStep.dispatch r.input = r.output.preparation.coordinator := by
      rw [r.output_eq]
      rfl
    rw [hdispatch, hr] at horigin
    have hclock := ReferenceFirstReplacementNextFollowerStep.complete_suffix_record_clock
      rate x rewards C_star C_h
      ⟨birthIndex rate rewards C_star C_h x + 1 + (liveTail rate rewards C_star C_h x).length,
        (List.getElem?_eq_some_iff.mp he).1⟩
    have hget : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate x rewards C_star C_h).get
        ⟨birthIndex rate rewards C_star C_h x + 1 + (liveTail rate rewards C_star C_h x).length,
          (List.getElem?_eq_some_iff.mp he).1⟩ = r := (List.getElem?_eq_some_iff.mp he).2
    rw [hget] at hclock
    simp only [ReferenceCoordinatorClockDomains.clockAt, horigin] at hclock
    have hboundary : registers.priorClock.g = FollowerCutoffScan.gridBoundary p rate.eta.val t := by
      have hg := hclock.2.1.1
      simpa only [CoordinatorPhaseClock.boundaryFromSigma, hclock.2.2.1, hsigmaT] using hg
    have hstartedGrid : started.clock.g = FollowerCutoffScan.gridBoundary p rate.eta.val t := by
      rw [← hstarted, hcutclock]
      exact hboundary
    have hpayTime : _ = t := Fin.ext (hsigma.trans (congrArg Fin.val ht))
    refine ⟨by simpa only [liveTail, birthIndex, sourceRecords, ht] using htime, ?_, ?_, hrows, hJ, hrewards, c, ?_, ?_, ?_⟩
    · simpa only [hpayTime] using hgrid
    · simpa only [hpayTime] using hcause
    · simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hlive, Option.none_or, hc]
    · rw [henabled, hstartedGrid]
    · rw [hrewards] at hreward
      exact hreward

/-- Both lists and their suffix are produced inside the proof on the same
original source; no prefix or run witness is an input to this export. -/
theorem firstCell_prefix_extension (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t)
    (n m : ℕ) (hn : t.val + 1 ≤ n) (hnm : n ≤ m)
    (hme : m ≤ endDate rate rewards C_star C_h t x) :
    ∃ inputsN inputsM suffix : List Input,
      prefixInputs rate rewards C_star C_h n x = some inputsN ∧
      prefixInputs rate rewards C_star C_h m x = some inputsM ∧
      inputsM = inputsN ++ suffix ∧ suffix.length = m - n := by
  obtain ⟨inputsN, hN, _hlenN, _hreadN⟩ :=
    firstCell_prefix_inputs rate rewards C_star C_h u t x hx n hn (hnm.trans hme)
  obtain ⟨inputsM, hM, _hlenM, _hreadM⟩ :=
    firstCell_prefix_inputs rate rewards C_star C_h u t x hx m (hn.trans hnm) hme
  obtain ⟨suffix, hjoin, hlen⟩ := firstCell_prefix_append
    rate rewards C_star C_h u t x hx n m hn hnm hme inputsN inputsM hN hM
  exact ⟨inputsN, inputsM, suffix, hN, hM, hjoin, hlen⟩

/-- The actual date-by-date update is the existing stopped queue step applied
to the produced initialized prefix and actual next physical record. -/
theorem firstCell_step_inputs (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t)
    (n : ℕ) (hn : t.val + 1 ≤ n) (hne : n < endDate rate rewards C_star C_h t x) :
    ∃ (L : List Input) (r : Record) (c : Input),
      prefixInputs rate rewards C_star C_h n x = some L ∧
      (sourceRecords rate rewards C_star C_h x)[n - sourceStart rate rewards C_star C_h x]? = some r ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧
      prefixInputs rate rewards C_star C_h (n + 1) x = some (L ++ [c]) ∧
      prefixReadout rate rewards C_star C_h (n + 1) x =
        some (stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)) := by
  obtain ⟨L, hL, _hlen, _hread⟩ :=
    firstCell_prefix_inputs rate rewards C_star C_h u t x hx n hn hne.le
  have htime := firstCell_birth_time rate rewards C_star C_h u t x hx
  have hidx : n - sourceStart rate rewards C_star C_h x =
      birthIndex rate rewards C_star C_h x + 1 + (n - (t.val + 1)) := by omega
  obtain ⟨r, c, hr, hc⟩ := firstCell_tail_cells rate rewards C_star C_h u t x hx
    (n - (t.val + 1)) (by unfold endDate at hne; omega)
  have hr' : (sourceRecords rate rewards C_star C_h x)[n - sourceStart rate rewards C_star C_h x]? = some r := by
    rw [hidx]
    exact hr
  have hnext := prefixInputs_append_one rate rewards C_star C_h n x L hL r c hr' hc
  refine ⟨L, r, c, hL, hr', hc, hnext, ?_⟩
  simp only [prefixReadout, hnext, Option.map_some]
  rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]

/-- At the actual grid boundary in this slice, the update is disabled for all
arms. Both queues and scores are preserved and all accepted arrivals vanish. -/
theorem firstCell_boundary_update (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t)
    (n : ℕ) (hn : t.val + 1 ≤ n) (hne : n < endDate rate rewards C_star C_h t x)
    (hboundary : n + 1 = FollowerCutoffScan.gridBoundary p rate.eta.val t) :
    ∃ (L : List Input) (c : Input),
      prefixInputs rate rewards C_star C_h n x = some L ∧
      prefixInputs rate rewards C_star C_h (n + 1) x = some (L ++ [c]) ∧
      c.enabled = false ∧
      (RecordedQueueRun.run Q (L ++ [c])).registers = (RecordedQueueRun.run Q L).registers ∧
      ∀ a, (RecordedQueueRun.run Q (L ++ [c])).records a =
          (RecordedQueueRun.run Q L).records a ++ [(false, 0)] ∧
        RecordedQueueRun.acceptedArrival (RecordedQueueRun.acceptedRecord Q (RecordedQueueRun.run Q L) c a) = 0 := by
  have htime := firstCell_birth_time rate rewards C_star C_h u t x hx
  let k := n - (t.val + 1)
  have hk : k < (liveTail rate rewards C_star C_h x).length + cutoffDelta rate rewards C_star C_h x := by
    unfold endDate at hne
    dsimp only [k]
    omega
  have hklive : ¬ k < (liveTail rate rewards C_star C_h x).length := by
    intro hlt
    obtain ⟨_hr, hdate, hgrid, _hrest⟩ :=
      firstCell_continuing_cells rate rewards C_star C_h u t x hx ⟨k, hlt⟩
    dsimp only at hdate hgrid
    dsimp only [k] at hdate hgrid
    omega
  have hdeltaBound : cutoffDelta rate rewards C_star C_h x ≤ 1 := by
    unfold cutoffDelta
    split
    · split <;> omega
    · omega
  have hkEq : k = (liveTail rate rewards C_star C_h x).length := by omega
  have hdelta : cutoffDelta rate rewards C_star C_h x = 1 := by omega
  obtain ⟨r, c, hr, hc⟩ := firstCell_tail_cells rate rewards C_star C_h u t x hx k hk
  rw [hkEq] at hr
  have hcut := firstCell_cutoff_cell rate rewards C_star C_h u t x hx
  simp only [hr] at hcut
  unfold cutoffDelta at hdelta
  rw [hr] at hdelta
  cases hcoord : r.output.preparation.coordinator <;> simp only [hcoord, Nat.zero_ne_one] at hdelta
  rename_i registers owned base result
  cases result <;> simp only [Nat.zero_ne_one] at hdelta
  rw [hcoord] at hcut
  dsimp only at hcut
  obtain ⟨hdate, _hgrid, _hcause, _hrows, _hJ, _hrewards, actual, hactual, henabled, _hreward⟩ := hcut
  have hcEq : c = actual := Option.some.inj (hc.symm.trans hactual)
  subst actual
  have hdisabled : c.enabled = false := by
    rw [henabled]
    have hdate' : r.input.time.val = n := by dsimp only [k] at hkEq; omega
    simp only [hdate', ← hboundary, lt_self_iff_false, decide_false]
  obtain ⟨L, hL, _hlen, _hread⟩ :=
    firstCell_prefix_inputs rate rewards C_star C_h u t x hx n hn hne.le
  have hindex : n - sourceStart rate rewards C_star C_h x =
      birthIndex rate rewards C_star C_h x + 1 + (liveTail rate rewards C_star C_h x).length := by
    dsimp only [k] at hkEq
    omega
  have hnext := prefixInputs_append_one rate rewards C_star C_h n x L hL r c
    (by rw [hindex]; exact hr) hc
  have hstep := ReferenceFirstCollectionRenewalFutureNumericalPrefix.disabled_step_registers_and_records
    rate (RecordedQueueRun.run Q L) c hdisabled
  refine ⟨L, c, hL, hnext, hdisabled, ?_, ?_⟩
  · rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]
    exact hstep.1
  · intro a
    constructor
    · rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one, hstep.2]
    · exact (RecordedQueueRun.step_disabled_preserves Q _ c hdisabled a).2

/-- The first detecting update is the full existing queue transition. Every
later date in this slice freezes that updated state, including the crossing. -/
theorem firstCell_first_overflow_update (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t)
    (n : ℕ) (hn : t.val + 1 ≤ n) (hne : n < endDate rate rewards C_star C_h t x) :
    ∃ (L : List Input) (c : Input),
      prefixInputs rate rewards C_star C_h n x = some L ∧
      prefixInputs rate rewards C_star C_h (n + 1) x = some (L ++ [c]) ∧
      ((RecordedQueueRun.run Q L).overflow = false →
        (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c).overflow = true →
        (∃ a, 32 * ((RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c).registers a).2 > (Q).D) ∧
        (∀ a, (RecordedQueueRun.run Q (L ++ [c])).registers a =
          QueueReplay.transition (4 * (Q).n) ((RecordedQueueRun.run Q L).registers a)
            (RecordedQueueRun.acceptedRecord Q (RecordedQueueRun.run Q L) c a)) ∧
        ∃ oe : Readout,
          prefixReadout rate rewards C_star C_h (endDate rate rewards C_star C_h t x) x = some oe ∧
          oe.1 = (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c).registers ∧
          ∀ a, oe.2.2 a = (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c).records a ++
            List.replicate (endDate rate rewards C_star C_h t x - (n + 1)) (false, 0)) := by
  obtain ⟨L, _r, c, hL, _hr, _hc, hnext, hread⟩ :=
    firstCell_step_inputs rate rewards C_star C_h u t x hx n hn hne
  refine ⟨L, c, hL, hnext, ?_⟩
  intro hprior hcross
  have hretained := RecordedQueueRun.step_retains_first_overflow_update Q
    (RecordedQueueRun.run Q L) c hprior hcross
  obtain ⟨oe, hoe, hreg, _hflag, hrecords⟩ :=
    firstCell_overflow_endpoint rate rewards C_star C_h u t x hx (n + 1)
      (by omega) (by omega)
      (stateReadout (RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c)) hread hcross
  refine ⟨hretained.1, ?_, oe, hoe, hreg, hrecords⟩
  intro a
  rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]
  exact hretained.2 a

/-- An absent launch stays absent in the optional prefix. -/
theorem prefixInputs_no_launch (n : ℕ) (x : X)
    (hx : ¬ actualLaunchBy rate rewards C_star C_h n x) :
    prefixInputs rate rewards C_star C_h n x = none ∧
      prefixReadout rate rewards C_star C_h n x = none := by
  simp only [prefixInputs, prefixReadout, ite_eq_right hx, Option.map_none, and_self]

/-- A call in the last physical round has only the inherited AFTER endpoint;
no successor action coordinate is fabricated. -/
theorem terminal_endDate (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) (ht : t.val + 1 = p.T) :
    endDate rate rewards C_star C_h t x = p.T := by
  have hb := endDate_bounds rate rewards C_star C_h u t x hx
  omega

end Bandits.Support.ReferenceFirstCollectionCorrectedSliceNumericalPrefix
end
