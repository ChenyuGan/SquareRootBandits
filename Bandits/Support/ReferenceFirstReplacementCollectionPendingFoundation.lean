/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionCommonStopObservation

/-!
# Forward scan and pending foundation for the first replacement collection

Sources: `sources/zip4/manuscript/06_interruptions.tex:180-239,246-349,425-431,459-487`,
`05_binary_transport.tex:20-55,180-240`, and
`appendix_a_local_protocol.tex:92-157`.

The scan consumes completed original records in chronological order. It keeps
an actual installed payload only after its actual later-chosen birth. Its
collection boundary is recorded only after the actual cutoff update. The
current pending observation also includes the incoming cutoff reset. No
physical record is removed by the analytical common-stop mask.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionPendingFoundation

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record := ReferenceCompletePhysicalHistory.RoundRecord p rate
abbrev Payload := ReferenceActivePhysicalStep.Payload rate
abbrev Source := BootstrapPrivateRoundStreams.SourceInput p

/-- State of an analytical scan, not an additional protocol state. Payloads
are retained from actual births; absence has no default assignment. -/
inductive PastPhase (rate : ReferenceActivePhysicalStep.RateInput p) where
  | firstLive
  | firstCollection
  | replacementLive (payload : Payload (rate := rate))
  | replacementCollection (payload : Payload (rate := rate)) (onset : ℕ)
  | closed

/-- Observe the actual newly installed payload, with all nonmatching
constructors retaining absence. -/
def birthPayload (r : Record (rate := rate)) : Option (Payload (rate := rate)) :=
  match r.output.preparation.coordinator with
  | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
      some installed.registers.payload
  | _ => none

/-- The actual completed cutoff tag. -/
def isCutoff (r : Record (rate := rate)) : Bool :=
  match r.output.preparation.coordinator with
  | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) => true
  | _ => false

/-- Advance from one completed physical record. A noncontinuing record before
the replacement cutoff closes this particular collection search. During
collection all failure records remain, until an actual next birth occurs. -/
def advance (phase : PastPhase rate) (r : Record (rate := rate)) : PastPhase rate :=
  match phase with
  | .firstLive => if isCutoff r then .firstCollection else .firstLive
  | .firstCollection =>
      match birthPayload r with
      | none => .firstCollection
      | some payload => .replacementLive payload
  | .replacementLive payload =>
      if ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r then
        .replacementLive payload
      else if isCutoff r then .replacementCollection payload (r.input.time.val + 1)
      else .closed
  | .replacementCollection payload u =>
      if ReferenceCollectionPhaseHistory.laterChosen r.input then .closed
      else .replacementCollection payload u
  | .closed => .closed

/-- The forward observer consumes precisely the supplied completed prefix. -/
def scan (records : List (Record (rate := rate))) (phase : PastPhase rate := .firstLive) :
    PastPhase rate := records.foldl advance phase

/-- Exact preparation identity; this does not equate records with different
whole public tables. -/
theorem preparation_eq (r : Record (rate := rate)) :
    r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
  simpa only [ReferenceActivePhysicalStep.step] using
    congrArg (fun out : ReferenceActivePhysicalStep.RoundOutput r.input => out.preparation)
      r.output_eq

theorem isCutoff_eq (r : Record (rate := rate)) :
    isCutoff r = ReferenceCollectionPhaseHistory.cutoffChosen r.input := by
  unfold isCutoff ReferenceCollectionPhaseHistory.cutoffChosen
  rw [preparation_eq]
  cases (ReferenceActivePhysicalStep.prepare r.input).coordinator with
  | live _ _ _ outcome => cases outcome <;> rfl
  | first _ => rfl
  | collection _ _ _ _ _ => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

theorem birthPayload_isSome (r : Record (rate := rate)) :
    (birthPayload r).isSome = ReferenceCollectionPhaseHistory.laterChosen r.input := by
  unfold birthPayload ReferenceCollectionPhaseHistory.laterChosen
  rw [← preparation_eq r]
  cases r.output.preparation.coordinator with
  | collection _ _ _ _ outcome => cases outcome <;> rfl
  | first _ => rfl
  | live _ _ _ _ => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

@[simp] theorem scan_nil (phase : PastPhase rate) : scan [] phase = phase := rfl

@[simp] theorem scan_cons (r : Record (rate := rate)) (R : List (Record (rate := rate)))
    (phase : PastPhase rate) : scan (r :: R) phase = scan R (advance phase r) := rfl

theorem scan_append (A B : List (Record (rate := rate))) (phase : PastPhase rate) :
    scan (A ++ B) phase = scan B (scan A phase) := List.foldl_append

private theorem scan_fixed (R : List (Record (rate := rate))) (phase : PastPhase rate)
    (h : ∀ r ∈ R, advance phase r = phase) : scan R phase = phase := by
  induction R with
  | nil => rfl
  | cons r R ih =>
      rw [scan_cons, h r (List.mem_cons_self ..)]
      exact ih (fun q hq => h q (List.mem_cons_of_mem r hq))

/-- Before the first actual cutoff the scan has acquired no payload. -/
theorem scan_firstLiveWindow (R : List (Record (rate := rate))) :
    scan (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R) = .firstLive := by
  apply scan_fixed
  intro r hr
  have hc := List.mem_takeWhile_imp hr
  have hfalse : isCutoff r = false := by
    rw [isCutoff_eq]
    simpa only [Bool.not_eq_true'] using hc
  simp only [advance, hfalse, Bool.false_eq_true, ↓reduceIte]

/-- No later birth means that initial collection has not supplied a
replacement payload, even if a dispatch or recording step failed. -/
theorem scan_firstCollection (R : List (Record (rate := rate)))
    (h : ∀ r ∈ R, ReferenceCollectionPhaseHistory.laterChosen r.input = false) :
    scan R .firstCollection = .firstCollection := by
  apply scan_fixed
  intro r hr
  have hb : birthPayload r = none := by
    have hh := (birthPayload_isSome r).trans (h r hr)
    cases he : birthPayload r <;> simp_all
  simp only [advance, hb]

/-- The actual continuing chosen prefix retains the same actual payload. -/
theorem scan_continuing (R : List (Record (rate := rate))) (payload : Payload (rate := rate))
    (h : ∀ r ∈ R, ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = true) :
    scan R (.replacementLive payload) = .replacementLive payload := by
  apply scan_fixed
  intro r hr
  simp only [advance, h r hr, ↓reduceIte]

/-- Completed collection records do not close the observer before an actual
next birth. This statement includes all exceptional constructors. -/
theorem scan_collection (R : List (Record (rate := rate)))
    (payload : Payload (rate := rate)) (u : ℕ)
    (h : ∀ r ∈ R, ReferenceCollectionPhaseHistory.laterChosen r.input = false) :
    scan R (.replacementCollection payload u) = .replacementCollection payload u := by
  apply scan_fixed
  intro r hr
  simp only [advance, h r hr, Bool.false_eq_true, ↓reduceIte]

private theorem take_of_prefix {α : Type*} (A B : List α) (h : A <+: B) :
    B.take A.length = A := by
  obtain ⟨C, rfl⟩ := h
  simp only [List.take_left]

private theorem take_succ_of_lookup {α : Type*} (R : List α) (j : ℕ) (r : α)
    (hr : R[j]? = some r) : R.take (j + 1) = R.take j ++ [r] := by
  rw [List.take_add_one, hr]
  rfl

private theorem drop_of_lookup {α : Type*} (R : List α) (j : ℕ) (r : α)
    (hr : R[j]? = some r) : R.drop j = r :: R.drop (j + 1) := by
  obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp hr
  simpa only [he] using List.drop_eq_getElem_cons hj

private theorem first_after_takeWhile {α : Type*} (test : α → Bool) (R : List α)
    (h : (R.takeWhile test).length < R.length) :
    test (R[(R.takeWhile test).length]'h) = false := by
  induction R with
  | nil => simp at h
  | cons r R ih =>
      cases ht : test r with
      | false => simp only [List.takeWhile_cons, ht, Bool.false_eq_true,
          ↓reduceIte, List.length_nil, List.getElem_cons_zero]
      | true =>
          have hR : (R.takeWhile test).length < R.length := by simpa [ht] using h
          simpa only [List.takeWhile_cons, ht, ↓reduceIte, List.length_cons,
            List.getElem_cons_succ] using ih hR

/-- At the literal initial-collection endpoint the scan is still waiting for
its first actual replacement birth. This is a finite-list identity. -/
theorem scan_before_birth (R : List (Record (rate := rate)))
    (hcut : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length < R.length) :
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    scan (R.take v) = .firstCollection := by
  dsimp only
  let A := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R
  let w := A.length
  let W := (R.drop (w + 1)).takeWhile
    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
  let cut := R[w]'hcut
  have hget : R[w]? = some cut := List.getElem?_eq_getElem hcut
  have hfirst : R.take w = A := take_of_prefix A R (List.takeWhile_prefix _)
  have htag : isCutoff cut = true := by
    rw [isCutoff_eq]
    have hno := first_after_takeWhile
      (fun r : Record (rate := rate) => !ReferenceCollectionPhaseHistory.cutoffChosen r.input)
      R hcut
    change (!ReferenceCollectionPhaseHistory.cutoffChosen cut.input) = false at hno
    simpa only [Bool.not_eq_false'] using hno
  have hC : ReferenceCollectionPhaseHistory.collectionWindow R w = cut :: W := by
    unfold ReferenceCollectionPhaseHistory.collectionWindow
    rw [drop_of_lookup R w cut hget]
    rfl
  have htake : R.take (w + (cut :: W).length) = (A ++ [cut]) ++ W := by
    rw [show w + (cut :: W).length = (w + 1) + W.length by simp; omega,
      List.take_add, take_succ_of_lookup R w cut hget, hfirst]
    rw [take_of_prefix W (R.drop (w + 1)) (List.takeWhile_prefix _)]
  rw [hC, htake, scan_append, scan_append, scan_firstLiveWindow]
  simp only [scan_cons, scan_nil, advance, htag, ↓reduceIte]
  apply scan_firstCollection
  intro r hr
  simpa only [Bool.not_eq_true'] using (List.mem_takeWhile_imp hr)

/-- At the end of the first replacement live prefix, only completed past
records have been consulted. The first noncontinuing record has not yet been
read. -/
theorem scan_before_replacement_cut (R : List (Record (rate := rate)))
    (birth : Record (rate := rate)) (payload : Payload (rate := rate))
    (hb : R[(ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length +
      (ReferenceCollectionPhaseHistory.collectionWindow R
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length]? = some birth)
    (hp : birthPayload birth = some payload) :
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    scan (R.take (v + 1 + tail.length)) = .replacementLive payload := by
  dsimp only
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  have hv : v < R.length := (List.getElem?_eq_some_iff.mp hb).1
  have hw : w < R.length := by dsimp [v] at hv; omega
  have ht : R.take (v + 1 + tail.length) = (R.take v ++ [birth]) ++ tail := by
    rw [List.take_add, take_succ_of_lookup R v birth hb]
    rw [take_of_prefix tail (R.drop (v + 1)) (List.takeWhile_prefix _)]
  change scan (R.take (v + 1 + tail.length)) = _
  rw [ht, scan_append, scan_append, scan_before_birth R hw]
  simp only [scan_cons, scan_nil, advance, hp]
  apply scan_continuing
  exact fun r hr => List.mem_takeWhile_imp hr

/-- The complete first-replacement collection is a prefix of the original
suffix at its actual cutoff; its physical length is not analytically clipped. -/
theorem collection_prefix (R : List (Record (rate := rate))) (c : ℕ)
    (cut : Record (rate := rate)) (hc : R[c]? = some cut) :
    cut :: (R.drop (c + 1)).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) <+: R.drop c := by
  rw [drop_of_lookup R c cut hc]
  exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩

private theorem cutoff_not_continuing (r : Record (rate := rate))
    (h : isCutoff r = true) :
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = false := by
  unfold isCutoff at h
  unfold ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
  cases hd : r.output.preparation.coordinator with
  | live _ _ _ outcome =>
      rw [hd] at h
      cases outcome <;> simp_all
  | first _ => simp only [hd, Bool.false_eq_true] at h
  | collection _ _ _ _ _ => simp only [hd, Bool.false_eq_true] at h
  | invalidCollectionCutoff => simp only [hd, Bool.false_eq_true] at h
  | dagger => simp only [hd, Bool.false_eq_true] at h

/-- On every coordinate of the literal physical collection, the completed
past scan carries the SAME installed birth payload. On its zero coordinate
the cutoff is still incoming; afterwards its one-based onset is retained. -/
theorem scan_collection_coordinate (R : List (Record (rate := rate)))
    (birth : Record (rate := rate)) (payload : Payload (rate := rate))
    (hb : R[(ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length +
      (ReferenceCollectionPhaseHistory.collectionWindow R
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length]? = some birth)
    (hp : birthPayload birth = some payload)
    (cut : Record (rate := rate))
    (hc : R[(ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length +
      (ReferenceCollectionPhaseHistory.collectionWindow R
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length + 1 +
      (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R
        ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length +
          (ReferenceCollectionPhaseHistory.collectionWindow R
            (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length)).length]? = some cut)
    (hcut : isCutoff cut = true) :
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    let K := cut :: (R.drop (c + 1)).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
    ∀ a : Fin K.length,
      scan (R.take (c + a.val)) =
        if a.val = 0 then .replacementLive payload
        else .replacementCollection payload (cut.input.time.val + 1) := by
  dsimp only
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  let c := v + 1 + tail.length
  let W := (R.drop (c + 1)).takeWhile
    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
  let K := cut :: W
  have hscan : scan (R.take c) = .replacementLive payload :=
    scan_before_replacement_cut R birth payload hb hp
  intro a
  by_cases ha : a.val = 0
  · simp only [ha, Nat.add_zero, ↓reduceIte]
    exact hscan
  · have hapos : 0 < a.val := by omega
    have hprefix : W.take (a.val - 1) <+: R.drop (c + 1) :=
      (List.take_prefix _ _).trans (List.takeWhile_prefix _)
    have htake : R.take (c + a.val) =
        (R.take c ++ [cut]) ++ W.take (a.val - 1) := by
      rw [show c + a.val = (c + 1) + (a.val - 1) by omega,
        List.take_add, take_succ_of_lookup R c cut hc]
      have hW : (R.drop (c + 1)).take (a.val - 1) = W.take (a.val - 1) := by
        have hle : a.val - 1 ≤ W.length := by have hh := a.isLt; change a.val < (cut :: W).length at hh; simp only [List.length_cons] at hh; omega
        have hl : (W.take (a.val - 1)).length = a.val - 1 := List.length_take_of_le hle
        simpa only [hl] using take_of_prefix (W.take (a.val - 1))
          (R.drop (c + 1)) hprefix
      rw [hW]
    rw [htake, scan_append, scan_append, hscan]
    simp only [scan_cons, scan_nil, advance, cutoff_not_continuing cut hcut,
      Bool.false_eq_true, ↓reduceIte, hcut, ha]
    apply scan_collection
    intro r hr
    have hmem : r ∈ W := List.mem_of_mem_take hr
    simpa only [Bool.not_eq_true'] using (List.mem_takeWhile_imp hmem)

/-- Read the actual birth payload from the generated finite selection code.
An incoming collection that continues has a present cutoff; a newly chosen
assignment has no cutoff. Other incoming constructors retain absence. -/
def birthFromSelection
    (coordinator : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate)
    (selected : Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate)) :
    Option (Payload (rate := rate)) :=
  match coordinator with
  | .inr (.inr (.inl _)) => selected.bind fun choice =>
      if choice.1.cutoff = none then some choice.1.payload else none
  | _ => none

/-- The generated code keeps precisely the installed payload of a real
later-chosen constructor, with no payload on any failed birth. -/
theorem birthFromSelection_actual (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    birthFromSelection (ReferenceActivePhysicalStepMeasurability.encodeCoordinator x.state.coordinator)
      ((ReferenceActivePhysicalStep.dispatch x).selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection) =
      (match (ReferenceActivePhysicalStep.prepare x).coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
          some installed.registers.payload
      | _ => none) := by
  unfold ReferenceActivePhysicalStep.prepare
  cases hs : x.state.coordinator with
  | first => simp only [ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
      birthFromSelection, ReferenceActivePhysicalStep.dispatch, hs,
      CoordinatorRoundDispatch.dispatch]; cases CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput x) <;> rfl
  | dagger => simp only [ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
      birthFromSelection, ReferenceActivePhysicalStep.dispatch, hs]
  | live r owned base =>
      simp only [ReferenceActivePhysicalStepMeasurability.encodeCoordinator, birthFromSelection]
      simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch]
      cases CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x r owned base) <;> rfl
  | collection payload ledger saved =>
      simp only [ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
      simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch]
      split
      · rename_i hc
        let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
        let localInput := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
        change birthFromSelection _
          ((ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection localInput)).selection.map _) = _
        change birthFromSelection _
          ((ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection localInput)).selection.map
              ReferenceCollectionDispatchMeasurability.encodeSelection) = _
        rw [ReferenceCollectionDispatchMeasurability.collection_selection_coordinates]
        cases ho : CoordinatorRoundDispatch.dispatchCollection localInput with
        | continuing core prepared boundary scores =>
            have hu : prepared.clockStarted.clock.u = some cutoff :=
              congrArg CoordinatorPhaseClock.ClockRegisters.u prepared.clockStarted_frame.1 |>.trans
                prepared.inputsValid.clock_cutoff_eq
            simp only [birthFromSelection, Option.bind_some]
            simp only [hu, CoordinatorLiveChoiceRecorderStep.cutoffFromClock,
              Option.map_some, reduceCtorEq, ↓reduceIte]
            rfl
        | laterChosen core consistent started hstart instruction hi output hlocal data installed selected =>
            have heffect := CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val x.time
              clock ledger.pending started instruction core.clock_parameter_valid
              core.clock_registers_valid core.clock_start_time_valid hstart hi
            have hu : started.clock.u = none := heffect.2.2.2.1
            simp only [birthFromSelection, Option.bind_some, hu,
              CoordinatorLiveChoiceRecorderStep.cutoffFromClock, Option.map_none, ↓reduceIte]
            rfl
        | clockFailure _ _ => rfl
        | localFailure _ _ _ _ => rfl
        | coreFailure _ _ _ _ => rfl
        | laterReconstructionFailure _ _ _ _ _ _ _ _ => rfl
        | laterPrefixFailure _ _ _ _ _ _ _ _ _ => rfl
        | laterOrientationFailure _ _ _ _ _ _ _ _ => rfl
        | laterChoiceFailure _ _ _ _ _ _ _ _ _ _ _ => rfl
      · rfl

/-- Lossless code factor of the actual birth readout. -/
theorem birthPayload_eq_code (r : Record (rate := rate)) :
    birthPayload r = birthFromSelection
      (ReferenceActiveHorizonMeasurability.roundRecordCode r).2.1.1
      (ReferenceActiveHorizonMeasurability.roundRecordCode r).2.2.1.1 := by
  rw [(ReferenceActiveHorizonMeasurability.roundRecordCode_front r).1]
  change birthPayload r = birthFromSelection
    (ReferenceActivePhysicalStepMeasurability.encodeCoordinator r.input.state.coordinator) _
  rw [birthFromSelection_actual]
  unfold birthPayload
  rw [preparation_eq]
  cases (ReferenceActivePhysicalStep.prepare r.input).coordinator with
  | collection _ _ _ _ outcome => cases outcome <;> rfl
  | first _ => rfl
  | live _ _ _ _ => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

/-- Whether the encoded incoming coordinator is LIVE. -/
def incomingLive : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate → Bool
  | .inr (.inl _) => true
  | _ => false

/-- A successful selection on an incoming LIVE record, retaining failure as
false. Its two successful alternatives are continuing and cutoff. -/
def liveSelection (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
    (p := p) (rate := rate)) : Bool :=
  incomingLive code.2.1.1 && code.2.2.1.1.isSome

private theorem live_selection_tags (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome (ReferenceActivePhysicalStep.liveInput x r owned base)) :
    (match ReferenceActivePhysicalStep.DispatchCut.live r owned base outcome with
      | .live _ _ _ (.continuingChosen ..) => true | _ => false) =
    (((ReferenceActivePhysicalStep.DispatchCut.live r owned base outcome).selection.map
      ReferenceLiveDispatchOutputMeasurability.encodeSelection).isSome &&
      !(match ReferenceActivePhysicalStep.DispatchCut.live r owned base outcome with
        | .live _ _ _ (.cutoffChosen ..) => true | _ => false)) := by
  cases outcome
  all_goals first | rfl | simp [ReferenceActivePhysicalStep.DispatchCut.selection,
    ReferenceActivePhysicalStep.selectionAt]

private theorem continuing_selection_actual (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (match (ReferenceActivePhysicalStep.prepare x).coordinator with
      | .live _ _ _ (.continuingChosen ..) => true
      | _ => false) =
      ((incomingLive (ReferenceActivePhysicalStepMeasurability.encodeCoordinator x.state.coordinator) &&
        ((ReferenceActivePhysicalStep.dispatch x).selection.map
          ReferenceLiveDispatchOutputMeasurability.encodeSelection).isSome) &&
      !(ReferenceCollectionPhaseHistory.cutoffChosen x)) := by
  unfold ReferenceCollectionPhaseHistory.cutoffChosen ReferenceActivePhysicalStep.prepare
  cases hs : x.state.coordinator with
  | first =>
      simp only [ReferenceActivePhysicalStepMeasurability.encodeCoordinator, incomingLive,
        Bool.false_and, ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch]
      cases CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput x) <;> rfl
  | dagger => simp only [ReferenceActivePhysicalStepMeasurability.encodeCoordinator, incomingLive,
      Bool.false_and, ReferenceActivePhysicalStep.dispatch, hs]
  | collection payload ledger saved =>
      simp only [ReferenceActivePhysicalStepMeasurability.encodeCoordinator, incomingLive,
        Bool.false_and, ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch]
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hc]
        rfl
      · simp only [dite_eq_right hc]
  | live r owned base =>
      simp only [ReferenceActivePhysicalStepMeasurability.encodeCoordinator, incomingLive,
        Bool.true_and, ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch]
      exact live_selection_tags x r owned base
        (CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x r owned base))

/-- Continuing recognition uses the same generated selection code and the
actual pre-round cutoff check, rather than a guessed clock condition. -/
theorem continuing_eq_code (r : Record (rate := rate)) :
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r =
      (liveSelection (ReferenceActiveHorizonMeasurability.roundRecordCode r) && !isCutoff r) := by
  have h := continuing_selection_actual r.input
  have hcode : liveSelection (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
      (incomingLive (ReferenceActivePhysicalStepMeasurability.encodeCoordinator r.input.state.coordinator) &&
        ((ReferenceActivePhysicalStep.dispatch r.input).selection.map
          ReferenceLiveDispatchOutputMeasurability.encodeSelection).isSome) := by
    unfold liveSelection
    rw [(ReferenceActiveHorizonMeasurability.roundRecordCode_front r).1]
    rfl
  rw [hcode, isCutoff_eq]
  refine Eq.trans ?_ h
  unfold ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
  rw [preparation_eq]
  cases (ReferenceActivePhysicalStep.prepare r.input).coordinator with
  | live _ _ _ outcome => cases outcome <;> rfl
  | first _ => rfl
  | collection _ _ _ _ _ => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

private theorem cutoff_implies_live (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (h : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    incomingLive (ReferenceActivePhysicalStepMeasurability.encodeCoordinator x.state.coordinator) = true := by
  unfold ReferenceCollectionPhaseHistory.cutoffChosen ReferenceActivePhysicalStep.prepare at h
  cases hs : x.state.coordinator with
  | live _ _ _ => rfl
  | first =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch] at h
      cases CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput x) <;> cases h
  | dagger => simp only [ReferenceActivePhysicalStep.dispatch, hs, Bool.false_eq_true] at h
  | collection payload ledger saved =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch] at h
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hc] at h
        cases h
      · simp only [dite_eq_right hc] at h
        cases h

variable (rate)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

/-- A cutoff is recognized by the accepted incoming dispatcher observation:
LIVE plus a nonempty reset observation for its actual stored start. -/
def cutoffFlag (t : Fin p.T) (z : Source (p := p)) : Bool :=
  decide (∃ b : Fin p.T,
    (ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h b.val t z).Nonempty ∧
    ((ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z).map
      (fun code => incomingLive code.1)).getD false = true)

/-- The incoming test recognizes exactly the actual chosen cutoff, including
failure, malformed and absent records. -/
theorem cutoffFlag_eq (t : Fin p.T) (z : Source (p := p)) :
    cutoffFlag rate rewards C_star C_h t z =
      ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
        isCutoff).getD false := by
  unfold cutoffFlag
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none => simp only [ReferenceFirstCollectionPendingObservation.Q, hr,
      Finset.not_nonempty_empty, false_and, exists_false, decide_false,
      Option.map_none, Option.getD_none]
  | some r =>
    simp only [ReferenceSourcePrefixHistoryFiltration.incoming, hr, Option.map_some, Option.getD_some]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨b, hQ, hlive⟩
      cases hs : r.input.state.coordinator with
      | first => simp only [ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hs, incomingLive, Bool.false_eq_true] at hlive
      | dagger => simp only [ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hs, incomingLive, Bool.false_eq_true] at hlive
      | collection _ _ _ => simp only [ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hs, incomingLive, Bool.false_eq_true] at hlive
      | live registers owned base =>
          simp only [ReferenceFirstCollectionPendingObservation.Q, hr, hs] at hQ
          split_ifs at hQ with h
          · exact (isCutoff_eq r).trans h.2
          · exact False.elim (Finset.not_nonempty_empty hQ)
    · intro hcut
      have hlive := cutoff_implies_live r.input ((isCutoff_eq r).symm.trans hcut)
      cases hs : r.input.state.coordinator with
      | first => simp only [hs, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
          incomingLive, Bool.false_eq_true] at hlive
      | dagger => simp only [hs, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
          incomingLive, Bool.false_eq_true] at hlive
      | collection _ _ _ => simp only [hs, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
          incomingLive, Bool.false_eq_true] at hlive
      | live registers owned base =>
          refine ⟨registers.payload.sigma, ?_, ?_⟩
          · have htag := (isCutoff_eq r).symm.trans hcut
            simp only [ReferenceFirstCollectionPendingObservation.Q, hr, hs, htag,
              and_self, ↓reduceIte]
            exact ⟨⟨0, by have hm := p.two_le_m; omega⟩, Finset.mem_univ _⟩
          · simpa only [ReferenceActivePhysicalStepMeasurability.encodeState] using hlive

private theorem measurable_incomingLive : Measurable (incomingLive (p := p) (rate := rate)) :=
  measurable_const.sumElim (measurable_const.sumElim measurable_const)

/-- The test uses only the pre-round incoming field; no current fresh control
or receiver observation enters the cutoff recognition. -/
theorem cutoffFlag_measurable (t : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (cutoffFlag rate rewards C_star C_h t) := by
  let : MeasurableSpace (Source (p := p)) :=
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)
  have hlive : Measurable (fun z : Source (p := p) =>
      ((ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z).map
        (fun code => incomingLive code.1)).getD false) := by
    have hm := ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun q : ReferenceActivePhysicalStepMeasurability.StateCode p rate × Source (p := p) =>
        incomingLive q.1.1)
      ((measurable_incomingLive (rate := rate)).comp (measurable_fst.comp measurable_fst)) _
      (ReferenceSourcePrefixHistoryFiltration.incoming_measurable rate rewards C_star C_h control0 t)
    have hget : @Measurable (Option Bool) Bool
        (LaterAssignmentStartMeasurability.optionMeasurableSpace) inferInstance
        (fun b => b.getD false) := by
      convert ReferenceCollectionOutcomeMeasurability.measurable_optionalElim false
        (id : Bool → Bool) measurable_id using 1
      funext b
      cases b <;> rfl
    exact hget.comp hm
  apply measurable_to_bool (f := cutoffFlag rate rewards C_star C_h t)
  change MeasurableSet {z : Source (p := p) | cutoffFlag rate rewards C_star C_h t z = true}
  simp only [cutoffFlag, decide_eq_true_eq, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro b
  exact ((ReferenceFirstCollectionPendingObservation.Q_measurable
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0 b.val t)
      (Set.to_countable {s : Finset (Fin (p.m - 1)) | s.Nonempty} |>.measurableSet)).inter
    (hlive (measurableSet_singleton true))

/-- The strictly completed original history, advanced one original calendar
date at a time. An absent physical record does not advance the scan. -/
def pastPhase : ℕ → Source (p := p) → PastPhase rate
  | 0, _ => .firstLive
  | n + 1, z =>
      if hn : n < p.T then
        match ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h ⟨n, hn⟩ z with
        | none => pastPhase n z
        | some r => advance (pastPhase n z) r
      else pastPhase n z

/-- The forward calendar recursion is exactly the completed prefix of the
original physical suffix, including no-launch and terminal-launch sources. -/
theorem pastPhase_eq_scan (n : ℕ) (z : Source (p := p)) :
    pastPhase rate rewards C_star C_h n z =
      scan ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).take
        (n - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hlen : R.length = p.T - s :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  induction n with
  | zero => simp only [pastPhase, Nat.zero_sub, List.take_zero, scan_nil]
  | succ n ih =>
      rw [pastPhase]
      by_cases hn : n < p.T
      · rw [dite_eq_left hn]
        by_cases hs : s ≤ n
        · have hsub : n + 1 - s = (n - s) + 1 := by omega
          rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hs, ih]
          change (match R[n - s]? with
            | none => scan (R.take (n - s))
            | some r => advance (scan (R.take (n - s))) r) =
              scan (R.take (n + 1 - s))
          rw [hsub, List.take_add_one, scan_append]
          cases R[n - s]? <;> rfl
        · have hsub : n + 1 - s = 0 := by omega
          rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_right hs, ih, hsub]
          have hsub' : n - s = 0 := by omega
          rw [hsub']
      · rw [dite_eq_right hn, ih]
        change scan (R.take (n - s)) = scan (R.take (n + 1 - s))
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

variable {rate}

/-- Countable lossless coordinates for the scan decisions used by pending
membership. The continuous payload itself remains in `pastPhase`. -/
def phaseSummary : PastPhase rate → ℕ × Option (ℕ × ℕ)
  | .firstLive => (0, none)
  | .firstCollection => (1, none)
  | .replacementLive payload => (2, some (payload.sigma.val, 0))
  | .replacementCollection payload u => (3, some (payload.sigma.val, u))
  | .closed => (4, none)

abbrev SummaryInput := Bool × (Bool × (Option ℕ × ℕ))

/-- Literal finite-code transition for the countable summary. -/
def summaryAdvance (state : ℕ × Option (ℕ × ℕ)) (input : SummaryInput) :
    ℕ × Option (ℕ × ℕ) :=
  match state.1 with
  | 0 => if input.1 then (1, none) else state
  | 1 => match input.2.2.1 with
    | none => state
    | some b => (2, some (b, 0))
  | 2 => if input.2.1 then state else if input.1 then
      (3, state.2.map fun q => (q.1, input.2.2.2 + 1)) else (4, none)
  | 3 => if input.2.2.1.isSome then (4, none) else state
  | _ => (4, none)

private theorem phaseSummary_advance (phase : PastPhase rate) (r : Record (rate := rate)) :
    phaseSummary (advance phase r) = summaryAdvance (phaseSummary phase)
      (isCutoff r, ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r,
        (birthPayload r).map (fun payload => payload.sigma.val), r.input.time.val) := by
  cases phase with
  | firstLive => cases hc : isCutoff r <;> simp [advance, hc, phaseSummary, summaryAdvance]
  | firstCollection => cases hb : birthPayload r <;> simp [advance, hb, phaseSummary, summaryAdvance]
  | replacementLive payload =>
      cases ht : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r <;>
        cases hc : isCutoff r <;> simp [advance, ht, hc, phaseSummary, summaryAdvance]
  | replacementCollection payload u =>
      have hsome : ((birthPayload r).map (fun payload => payload.sigma.val)).isSome =
          ReferenceCollectionPhaseHistory.laterChosen r.input := by
        rw [Option.isSome_map, birthPayload_isSome]
      simp only [advance, phaseSummary, summaryAdvance, hsome]
      cases ReferenceCollectionPhaseHistory.laterChosen r.input <;> rfl
  | closed => rfl

private theorem measurable_optionBind {X Y W : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
    (f : Y → Option W) (hf : Measurable f) (g : X → Option Y) (hg : Measurable g) :
    Measurable (fun x => (g x).bind f) := by
  have hbind : Measurable (fun o : Option Y => o.bind f) := by
    apply measurable_comap_iff.mpr
    have hsum : Measurable (Sum.elim
        (fun y => Equiv.optionEquivSumPUnit W (f y))
        (fun _ : PUnit => Equiv.optionEquivSumPUnit W none)) :=
      (measurable_comap_iff.mp hf).sumElim measurable_const
    convert hsum.comp (comap_measurable (Equiv.optionEquivSumPUnit Y)) using 1
    funext o
    cases o <;> rfl
  exact hbind.comp hg

private theorem measurable_birthFromSelection : Measurable
    (fun q : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate ×
      Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) =>
        birthFromSelection q.1 q.2) := by
  let isCollection : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate → Bool :=
    fun c => match c with | .inr (.inr (.inl _)) => true | _ => false
  have hcol : Measurable isCollection :=
    measurable_const.sumElim (measurable_const.sumElim
      (measurable_const.sumElim measurable_const))
  have hv : Measurable (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
      (p := p) (rate := rate)) := comap_measurable _
  have hp := (measurable_fst.comp hv).comp
    (measurable_fst : Measurable (Prod.fst : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate → _))
  have hc := (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hv))).comp
    (measurable_fst : Measurable (Prod.fst : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate → _))
  have hs : Measurable (some : Payload (rate := rate) → Option (Payload (rate := rate))) :=
    measurable_comap_iff.mpr measurable_inl
  have hchoice : Measurable (fun choice : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
      if choice.1.cutoff = none then some choice.1.payload else none) :=
    Measurable.ite (measurableSet_eq_fun hc measurable_const) (hs.comp hp) measurable_const
  have hbind := measurable_optionBind _ hchoice
    (Prod.snd : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate ×
      Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) → _) measurable_snd
  have h : Measurable (fun q : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate ×
      Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) =>
        if isCollection q.1 = true then q.2.bind
          (fun choice => if choice.1.cutoff = none then some choice.1.payload else none) else none) :=
    Measurable.ite ((hcol.comp measurable_fst) (measurableSet_singleton true)) hbind measurable_const
  convert h using 1
  funext q
  rcases q with ⟨c, selected⟩
  cases c with
  | inl _ => rfl
  | inr c => cases c with
    | inl _ => rfl
    | inr c => cases c <;> rfl

variable (rate)

/-- The optional original round-end code; absence is retained. -/
def sourceCode (t : Fin p.T) (z : Source (p := p)) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
    ReferenceActiveHorizonMeasurability.roundRecordCode

private theorem sourceCode_borel (t : Fin p.T) :
    Measurable (sourceCode rate rewards C_star C_h t) := by
  have h := (measurable_pi_apply (⟨t.val, by omega⟩ : Fin (t.val + 1))).comp
    (ReferenceInspectedPastRoundObservations.measurable_pastRoundObservations
      rate rewards C_star C_h (t.val + 1) (by omega))
  exact h

private theorem sourceCode_measurable (n : ℕ) (t : Fin p.T) (ht : t.val < n) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      (sourceCode rate rewards C_star C_h t) := by
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  have h := (sourceCode_borel rate rewards C_star C_h t).comp
    (comap_measurable (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n))
  convert h using 1
  funext z
  exact ReferenceFirstReplacementCollectionCommonStopObservation.actualRecordCode_factor
    rate rewards C_star C_h control0 n t ht z

variable {rate}

/-- Read only countable decision coordinates from the unchanged full code. -/
def summaryInput (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
    (p := p) (rate := rate)) (cut : Bool) : SummaryInput :=
  (cut, liveSelection code && !cut,
    (birthFromSelection code.2.1.1 code.2.2.1.1).map (fun payload => payload.sigma.val), code.1)

private theorem measurable_summaryInput : Measurable
    (fun q : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) × Bool => summaryInput q.1 q.2) := by
  have hsome : Measurable (fun c : Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) =>
      c.isSome) := by
    convert ReferenceCollectionOutcomeMeasurability.measurable_optionalElim false
      (fun _ : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate => true) measurable_const using 1
    funext c
    cases c <;> rfl
  have hfront : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) => code.2.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp (measurable_snd.comp (measurable_snd)))
  have hcoord : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) => code.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hlive : Measurable (liveSelection (p := p) (rate := rate)) :=
    (measurable_of_countable (fun q : Bool × Bool => q.1 && q.2)).comp
      (((measurable_incomingLive (rate := rate)).comp hcoord).prodMk (hsome.comp hfront))
  have hb := measurable_birthFromSelection (rate := rate) |>.comp (hcoord.prodMk hfront)
  have hsig : Measurable (fun payload : Payload (rate := rate) => payload.sigma.val) :=
    (measurable_of_countable (fun t : Fin p.T => t.val)).comp
      (ReferenceCollectionDispatchMeasurability.measurable_payloadSigma (rate := rate))
  have hsomeNat : Measurable (fun payload : Payload (rate := rate) =>
      (some payload.sigma.val : Option ℕ)) :=
    (measurable_of_countable (some : ℕ → Option ℕ)).comp hsig
  have hmap := (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim
    (none : Option ℕ) (fun payload : Payload (rate := rate) => some payload.sigma.val) hsomeNat).comp hb
  have hmap' : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) =>
        (birthFromSelection code.2.1.1 code.2.2.1.1).map (fun payload => payload.sigma.val)) := by
    convert hmap using 1
    funext code
    dsimp only [Function.comp_apply]
    cases birthFromSelection code.2.1.1 code.2.2.1.1 <;> rfl
  exact measurable_snd.prodMk
    (((measurable_of_countable (fun q : Bool × Bool => q.1 && !q.2)).comp
      ((hlive.comp measurable_fst).prodMk measurable_snd)).prodMk
      ((hmap'.comp measurable_fst).prodMk (measurable_fst.comp measurable_fst)))

variable (rate)

private theorem phaseSummary_next (n : ℕ) (hn : n < p.T) (z : Source (p := p)) :
    phaseSummary (pastPhase rate rewards C_star C_h (n + 1) z) =
      match sourceCode rate rewards C_star C_h ⟨n, hn⟩ z with
      | none => phaseSummary (pastPhase rate rewards C_star C_h n z)
      | some code => summaryAdvance (phaseSummary (pastPhase rate rewards C_star C_h n z))
          (summaryInput code (cutoffFlag rate rewards C_star C_h ⟨n, hn⟩ z)) := by
  rw [pastPhase, dite_eq_left hn]
  unfold sourceCode
  rw [cutoffFlag_eq]
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h ⟨n, hn⟩ z with
  | none => rfl
  | some r =>
      simp only [Option.map_some, Option.getD_some]
      rw [phaseSummary_advance, continuing_eq_code, birthPayload_eq_code]
      rfl

private theorem laterOptionSpace_countable {A : Type*} [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A] :
    @LaterAssignmentStartMeasurability.optionMeasurableSpace A inferInstance = ⊤ := by
  apply MeasurableSpace.ext
  intro U
  constructor
  · intro _; trivial
  · intro _
    rw [LaterAssignmentStartMeasurability.optionMeasurableSpace,
      MeasurableSpace.measurableSet_comap]
    let e := Equiv.optionEquivSumPUnit A
    have hU : MeasurableSet (e '' U) := by
      rw [measurableSet_sum_iff]
      exact ⟨(Set.to_countable _).measurableSet, (Set.to_countable _).measurableSet⟩
    exact ⟨e '' U, hU, e.injective.preimage_image U⟩

/-- The countable actual scan coordinates are adapted before the next
original round, with no continuity carrier made discrete. -/
theorem phaseSummary_measurable (n : ℕ) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      (fun z : Source (p := p) => phaseSummary (pastPhase rate rewards C_star C_h n z)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
      let : MeasurableSpace (Source (p := p)) := F (n + 1 + 1)
      have hprev : Measurable (fun z : Source (p := p) =>
          phaseSummary (pastPhase rate rewards C_star C_h n z)) :=
        ih.mono (F.mono (show n + 1 ≤ n + 1 + 1 by omega)) le_rfl
      by_cases hn : n < p.T
      · have hcode := sourceCode_measurable rate rewards C_star C_h control0 (n + 1) ⟨n, hn⟩ (Nat.lt_succ_self n)
        have hcut : Measurable (cutoffFlag rate rewards C_star C_h ⟨n, hn⟩) :=
          (cutoffFlag_measurable rate rewards C_star C_h control0 ⟨n, hn⟩).mono
            (F.mono (show n + 1 ≤ n + 1 + 1 by omega)) le_rfl
        have hinput := (ReferenceCollectionOutcomeMeasurability.measurable_mapOptional _
          (measurable_summaryInput (rate := rate))).comp (hcode.prodMk hcut)
        rw [laterOptionSpace_countable (A := SummaryInput)] at hinput
        have hstep := (measurable_of_countable (fun q : (ℕ × Option (ℕ × ℕ)) × Option SummaryInput =>
          match q.2 with | none => q.1 | some input => summaryAdvance q.1 input)).comp
            (hprev.prodMk hinput)
        convert hstep using 1
        funext z
        rw [phaseSummary_next rate rewards C_star C_h n hn z]
        dsimp only [Function.comp_apply, ReferenceCollectionOutcomeMeasurability.mapOptional]
        cases sourceCode rate rewards C_star C_h ⟨n, hn⟩ z <;> rfl
      · convert hprev using 1
        funext z
        simp only [pastPhase, dite_eq_right hn]

/-- Actual candidate payload and collection onset carried by the past scan.
The live case uses the current incoming date only; its raw pending set is
empty unless the actual pre-round cutoff check succeeds. -/
def payloadOnset (n : ℕ) (z : Source (p := p)) : Option (Payload (rate := rate) × ℕ) :=
  match pastPhase rate rewards C_star C_h n z with
  | .replacementLive payload => some (payload, n + 1)
  | .replacementCollection payload u => some (payload, u)
  | .firstLive | .firstCollection | .closed => none

/-- Countable pending coordinates, read from the actual past scan. -/
def pendingCode (n : ℕ) (z : Source (p := p)) : Option (ℕ × ℕ) :=
  let q := phaseSummary (pastPhase rate rewards C_star C_h n z)
  if q.1 = 2 then q.2.map (fun pair : ℕ × ℕ => (pair.1, n + 1))
  else if q.1 = 3 then q.2 else none

theorem pendingCode_eq (n : ℕ) (z : Source (p := p)) :
    pendingCode rate rewards C_star C_h n z =
      (payloadOnset rate rewards C_star C_h n z).map (fun pair => (pair.1.sigma.val, pair.2)) := by
  unfold pendingCode payloadOnset
  cases pastPhase rate rewards C_star C_h n z <;> rfl

theorem pendingCode_measurable (n : ℕ) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      (pendingCode rate rewards C_star C_h n) :=
  (measurable_of_countable (fun q : ℕ × Option (ℕ × ℕ) =>
    if q.1 = 2 then q.2.map (fun pair : ℕ × ℕ => (pair.1, n + 1))
    else if q.1 = 3 then q.2 else none)).comp
      (phaseSummary_measurable rate rewards C_star C_h control0 n)

/-- Raw actual incoming pending labels for this forward scan. The underlying
incoming observer performs the actual pre-round cutoff reset, and otherwise
reads the same start's ledger. It does not read an arm or feedback. -/
def Praw (n : ℕ) (z : Source (p := p)) : Finset (Fin (p.m - 1)) :=
  if hn : n < p.T then
    match payloadOnset rate rewards C_star C_h n z with
    | none => ∅
    | some (payload, _) =>
        ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
          payload.sigma.val ⟨n, hn⟩ z
  else ∅

/-- The actual pending observation with the strict-past common mask. The
mask never removes the detecting record or truncates the physical list. -/
def P_repl (n : ℕ) (z : Source (p := p)) : Finset (Fin (p.m - 1)) :=
  (Praw rate rewards C_star C_h n z).filter fun i =>
    match payloadOnset rate rewards C_star C_h n z with
    | none => false
    | some (_, u) => !ReferenceFirstReplacementCollectionCommonStopObservation.L
        rate rewards C_star C_h control0
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) u i n z

/-- Incoming raw pending membership is adapted on every natural date. -/
theorem Praw_measurable (n : ℕ) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      (Praw rate rewards C_star C_h n) := by
  let : MeasurableSpace (Source (p := p)) :=
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)
  by_cases hn : n < p.T
  · have hread : Measurable (fun q : Option (ℕ × ℕ) × Source (p := p) =>
        match q.1 with
        | none => (∅ : Finset (Fin (p.m - 1)))
        | some pair => ReferenceFirstCollectionPendingObservation.Q
            rate rewards C_star C_h pair.1 ⟨n, hn⟩ q.2) := by
      apply measurable_from_prod_countable_right
      intro code
      cases code with
      | none => exact measurable_const
      | some pair =>
          exact ReferenceFirstCollectionPendingObservation.Q_measurable control0 pair.1 ⟨n, hn⟩
    have h := hread.comp ((pendingCode_measurable rate rewards C_star C_h control0 n).prodMk measurable_id)
    convert h using 1
    funext z
    simp only [Praw, dite_eq_left hn, pendingCode_eq, Function.comp_apply]
    cases payloadOnset rate rewards C_star C_h n z <;> rfl
  · convert (measurable_const : Measurable (fun _ : Source (p := p) =>
      (∅ : Finset (Fin (p.m - 1))))) using 1
    funext z
    simp only [Praw, dite_eq_right hn]

/-- The masked actual task membership is pre-round measurable. The variable
physical launch date is handled only on already-launched strata. -/
theorem P_repl_mem_measurable (n : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      {z : Source (p := p) | i ∈ P_repl rate rewards C_star C_h control0 n z} := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  by_cases hn : n < p.T
  · have heq : {z : Source (p := p) | i ∈ P_repl rate rewards C_star C_h control0 n z} =
        ⋃ b : ℕ, ⋃ u : ℕ, ⋃ s : Fin (n + 1),
          ({z | pendingCode rate rewards C_star C_h n z = some (b, u)} ∩
            ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
              (rate := rate) rewards C_star C_h s.val) ∩
          ({z | i ∈ ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h b ⟨n, hn⟩ z} ∩
            {z | ReferenceFirstReplacementCollectionCommonStopObservation.L
              rate rewards C_star C_h control0 s.val u i n z = false}) := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro hi
        cases ho : payloadOnset rate rewards C_star C_h n z with
        | none => simp only [P_repl, Praw, dite_eq_left hn, ho, Finset.notMem_empty,
            Finset.mem_filter, false_and] at hi
        | some pair =>
          rcases pair with ⟨payload, u⟩
          simp only [P_repl, Praw, dite_eq_left hn, ho, Finset.mem_filter, Bool.not_eq_true'] at hi
          have hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h n z := by
            by_contra hz
            rw [ReferenceFirstCollectionPendingObservation.Q_eq_empty_of_not_launchBy
              payload.sigma.val ⟨n, hn⟩ z hz] at hi
            exact Finset.notMem_empty i hi.1
          refine ⟨payload.sigma.val, u, ⟨ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h, by have hs := hz.2; omega⟩, ?_, hi⟩
          exact ⟨by rw [pendingCode_eq, ho]; rfl, hz.1, rfl⟩
      · rintro ⟨b, u, s, ⟨hcode, hs⟩, hQ, hL⟩
        change _ ∧ ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s.val at hs
        rw [pendingCode_eq] at hcode
        obtain ⟨pair, ho, hpair⟩ := Option.map_eq_some_iff.mp hcode
        rcases pair with ⟨payload, onset⟩
        have hfields := Prod.mk.inj hpair
        dsimp only at hfields
        simp only [P_repl, Praw, dite_eq_left hn, ho, Finset.mem_filter, Bool.not_eq_true']
        rw [hfields.1, hfields.2, hs.2]
        exact ⟨hQ, hL⟩
    rw [heq]
    exact MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun u =>
      MeasurableSet.iUnion fun s =>
        (((pendingCode_measurable rate rewards C_star C_h control0 n)
          (measurableSet_singleton (some (b, u)))).inter
          (ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_measurable
            rate rewards C_star C_h control0 ⟨n, hn⟩ s.val (Nat.le_of_lt_succ s.isLt))).inter
        ((ReferenceFirstCollectionPendingObservation.Q_mem_measurable control0 b i ⟨n, hn⟩).inter
          ((ReferenceFirstReplacementCollectionCommonStopObservation.L_measurable
            rate rewards C_star C_h control0 s.val u n i) (measurableSet_singleton false)))
  · simp only [P_repl, Praw, dite_eq_right hn, Finset.filter_empty, Finset.notMem_empty,
      Set.ofPred_false, MeasurableSet.empty]

/-- Every pending label factors through the SAME strict original prefix. -/
theorem P_repl_factor (n : ℕ) (z : Source (p := p)) :
    P_repl rate rewards C_star C_h control0 n z =
      P_repl rate rewards C_star C_h control0 n
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  ext i
  have h := P_repl_mem_measurable rate rewards C_star C_h control0 n i
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at h
  obtain ⟨B, _hB, he⟩ := h
  change z ∈ {z | i ∈ P_repl rate rewards C_star C_h control0 n z} ↔
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z ∈
      {z | i ∈ P_repl rate rewards C_star C_h control0 n z}
  rw [← he]
  change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z ∈ B ↔
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) ∈ B
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 n n le_rfl]

include control0 in
/-- Ambient Borel measurability of the raw pending observation on the
unchanged original product source. -/
theorem Praw_borel (n : ℕ) :
    Measurable (Praw rate rewards C_star C_h n) :=
  (Praw_measurable rate rewards C_star C_h control0 n).mono
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (n + 1)) le_rfl

/-- Ambient Borel measurability of each masked pending membership event. -/
theorem P_repl_mem_borel (n : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet {z : Source (p := p) | i ∈ P_repl rate rewards C_star C_h control0 n z} :=
  (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (n + 1)
    _ (P_repl_mem_measurable rate rewards C_star C_h control0 n i)

@[simp] theorem Praw_of_horizon_le (n : ℕ) (hn : p.T ≤ n) (z : Source (p := p)) :
    Praw rate rewards C_star C_h n z = ∅ := by
  simp only [Praw, dite_eq_right (Nat.not_lt.mpr hn)]

@[simp] theorem P_repl_of_horizon_le (n : ℕ) (hn : p.T ≤ n) (z : Source (p := p)) :
    P_repl rate rewards C_star C_h control0 n z = ∅ := by
  simp only [P_repl, Praw_of_horizon_le rate rewards C_star C_h n hn, Finset.filter_empty]

private theorem actual_lookup_of_prefix (z : Source (p := p))
    (K : List (Record (rate := rate))) (c : ℕ)
    (hprefix : K <+: (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).drop c)
    (a : Fin K.length)
    (htime : (K.get a).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + c + a.val) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (K.get a).input.time z = some (K.get a) := by
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hs : s ≤ (K.get a).input.time.val := by rw [htime]; omega
  have hi : (K.get a).input.time.val - s = c + a.val := by rw [htime]; omega
  obtain ⟨rest, hrest⟩ := hprefix
  rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hs, hi,
    ← List.getElem?_drop, ← hrest, List.getElem?_append_left a.isLt]
  exact List.getElem?_eq_getElem a.isLt

/-- Original-source correspondence of the forward pending construction with
EVERY coordinate of the literal first-replacement collection. The root has
only the original source data. No cutoff, birth or successful branch is
assumed; the absent and nonmatching branches stay explicit. -/
theorem complete_first_replacement_pending_coordinates :
    ∀ z : Source (p := p),
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let K := cut :: (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            ∀ a : Fin K.length,
              let n := u - 1 + a.val
              payloadOnset rate rewards C_star C_h n z = some (payload, u) ∧
              ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
                (K.get a).input.time z = some (K.get a) ∧
              Praw rate rewards C_star C_h n z =
                ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
                  payload.sigma.val (K.get a).input.time z ∧
              ∀ i : Fin (p.m - 1),
                (i ∈ P_repl rate rewards C_star C_h control0 n z ↔
                  i ∈ ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
                    payload.sigma.val (K.get a).input.time z ∧
                  a.val ≤ ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopIndex
                    s K z rewards C_star C_h control0 i)
          | _ => True
      | _ => True := by
  intro z
  have hQ :=
    ReferenceFirstReplacementCollectionStoppedCompositeQuota.complete_first_replacement_collection_stopped_composite_quota
      rate z rewards C_star C_h control0
  obtain ⟨_, _, _, _, hO⟩ :=
    ReferenceFirstReplacementCollectionCommonStopObservation.complete_first_replacement_common_stop_observation
      rate rewards C_star C_h control0
  specialize hO z
  dsimp only at hQ hO ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    rw [hb] at hQ hO
    dsimp only at hQ hO ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      rw [hbirth] at hQ hO
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hQ hO ⊢
      have hp : birthPayload birth = some installed.registers.payload := by
        simp only [birthPayload, hbirth]
        rfl
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        rw [hc] at hQ hO
        dsimp only at hQ hO ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          rw [hcut] at hQ hO
          cases outcome <;> try trivial
          dsimp only at hQ hO ⊢
          let payload := installed.registers.payload
          let u := cut.input.time.val + 1
          let K := cut :: (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          obtain ⟨hcuttime, hcalendar, _hinjective, _hquota⟩ := hQ
          change cut.input.time.val = s + c at hcuttime
          obtain ⟨hmask, _hprefixMask⟩ := hO
          have hcutTag : isCutoff cut = true := by simp only [isCutoff, hcut]
          have hscan := scan_collection_coordinate R birth payload hb hp cut hc hcutTag
          have hprefix : K <+: R.drop c := collection_prefix R c cut hc
          intro a
          let n := u - 1 + a.val
          have htime : (K.get a).input.time.val = n := by
            have ht := hcalendar a
            change (K.get a).input.time.val + 1 = u + a.val at ht
            dsimp only [n, u] at ht ⊢
            omega
          have hindex : n - s = c + a.val := by dsimp only [n, u]; omega
          have hphase : pastPhase rate rewards C_star C_h n z =
              if a.val = 0 then .replacementLive payload
              else .replacementCollection payload u := by
            rw [pastPhase_eq_scan]
            change scan (R.take (n - s)) = _
            rw [hindex]
            exact hscan a
          have honset : payloadOnset rate rewards C_star C_h n z = some (payload, u) := by
            unfold payloadOnset
            rw [hphase]
            by_cases ha : a.val = 0
            · simp only [ha, ↓reduceIte]
              have hnu : n + 1 = u := by dsimp only [n, u]; omega
              rw [hnu]
              rfl
            · simp only [ha, ↓reduceIte]
              rfl
          have hn : n < p.T := htime ▸ (K.get a).input.time.isLt
          have hfin : (⟨n, hn⟩ : Fin p.T) = (K.get a).input.time := Fin.ext htime.symm
          have hraw : Praw rate rewards C_star C_h n z =
              ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
                payload.sigma.val (K.get a).input.time z := by
            simp only [Praw, dite_eq_left hn, honset, hfin]
          have hlookup : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
              (K.get a).input.time z = some (K.get a) := by
            apply actual_lookup_of_prefix rate rewards C_star C_h z K c hprefix a
            rw [htime]
            dsimp only [n, u]
            omega
          refine ⟨honset, hlookup, hraw, ?_⟩
          intro i
          have hmem : i ∈ P_repl rate rewards C_star C_h control0 n z ↔
              i ∈ ReferenceFirstCollectionPendingObservation.Q rate rewards C_star C_h
                payload.sigma.val (K.get a).input.time z ∧
              a.val ≤ ReferenceFirstReplacementCollectionStoppedCompositeQuota.commonStopIndex
                s K z rewards C_star C_h control0 i := by
            simp only [P_repl, Finset.mem_filter, honset, Bool.not_eq_true']
            rw [hraw]
            exact and_congr_right fun _ => hmask i a
          exact hmem

end Bandits.Support.ReferenceFirstReplacementCollectionPendingFoundation

end
