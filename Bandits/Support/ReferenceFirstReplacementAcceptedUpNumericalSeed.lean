/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionNextStartNumericalSeed
public import Bandits.Support.ReferenceCompleteAcceptedUpLedgerNumericalReplay

import Lean.Elab.Tactic.Omega

/-!
# First replacement seed for an actual accepted UP

Source evidence: ZIP4 Appendix A:42-64; 06:46-61,80-100,192-233,391-408;
04:157-174. The first collection boundary is identified in the original
complete physical suffix. All numerical replays retain the actual installed
payload and the actual cutoff initializer.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementAcceptedUpNumericalSeed

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem takeWhile_boundary {α : Type*} (test : α → Bool) (xs : List α)
    (h : (xs.takeWhile test).length < xs.length) :
    test xs[(xs.takeWhile test).length] = false := by
  induction xs with
  | nil => simp only [List.takeWhile_nil, List.length_nil] at h; omega
  | cons x xs ih =>
      cases hx : test x with
      | false => simp only [List.takeWhile_cons, hx, Bool.false_eq_true, ↓reduceIte,
          List.length_nil, List.getElem_cons_zero]
      | true =>
          simp only [List.takeWhile_cons, hx, ↓reduceIte, List.length_cons] at h ⊢
          exact ih (by omega)

/-- A retained next record after the literal collection window is a later
choice. This uses the stopping predicate, not an assumed successful sample. -/
private theorem collection_window_boundary
    (R : List (RoundRecord (p := p) (rate := rate))) (w : ℕ)
    (hv : w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length < R.length) :
    w < R.length ∧
    ReferenceCollectionPhaseHistory.laterChosen
      R[w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length].input = true := by
  have hw : w < R.length := by omega
  let tail := R.drop (w + 1)
  let W := tail.takeWhile (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
  have hC : ReferenceCollectionPhaseHistory.collectionWindow R w = R[w] :: W := by
    unfold ReferenceCollectionPhaseHistory.collectionWindow
    rw [List.drop_eq_getElem_cons hw]
    simp only [List.take_succ_cons, List.take_zero, List.singleton_append]
    rfl
  have hW : W.length < tail.length := by
    have hlen : tail.length = R.length - (w + 1) := List.length_drop
    rw [hC, List.length_cons] at hv
    omega
  have hstop := takeWhile_boundary
    (fun r : RoundRecord (p := p) (rate := rate) =>
      !ReferenceCollectionPhaseHistory.laterChosen r.input) tail hW
  have hindex : w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length =
      w + 1 + W.length := by rw [hC, List.length_cons]; omega
  refine ⟨hw, ?_⟩
  dsimp only [tail] at hstop
  rw [List.getElem_drop] at hstop
  change (!ReferenceCollectionPhaseHistory.laterChosen R[w + 1 + W.length].input) = false at hstop
  have hb : ReferenceCollectionPhaseHistory.laterChosen R[w + 1 + W.length].input = true := by
    cases hb : ReferenceCollectionPhaseHistory.laterChosen R[w + 1 + W.length].input <;>
      simp_all only [Bool.not_false, Bool.not_true, Bool.true_eq_false]
  simpa only [hindex] using hb

private theorem connected_successor
    (R : List (RoundRecord (p := p) (rate := rate))) (initial final : ReferenceActivePhysicalStep.State p rate)
    (hchain : Connected initial R final) (n : ℕ) (hn : n + 1 < R.length) :
    R[n + 1].input.state = R[n].output.next := by
  induction R generalizing initial n with
  | nil => simp only [List.length_nil] at hn; omega
  | cons r rest ih =>
      cases n with
      | zero =>
          cases rest with
          | nil => simp only [List.length_cons, List.length_nil] at hn; omega
          | cons next tail => exact hchain.2.1
      | succ n =>
          exact ih r.output.next hchain.2 n (by simp only [List.length_cons] at hn; omega)

private theorem collection_choice_pending
    (x : RoundInput p rate) (payload : Payload rate) (ledger : Ledger rate)
    (saved : Option (Fin p.T × Bool)) (c : Choice rate)
    (hstate : x.state.coordinator = .collection payload ledger saved)
    (hc : choice x = some c) : ledger.pending.Nonempty := by
  unfold choice at hc
  split at hc
  · contradiction
  next =>
    change choiceOfCut (dispatch x) = some c at hc
    simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hc
    split at hc
    next hcut =>
      let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := collectionClock payload ledger saved cutoff
      change choiceOfCut (.collection payload ledger clock cutoff
        (CoordinatorRoundDispatch.dispatchCollection
          (collectionInput x payload ledger clock cutoff))) = some c at hc
      cases hout : CoordinatorRoundDispatch.dispatchCollection
          (collectionInput x payload ledger clock cutoff) <;>
        simp only [hout, choiceOfCut, reduceCtorEq] at hc
      rename_i core snapshot boundary scores
      exact snapshot.inputsValid.pending_nonempty
    · simp only [choiceOfCut, reduceCtorEq] at hc

private theorem completed_choice
    (r : RoundRecord (p := p) (rate := rate))
    (h : (extractRound r).isSome = true) : ∃ c, choice r.input = some c := by
  cases hc : choice r.input with
  | none => simp only [extractRound, hc, Option.bind_none, Option.isSome_none,
      Bool.false_eq_true] at h
  | some c => exact ⟨c, rfl⟩

private theorem record_eq_of_input
    (record : RoundRecord (p := p) (rate := rate)) (x : RoundInput p rate)
    (h : record.input = x) : record = ⟨x, step x, rfl⟩ := by
  cases record with
  | mk input output houtput =>
      dsimp only at h
      subst input
      subst output
      rfl

private theorem complete_record_time
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[b.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + b.val := by
  have h := congrArg (fun xs : List ℕ => xs[b.val]?)
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
      rate source rewards C_star C_h)
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate source rewards C_star C_h
  have hb : b.val < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h := by rw [← hlen]; exact b.isLt
  rw [List.getElem?_map, List.getElem?_eq_getElem b.isLt, Option.map_some,
    ReferenceActivePhysicalHorizon.calendar,
    List.getElem?_range' (s := ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h) (step := 1) hb] at h
  simpa only [Nat.one_mul, Option.some.injEq] using h

private theorem complete_birth_index_unique
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (b b' : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (payload : Payload rate)
    (hb : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[b.val] payload)
    (hb' : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[b'.val] payload) : b' = b := by
  have ht := (ReferenceAssignmentPayloadChronology.installationBirth_time_eq _ _ hb').symm.trans
    (ReferenceAssignmentPayloadChronology.installationBirth_time_eq _ _ hb)
  rw [complete_record_time rewards C_star C_h source b',
    complete_record_time rewards C_star C_h source b] at ht
  apply Fin.ext
  omega

private theorem complete_crossing
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true := by
  apply (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate source rewards C_star C_h).mp
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hnil := (ReferenceCompletePhysicalHistory.no_launch_complete_history
        rate source rewards C_star C_h hl).2.1
      have hk := k.isLt
      have hlen := congrArg List.length hnil
      simp only [List.length_nil] at hlen
      omega
  | some initial => rfl

private theorem complete_epoch_eq
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (span : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h +
        (p.T - ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h) ≤ p.T) :
    (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hc
      (p.T - ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h) span).records =
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h := by
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hc
  have hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some initial := by
    exact (Option.some_get ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).mpr hc)).symm
  exact (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate source rewards C_star C_h initial hl).symm

section StreamAlignment

variable (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (count : ℕ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (span : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (short : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hc count span).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (p := p) (rate := rate) source rewards C_star C_h count hc span short)

local notation "E" => ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
  source rewards C_star C_h hc count span
local notation "R" => ReferenceActivePhysicalHorizon.Run.records
  (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
    source rewards C_star C_h hc count span)
local notation "w" => List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R)
local notation "C" => ReferenceCollectionPhaseHistory.collectionWindow R w

private theorem stream_successor_state
    (hv : w + (C).length < (R).length) :
    (R[w + d.stream.ell]'(by
      have hle := d.stream.withinWindow
      have hw := d.stream.windowIsActual
      rw [hw] at hle
      change d.stream.ell ≤ (C).length at hle
      omega)).input.state.coordinator =
      .collection d.stream.payload d.ledger d.stream.saved := by
  have hwindow : d.stream.window = C := d.stream.windowIsActual
  have hle : d.stream.ell ≤ (C).length := by
    simpa only [hwindow] using d.stream.withinWindow
  have hlast := d.lastIsLast
  have hlastlt := d.last.isLt
  have halign := (d.stream.alignment
    ⟨d.last.val, lt_of_lt_of_le d.last.isLt d.stream.withinWindow⟩).1
  have hrecord := d.recordAt
  rw [List.getElem?_eq_getElem (lt_of_lt_of_le d.last.isLt d.stream.withinWindow)] at hrecord
  rw [Option.some.inj hrecord] at halign
  have hprev : R[w + d.last.val] = d.record :=
    (List.getElem?_eq_some_iff.mp halign).2
  have hchain := (E).connected
  have hadj := connected_successor R _ _ hchain (w + d.last.val) (by omega)
  have hindex : w + d.last.val + 1 = w + d.stream.ell := by omega
  rw [hprev] at hadj
  have hadj' : (R[w + d.stream.ell]'(by omega)).input.state = d.record.output.next := by
    simpa only [hindex] using hadj
  exact (congrArg (fun state => state.coordinator) hadj').trans d.actualNextCoordinator

/-- The checked first window cannot continue after an empty-pending FINISH.
The actual replacement remains outside the old collection window. -/
private theorem stream_boundary_alignment
    (hv : w + (C).length < (R).length)
    (hcomplete : ∀ r ∈ C, (extractRound r).isSome = true) :
    d.stream.ell = (C).length ∧ d.ledger.pending = ∅ := by
  have hwindow : d.stream.window = C := d.stream.windowIsActual
  have hle : d.stream.ell ≤ (C).length := by
    simpa only [hwindow] using d.stream.withinWindow
  have hsucc := stream_successor_state source rewards C_star C_h count hc span short d hv
  have heq : d.stream.ell = (C).length := by
    by_contra hne
    have hlt : d.stream.ell < d.stream.window.length := by rw [hwindow]; omega
    have halign := (d.stream.alignment ⟨d.stream.ell, hlt⟩).1
    have hr : R[w + d.stream.ell] = d.stream.window[d.stream.ell] :=
      (List.getElem?_eq_some_iff.mp halign).2
    have hmem : d.stream.window[d.stream.ell] ∈ C := by
      rw [← hwindow]
      exact List.getElem_mem hlt
    obtain ⟨c, hchoice⟩ := completed_choice _ (hcomplete _ hmem)
    rw [← hr] at hchoice
    have hpending := collection_choice_pending _ _ _ _ c hsucc hchoice
    cases d.outcome with
    | exhausted _ hexhausted _ _ _ => omega
    | empty e => exact (Finset.not_nonempty_iff_eq_empty.mpr e.pendingEmpty) hpending
  have hlater := (collection_window_boundary R w hv).2
  have hsucc' : R[w + (C).length].input.state.coordinator =
      .collection d.stream.payload d.ledger d.stream.saved := by
    simpa only [heq] using hsucc
  obtain ⟨payload, ledger, saved, hstate, hempty⟩ :=
    ReferenceCollectionPhaseHistory.laterChosen_pending_empty _ hlater
  rw [hsucc'] at hstate
  have hledger := (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj hstate).2.1
  exact ⟨heq, hledger.symm ▸ hempty⟩

private theorem stream_next_input
    (hepoch : R = ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hpending : d.ledger.pending = ∅)
    (hboundary : w + d.stream.ell = b.val) :
    match d.outcome with
    | .exhausted _ _ _ _ _ => False
    | .empty e => match e.nextBoundary with
      | .terminal _ _ => False
      | .next _ _ x _ _ _ _ _ _ _ _ _ =>
          x = (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[b.val].input := by
  have hlast := d.lastIsLast
  have hlasttime := (d.stream.alignment
    ⟨d.last.val, lt_of_lt_of_le d.last.isLt d.stream.withinWindow⟩).2
  have hlastrecord := d.recordAt
  rw [List.getElem?_eq_getElem (lt_of_lt_of_le d.last.isLt d.stream.withinWindow)] at hlastrecord
  rw [Option.some.inj hlastrecord] at hlasttime
  dsimp only at hlasttime
  have hlasttime' : d.record.input.time.val + 1 =
      ReferenceFirstCollectionReadyStream.startTime (rate := rate)
        source rewards C_star C_h + b.val := by omega
  have hbtime := complete_record_time rewards C_star C_h source b
  have hbT := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[b.val].input.time.isLt
  cases houtcome : d.outcome with
  | exhausted hnonempty _ _ _ _ =>
      exact (Finset.not_nonempty_iff_eq_empty.mpr hpending) hnonempty
  | empty e =>
      cases hn : e.nextBoundary with
      | terminal htime _ =>
          have ht : (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h)[b.val].input.time.val = p.T := by
            calc
              _ = ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                  source rewards C_star C_h + b.val := hbtime
              _ = d.record.input.time.val + 1 := hlasttime'.symm
              _ = p.T := htime
          exact False.elim ((Nat.ne_of_lt hbT) ht)
      | next _ _ x _ _ _ _ _ _ _ hrun _ =>
          simp only [hn]
          apply hrun
          rw [hboundary, hepoch]
          exact List.getElem?_eq_getElem b.isLt

end StreamAlignment

private theorem complete_first_window_completed
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hb : b.val =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)).length +
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)).length).length) :
    ∀ r ∈ ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)).length,
      (extractRound r).isSome = true := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let C := ReferenceCollectionPhaseHistory.collectionWindow R w
  have hv : w + C.length < R.length := by rw [← hb]; exact b.isLt
  have hlater := (collection_window_boundary R w hv).2
  have hexecution :=
    ReferenceFirstReplacementCollectionExecution.complete_first_replacement_collection_execution
      rate source rewards C_star C_h
  change (match R[w + C.length]? with
    | none => True
    | some record => _) at hexecution
  rw [List.getElem?_eq_getElem hv] at hexecution
  dsimp only at hexecution
  have hprep : (R[w + C.length]).output.preparation.coordinator =
      (prepare (R[w + C.length]).input).coordinator := by
    rw [(R[w + C.length]).output_eq]; rfl
  rw [ReferenceCollectionPhaseHistory.laterChosen, ← hprep] at hlater
  cases hout : (R[w + C.length]).output.preparation.coordinator with
  | first outcome => cases outcome <;> simp only [hout, Bool.false_eq_true] at hlater
  | live registers owned base outcome => simp only [hout, Bool.false_eq_true] at hlater
  | invalidCollectionCutoff => simp only [hout, Bool.false_eq_true] at hlater
  | dagger => simp only [hout, Bool.false_eq_true] at hlater
  | collection old ledger clock cutoff outcome =>
      rw [hout] at hexecution
      cases outcome <;> simp only [hout, Bool.false_eq_true] at hlater
      obtain ⟨_, _, _, seg, init, _, _, _, _, _, _, hgood, _⟩ := hexecution
      exact hgood

section ChoiceSeed

variable (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)
    (hepoch : (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hcross count hspan).records =
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
    (c : Choice rate)
    (k b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hc : choice (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input = some c)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[b.val] c.payload)
    (hb : b.val =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)).length +
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)).length).length)

open ReferenceFirstCollectionAllArmNumericalStream

local notation "s" => ReferenceFirstCollectionReadyStream.startTime (rate := rate)
  source rewards C_star C_h
local notation "L" => ReferenceFirstLiveConfirmationHistory.firstLiveWindow
  (ReferenceActivePhysicalHorizon.Run.records
    (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
      source rewards C_star C_h hcross count hspan))
local notation "Cells" => ReferenceFirstWindowNumericalStream.actualLiveSourceCells
  rate source rewards C_star C_h hcross count hspan

include hepoch hc hbirth hb

/-- Conditional internal join. The final accepted-UP theorem below produces
all horizon witnesses and specializes this join only inside its first-birth
alternative. The complete actual S certificate remains in the output. -/
private theorem first_replacement_choice_seed :
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort,
    let out := d.stream
    ∃ (head : Choice rate) (initializer : Initializer p)
      (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
          head.payload head.started head.weights))
      (D : List (RecordedQueueRun.RoundInput p.K)),
      choice out.cutoff.cut.input = some head ∧ head.payload = out.payload ∧
      head.initializer = some initializer ∧
      initializer.checkedStart rate = .success head.preLedger ∧
      ∃ hDlen : D.length = out.ell,
      D[0]'(by rw [hDlen]; have h := out.positiveLength; omega) =
        ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head rewards valid ∧
      (∀ n : Fin out.ell,
        let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
        let cell := D[n.val]'(by rw [hDlen]; exact n.isLt)
        ∃ (call : Choice rate)
          (validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
            (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
              call.payload call.started call.weights)),
          choice record.input = some call ∧ call.payload = out.payload ∧
          CollectionBufferProvenance.collectionContext call.preLedger =
            CollectionBufferProvenance.collectionContext head.preLedger ∧
          cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate record call rewards validCall ∧
          record.input.rows = source.1.2 ∧
          record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
          record.input.rewards = rewards ∧ record.input.time.val = s + (L).length + n.val ∧
          cell.enabled = ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time ∧
          cell.reward = (fun a => ((rewards record.input.time a).val : ℝ) /
            (ConstructorDimensions.D p : ℝ)) ∧ cell.rate = out.payload.rate ∧
          (∀ a : Fin p.K,
            ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a record =
              (cell.enabled, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
          (0 < n.val → ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some cell)) ∧
      (∀ h, h ≤ out.ell → ∀ a : Fin p.K,
        (out.window.take h).map (ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a) =
          arrivals rate a (D.take h)) ∧
      out.ell = (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)).length).length ∧
      (∀ f : Fin (p.m - 1), c.preLedger.baseScore f =
        (QueueReplay.replay (4 * rate.n) (0, 0)
          (arrivals rate (c.payload.assignment.assigned f) (Cells ++ D))).1) ∧
      (∀ a : Fin p.K, c.payload.queues a =
        (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells ++ D))).2) ∧
      (∃ (x : RoundInput p rate)
        (dispatch : ReferenceFirstCollectionStreamEmptyDispatch.ActualNextDispatch
          x out.payload d.ledger out.saved),
        x = (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[b.val].input ∧
        let input := collectionInput x out.payload d.ledger
          (collectionClock out.payload d.ledger out.saved dispatch.cutoffTime) dispatch.cutoffTime
        let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger input dispatch.core.payload_n_eq
        ∃ consistent : LaterAssignmentStartOperation.LocalConsistency input.payload operationLedger,
        ∃ output : LaterAssignmentStartOperation.SuccessfulStart input.payload operationLedger
          dispatch.instruction input.row,
        ∃ hlocal : output.localConsistency = consistent,
        ∃ clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output,
        ∃ installed : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData,
        ∃ selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
          dispatch.started dispatch.instruction.time installed.registers.complementWeights input.row,
          CoordinatorRoundDispatch.dispatchCollection input =
            .laterChosen dispatch.core consistent dispatch.started dispatch.startCheck
              dispatch.instruction dispatch.assignmentStart output hlocal clockData installed selection ∧
          installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
          c.payload = installed.registers.payload ∧
          c.preLedger.baseScore = installed.retainedBaseScore ∧
          (∀ a, AssignmentScoreReconstruction.sourceScore output.reconstruction a =
            (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells ++ D))).1 ∧
            AssignmentScoreReconstruction.initialQueue output.reconstruction a =
              (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells ++ D))).2) ∧
          (∀ a, installed.registers.payload.queues a =
            (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells ++ D))).2) ∧
          (∀ f : Fin (p.m - 1),
            installed.retainedBaseScore f =
              (QueueReplay.replay (4 * rate.n) (0, 0)
                (arrivals rate (installed.registers.payload.assignment.assigned f) (Cells ++ D))).1 ∧
            (installed.registers.payload.downRecord f).val.q =
              (QueueReplay.replay (4 * rate.n) (0, 0)
                (arrivals rate (installed.registers.payload.assignment.assigned f) (Cells ++ D))).2)) := by
  classical
  obtain ⟨d, head, initializer, valid, D, hhead, hpay, hinit, hchecked,
    hDlen, hzero, hcells, hprefix, hledgers, hfinal, hnext⟩ :=
    ReferenceFirstCollectionNextStartNumericalSeed.actual_initialized_first_collection_classified_next_start_numerical_seed
      rate source rewards C_star C_h hcross count hspan hshort
  have hgood := complete_first_window_completed rewards C_star C_h source b hb
  have hv : (L).length +
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hcross count hspan).records (L).length).length <
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records.length := by
    simpa only [hepoch, ← hb] using b.isLt
  have hgood' : ∀ r ∈ ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records (L).length,
      (extractRound r).isSome = true := by simpa only [hepoch] using hgood
  obtain ⟨hell, hpending⟩ := stream_boundary_alignment
    source rewards C_star C_h count hcross hspan hshort d hv hgood'
  have hell' : d.stream.ell = (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)).length).length := by
    simpa only [hepoch] using hell
  refine ⟨d, head, initializer, valid, D, hhead, hpay, hinit, hchecked,
    hDlen, hzero, hcells, hprefix, hell', ?_⟩
  clear hhead hpay hinit hchecked hzero hcells hprefix hledgers hfinal
  obtain ⟨b', _hbk, hbirth', _harm, _hsigma, _hcutoff, hbase⟩ :=
    ReferenceAssignmentRetainedBirthProvenance.complete_collection_choice_birth_provenance
      rate rewards C_star C_h source k c hc
  have hb' := complete_birth_index_unique rewards C_star C_h source b b' c.payload hbirth hbirth'
  subst b'
  have hbaseProjected : ReferenceAssignmentCollectionMassSteps.installedBaseScore
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[b.val] = some c.preLedger.baseScore := by
    unfold ReferenceAssignmentCollectionMassSteps.installedBaseScore
    split at hbase <;> simp_all only
  clear hbase
  have hboundary : (L).length + d.stream.ell = b.val := by
    simpa only [hepoch, hell'] using hb.symm
  have hinput := stream_next_input source rewards C_star C_h count hcross hspan hshort
    d hepoch b hpending hboundary
  cases houtcome : d.outcome with
  | exhausted _ _ _ _ _ => simp only [houtcome] at hinput
  | empty e =>
      simp only [houtcome] at hnext hinput
      cases hnextBoundary : e.nextBoundary with
      | terminal _ _ => simp only [hnextBoundary] at hinput
      | next _ _ x _ _ _ _ _ _ _ hrun dispatch =>
          simp only [hnextBoundary] at hnext hinput
          have hx : x = (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h)[b.val].input := hinput
          have hrecord : (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h)[b.val] =
              (⟨x, step x, rfl⟩ : RoundRecord (p := p) (rate := rate)) :=
            record_eq_of_input (p := p) (rate := rate) _ x hx.symm
          obtain ⟨_htime, canonical, _hcanonical, _hcanonicalNum,
            consistent, reconstructed, _hrec, _hnum, hcases⟩ := hnext
          have hprepared := dispatch.preparedCoordinator
          rcases hcases with hfailure | hsuccess
          · obtain ⟨arm, reason, _hcorrected, hlater, hdispatch⟩ := hfailure
            rw [hdispatch] at hprepared
            have hbX := hbirth
            rw [hrecord] at hbX
            simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth,
              ReferenceActivePhysicalStep.step, hprepared] at hbX
          · obtain ⟨output, hlocal, clockData, installed, selection, hinstall,
              hreconstruction, hlater, hdispatch, hpayload, htime, hvector,
              hinstalledRec, hqueues, hbases, howned⟩ := hsuccess
            rw [hdispatch] at hprepared
            have hnewbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
                (ReferenceCompletePhysicalHistory.completeSuffixRecords
                  rate source rewards C_star C_h)[b.val] installed.registers.payload := by
              rw [hrecord]
              simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth,
                ReferenceActivePhysicalStep.step, hprepared]
              exact ⟨rfl, congrArg Fin.val htime⟩
            have hP := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
              _ _ _ hbirth hnewbirth
            rw [hrecord] at hbaseProjected
            simp only [ReferenceAssignmentCollectionMassSteps.installedBaseScore,
              ReferenceActivePhysicalStep.step, hprepared] at hbaseProjected
            have hbase : c.preLedger.baseScore = installed.retainedBaseScore :=
              (Option.some.inj hbaseProjected).symm
            refine ⟨?_, ?_, ?_⟩
            · intro f
              rw [hbase, (hbases f).2.1]
              rw [hP]
              rfl
            · intro a
              rw [hP]
              exact hqueues a
            · refine ⟨x, dispatch, hx, consistent, output, hlocal, clockData,
                installed, selection, hdispatch, hinstall, hP, hbase, ?_, hqueues, ?_⟩
              · intro a
                rw [hreconstruction]
                exact ⟨(_hnum a).1, (_hnum a).2.1⟩
              · intro f
                exact ⟨(hbases f).2.1, (hbases f).2.2⟩

end ChoiceSeed

open ReferenceFirstCollectionAllArmNumericalStream

/-- Internal numerical substitution with the actual source-produced birth
seed. The public theorem supplies every conditional input from its one N
elimination, keeping its exact live and collection lists. -/
private theorem first_replacement_finish_seed
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (c : Choice rate)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hc : choice (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input = some c)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[b.val] c.payload)
    (I : Initializer p) (hbase : I.base = c.preLedger.baseScore)
    (N n : ℕ) (A : List (Bool × ℕ)) (H : ℕ → List (Bool × ℕ))
    (finished : Ledger rate)
    (hcutnum : finished.cutoffRegisters (c.payload.assignment.assigned i) =
      some ⟨(QueueReplay.replay (4 * rate.n) (I.base i, (c.payload.downRecord i).val.q) (A.take (N))).1, (QueueReplay.replay (4 * rate.n) (I.base i, (c.payload.downRecord i).val.q) (A.take (N))).2,
        (QueueReplay.replay (4 * rate.n) (I.base i, (c.payload.downRecord i).val.q) (A.take (N))).1 - (QueueReplay.replay (4 * rate.n) (I.base i, (c.payload.downRecord i).val.q) (A.take (N - 1))).1⟩)
    (hcurrentnum : finished.currentRegisters (c.payload.assignment.assigned i) =
      some ⟨(QueueReplay.replay (4 * rate.n) (I.base i, (c.payload.downRecord i).val.q) (A ++ H (n + 1))).2, (QueueReplay.replay (4 * rate.n) (I.base i, (c.payload.downRecord i).val.q) (A ++ H (n + 1))).1 - (QueueReplay.replay (4 * rate.n) (I.base i, (c.payload.downRecord i).val.q) (A ++ H (n))).1⟩)
    (hincnum : finished.increment (c.payload.assignment.assigned i) = (QueueReplay.replay (4 * rate.n) (I.base i, (c.payload.downRecord i).val.q) (A ++ H (n + 1))).1 - (QueueReplay.replay (4 * rate.n) (I.base i, (c.payload.downRecord i).val.q) (A.take (N))).1)
    (hfinishnum : ((QueueReplay.replay (4 * rate.n) (I.base i, (c.payload.downRecord i).val.q) (A.take (N))).1 + finished.increment (c.payload.assignment.assigned i), (QueueReplay.replay (4 * rate.n) (I.base i, (c.payload.downRecord i).val.q) (A ++ H (n + 1))).2) =
      (QueueReplay.replay (4 * rate.n) (I.base i, (c.payload.downRecord i).val.q) (A ++ H (n + 1)))) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let P := c.payload
    let M := P.downRecord i
    let a := P.assignment.assigned i
    let cap := 4 * rate.n
    let X := fun m => QueueReplay.replay cap (I.base i, M.val.q) (A.take m)
    let Y := fun m => QueueReplay.replay cap (I.base i, M.val.q) (A ++ H m)
    (b.val =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length +
        (ReferenceCollectionPhaseHistory.collectionWindow R
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length →
      ∃ hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput
          source rewards C_star C_h rate)).crossing.isSome = true,
      ∃ hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
        source rewards C_star C_h + (p.T - s) ≤ p.T,
      ∃ hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hcross (p.T - s) hspan).records).length < p.T - s,
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross (p.T - s) hspan).records = R ∧
      let s0 := ReferenceFirstCollectionReadyStream.startTime (rate := rate)
        source rewards C_star C_h
      let L0 := ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hcross (p.T - s) hspan).records
      let Cells0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate source rewards C_star C_h hcross (p.T - s) hspan
      ∃ seedDispatch : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (p := p) (rate := rate) source rewards C_star C_h (p.T - s) hcross hspan hshort,
      let out := seedDispatch.stream
      ∃ (head0 : Choice rate) (initializer0 : Initializer p)
        (valid0 : CoordinatorRecorderComplementBridge.LocalInputsValid
          (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
            head0.payload head0.started head0.weights))
        (D0 : List (RecordedQueueRun.RoundInput p.K)),
        choice out.cutoff.cut.input = some head0 ∧ head0.payload = out.payload ∧
        head0.initializer = some initializer0 ∧
        initializer0.checkedStart rate = .success head0.preLedger ∧
        ∃ hDlen : D0.length = out.ell,
        D0[0]'(by rw [hDlen]; have h := out.positiveLength; omega) =
          ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head0 rewards valid0 ∧
        (∀ n : Fin out.ell,
          let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
          let cell := D0[n.val]'(by rw [hDlen]; exact n.isLt)
          ∃ (call : Choice rate)
            (validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
              (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
                call.payload call.started call.weights)),
            choice record.input = some call ∧ call.payload = out.payload ∧
            CollectionBufferProvenance.collectionContext call.preLedger =
              CollectionBufferProvenance.collectionContext head0.preLedger ∧
            cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate record call rewards validCall ∧
            record.input.rows = source.1.2 ∧
            record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
            record.input.rewards = rewards ∧ record.input.time.val = s0 + (L0).length + n.val ∧
            cell.enabled = ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time ∧
            cell.reward = (fun a => ((rewards record.input.time a).val : ℝ) /
              (ConstructorDimensions.D p : ℝ)) ∧ cell.rate = out.payload.rate ∧
            (∀ a : Fin p.K,
              ReferenceCollectionRawBufferHistory.physicalQueueRecord head0.preLedger a record =
                (cell.enabled, RecordedQueueRun.quantizedArrival
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
            (0 < n.val → ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s0 record = some cell)) ∧
        (∀ h, h ≤ out.ell → ∀ a : Fin p.K,
          (out.window.take h).map (ReferenceCollectionRawBufferHistory.physicalQueueRecord head0.preLedger a) =
            arrivals rate a (D0.take h)) ∧
        out.ell = (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)).length).length ∧
        (∀ f : Fin (p.m - 1), c.preLedger.baseScore f =
          (QueueReplay.replay (4 * rate.n) (0, 0)
            (arrivals rate (c.payload.assignment.assigned f) (Cells0 ++ D0))).1) ∧
        (∀ a : Fin p.K, c.payload.queues a =
          (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells0 ++ D0))).2) ∧
        (∃ (x : RoundInput p rate)
          (dispatch : ReferenceFirstCollectionStreamEmptyDispatch.ActualNextDispatch
            x out.payload seedDispatch.ledger out.saved),
          x = (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[b.val].input ∧
          let input := collectionInput x out.payload seedDispatch.ledger
            (collectionClock out.payload seedDispatch.ledger out.saved dispatch.cutoffTime) dispatch.cutoffTime
          let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger input dispatch.core.payload_n_eq
          ∃ consistent : LaterAssignmentStartOperation.LocalConsistency input.payload operationLedger,
          ∃ output : LaterAssignmentStartOperation.SuccessfulStart input.payload operationLedger
            dispatch.instruction input.row,
          ∃ hlocal : output.localConsistency = consistent,
          ∃ clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output,
          ∃ installed : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData,
          ∃ selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
            dispatch.started dispatch.instruction.time installed.registers.complementWeights input.row,
            CoordinatorRoundDispatch.dispatchCollection input =
              .laterChosen dispatch.core consistent dispatch.started dispatch.startCheck
                dispatch.instruction dispatch.assignmentStart output hlocal clockData installed selection ∧
            installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
            c.payload = installed.registers.payload ∧
            c.preLedger.baseScore = installed.retainedBaseScore ∧
            (∀ a, AssignmentScoreReconstruction.sourceScore output.reconstruction a =
              (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells0 ++ D0))).1 ∧
              AssignmentScoreReconstruction.initialQueue output.reconstruction a =
                (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells0 ++ D0))).2) ∧
            (∀ a, installed.registers.payload.queues a =
              (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells0 ++ D0))).2) ∧
            (∀ f : Fin (p.m - 1),
              installed.retainedBaseScore f =
                (QueueReplay.replay (4 * rate.n) (0, 0)
                  (arrivals rate (installed.registers.payload.assignment.assigned f) (Cells0 ++ D0))).1 ∧
              (installed.registers.payload.downRecord f).val.q =
                (QueueReplay.replay (4 * rate.n) (0, 0)
                  (arrivals rate (installed.registers.payload.assignment.assigned f) (Cells0 ++ D0))).2)) ∧
        let Q_a := QueueReplay.replay cap (0, 0) (arrivals rate a (Cells0 ++ D0))
        let X0 := fun m => QueueReplay.replay cap (0, 0)
          (arrivals rate a (Cells0 ++ D0) ++ A.take m)
        let Y0 := fun m => QueueReplay.replay cap (0, 0)
          (arrivals rate a (Cells0 ++ D0) ++ (A ++ H m))
        (I.base i, M.val.q) = Q_a ∧
        (∀ m, X m = X0 m) ∧ (∀ m, Y m = Y0 m) ∧
        finished.cutoffRegisters a =
          some ⟨(X0 N).1, (X0 N).2, (X0 N).1 - (X0 (N - 1)).1⟩ ∧
        finished.currentRegisters a =
          some ⟨(Y0 (n + 1)).2, (Y0 (n + 1)).1 - (Y0 n).1⟩ ∧
        finished.increment a = (Y0 (n + 1)).1 - (X0 N).1 ∧
        ((X0 N).1 + finished.increment a, (Y0 (n + 1)).2) = Y0 (n + 1)) := by
  classical
  intro R s P M a cap X Y
  have hq : M.val.q = P.queues a := P.downRecord_initialQueue i
  change finished.cutoffRegisters a =
    some ⟨(X N).1, (X N).2, (X N).1 - (X (N - 1)).1⟩ at hcutnum
  change finished.currentRegisters a =
    some ⟨(Y (n + 1)).2, (Y (n + 1)).1 - (Y n).1⟩ at hcurrentnum
  change finished.increment a = (Y (n + 1)).1 - (X N).1 at hincnum
  change ((X N).1 + finished.increment a, (Y (n + 1)).2) = Y (n + 1) at hfinishnum
  intro hb
  have hcross := complete_crossing rewards C_star C_h source k
  have hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + (p.T - s) ≤ p.T := by
    change s + (p.T - s) ≤ p.T
    exact Nat.add_sub_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T
      rate source rewards C_star C_h) |>.le
  have hepoch := complete_epoch_eq rewards C_star C_h source hcross hspan
  have hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross (p.T - s) hspan).records).length < p.T - s := by
    have hv : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length +
        (ReferenceCollectionPhaseHistory.collectionWindow R
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length < R.length := by
      rw [← hb]
      exact b.isLt
    have hw := (collection_window_boundary R _ hv).1
    rw [hepoch]
    have hlen : R.length = p.T - s :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate source rewards C_star C_h
    exact Nat.lt_of_lt_of_eq hw hlen
  obtain ⟨seedDispatch, head0, initializer0, valid0, D0, hhead0, hpay0, hinit0, hchecked0,
    hDlen0, hzero0, hcells0, hprefix0, hell0, hseedBase, hseedQueue, hactual0⟩ :=
    first_replacement_choice_seed source rewards C_star C_h (p.T - s)
      hcross hspan hshort hepoch c k b hc hbirth hb
  refine ⟨hcross, hspan, hshort, hepoch,
    seedDispatch, head0, initializer0, valid0, D0, hhead0, hpay0, hinit0, hchecked0,
    hDlen0, hzero0, hcells0, hprefix0, hell0, hseedBase, hseedQueue, hactual0, ?_⟩
  let Cells0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hcross (p.T - s) hspan
  let Q_a := QueueReplay.replay cap (0, 0) (arrivals rate a (Cells0 ++ D0))
  let X0 := fun m => QueueReplay.replay cap (0, 0)
    (arrivals rate a (Cells0 ++ D0) ++ A.take m)
  let Y0 := fun m => QueueReplay.replay cap (0, 0)
    (arrivals rate a (Cells0 ++ D0) ++ (A ++ H m))
  have hseed : (I.base i, M.val.q) = Q_a := by
    apply Prod.ext
    · change I.base i = _
      rw [hbase]
      exact hseedBase i
    · change M.val.q = _
      rw [hq]
      exact hseedQueue a
  have hX0 (m : ℕ) : X m = X0 m := by
    dsimp only [X, X0]
    rw [QueueReplay.replay_append]
    exact congrArg (fun initial => QueueReplay.replay cap initial (A.take m)) hseed
  have hY0 (m : ℕ) : Y m = Y0 m := by
    dsimp only [Y, Y0]
    rw [QueueReplay.replay_append cap (0, 0)
      (arrivals rate a (Cells0 ++ D0)) (A ++ H m)]
    exact congrArg (fun initial => QueueReplay.replay cap initial (A ++ H m)) hseed
  refine ⟨hseed, hX0, hY0, ?_, ?_, ?_, ?_⟩
  · change finished.cutoffRegisters a =
      some ⟨(X0 N).1, (X0 N).2, (X0 N).1 - (X0 (N - 1)).1⟩
    simpa only [hX0] using hcutnum
  · change finished.currentRegisters a =
      some ⟨(Y0 (n + 1)).2, (Y0 (n + 1)).1 - (Y0 n).1⟩
    simpa only [hY0] using hcurrentnum
  · change finished.increment a = (Y0 (n + 1)).1 - (X0 N).1
    simpa only [hX0, hY0] using hincnum
  · change ((X0 N).1 + finished.increment a, (Y0 (n + 1)).2) = Y0 (n + 1)
    simpa only [hX0, hY0] using hfinishnum


/-- Retain one actual accepted-UP telescope and, on its first replacement
birth, join the initialized old LIVE/collection prefix to that same payload,
initializer, DOWN word and inclusive accepted FINISH replay. Other births
remain explicit. This is an internal deterministic result, not regret closure. -/
theorem complete_accepted_up_first_replacement_numerical_seed
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    ∃ (c : ReferenceCollectionSegmentExtraction.Choice rate)
      (b j : Fin R.length)
      (logged after : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
      (scan : FollowerCutoffScan.ScanResult p.T)
      (registers : ℕ × ℕ) (lastService : ℕ),
      ReferenceCollectionSegmentExtraction.choice (R[k.val]'k.isLt).input = some c ∧
      b.val ≤ j.val ∧ j.val < k.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth (R[b.val]'b.isLt) c.payload ∧
      ReferenceAcceptedUpFollowerHistory.RetainedDown R[j.val] i (c.payload.downRecord i) ∧
      (R[j.val].output.followers i).downInput = some logged ∧
      (R[j.val].output.followers i).down = some cut ∧
      cut.outcome = .accepted logged after raw (c.payload.downRecord i) scan registers lastService ∧
      let P := c.payload
      let M := P.downRecord i
      let a := P.assignment.assigned i
      let sigma := P.sigma.val + 1
      let cap := 4 * rate.n
      let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
      let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
      let ell := min u (R[j.val].input.time.val + 2)
      let N := u - sigma
      let d := ell - sigma
      let z := max (b.val + N) (j.val + 1)
      let L := (R.drop b.val).take N
      let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
      ell = scan.endpoint ∧
      ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell =
        .ok ⟨registers, lastService⟩ ∧
      M.val.q = P.queues a ∧ 0 < d ∧ d ≤ N ∧
      L.map (fun (r : RoundRecord (p := p) (rate := rate)) => r.input.time.val + 1) = List.range' sigma N ∧
      ∃ (hLlen : L.length = N)
        (v : ∀ n : Fin N, Selection
          (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input)
        (ho : ∀ n : Fin N, ReferenceLaterLiveNumericalReadout.preparedOrdinary
          (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm))),
        (∀ n, (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).output.preparation.coordinator.selection =
            some (v n) ∧ (v n).view.payload = P ∧ (v n).view.cutoff = none ∧
            CoordinatorLocalArmChoice.assignmentIsLive (v n).view.payload
              (v n).view.cutoff (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)).input.time) ∧
        (∀ n f, (ReferenceFollowerFixedReply.actualChoice
            (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) f).configuration =
          .ordinary
            (ReferenceLaterLiveNumericalReadout.preparedStates
              (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n) f)
            (ReferenceLaterLiveNumericalReadout.preparedMemories
              (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n) f)) ∧
        let Cells : Fin N → RecordedQueueRun.RoundInput p.K := fun n =>
          ReferenceFirstWindowNumericalStream.sourceCell
            (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (v n).view.payload
            (v n).view.pendingAtChoice
            (ReferenceLaterLiveNumericalReadout.preparedStates
              (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n))
            (v n).view.complementWeights (v n).view.cutoff
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v n))
        let A := List.ofFn (fun n : Fin N =>
          ((Cells n).enabled, RecordedQueueRun.quantizedArrival qp (Cells n) a))
        let V := fun count => QueueReplay.replay cap (0, M.val.q) (A.take count)
        let Ed := ((R.drop b.val).take d).map
          (fun r => (true, ReferenceFollowerSparseEmissionRecovery.emissionContribution M i r))
        let Q := ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell
        Q = Ed ∧ Ed = A.take d ∧ A.length = N ∧
        (∀ x ∈ A, x.1 = true) ∧ registers = V d ∧
        lastService = (V d).1 - (V (d - 1)).1 ∧
        let W := fun count => QueueReplay.replay cap registers ((A.drop d).take (count - d))
        ∃ hz : z < R.length, z ≤ k.val ∧
          ∃ (terminal : ReferencePrelaunchFollower.State p rate.eta)
            (terminalMemory : ActiveFollowerLifecycle.LocalMemory p),
            (ReferenceFollowerFixedReply.actualChoice (R[z]'hz) i).configuration =
              .ordinary terminal terminalMemory ∧
            terminal.status = .unoccupied ∧ terminal.lastDown = some M ∧
            (terminal.S, terminal.backlog) = W N ∧
            terminal.delta = (if d < N then (W N).1 - (W (N - 1)).1 else lastService) ∧
            U.val.sigma = sigma ∧ U.val.S = terminal.S ∧
            U.val.delta = terminal.delta ∧ U.val.q = terminal.backlog ∧
            (U.val.S, U.val.q) = QueueReplay.replay cap (0, M.val.q) A ∧
            U.val.delta =
              (QueueReplay.replay cap (0, M.val.q) A).1 -
                (QueueReplay.replay cap (0, M.val.q) (A.take (N - 1))).1 ∧
            let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
            let o := u - (s + 1)
            let n := k.val - o
              ∃ (seg : Segment rate) (done : CompletedRound rate)
                (c0 : Choice rate) (I : Initializer p),
                o ≤ k.val ∧ o < R.length ∧ n < seg.records.length ∧
                segmentAt R o = some seg ∧
                (∀ ho : o < R.length, seg.entry = R[o]'ho) ∧ seg.context = c0 ∧
                choice seg.entry.input = some c0 ∧ c0.payload = c.payload ∧
                c0.initializer = some I ∧ I.checkedStart rate = .success seg.context.preLedger ∧
                I.sigma = sigma ∧ I.cutoff = u ∧ seg.entry.input.time.val + 1 = u ∧
                (∃ (liveInit : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                  (ownedInit : CoordinatorLiveServiceFinish.OwnedRegisters liveInit)
                  (baseInit : Fin (p.m - 1) → ℕ),
                  seg.entry.input.state.coordinator = .live liveInit ownedInit baseInit ∧
                  I = cutoffInitializer (liveRegistersAt liveInit seg.entry.input.time)
                    (liveOwnedAt liveInit ownedInit seg.entry.input.time) baseInit seg.entry.input.time ∧
                  (prepare seg.entry.input).coordinator = .live liveInit ownedInit baseInit
                    (CoordinatorRoundDispatch.dispatchLive (liveInput seg.entry.input liveInit ownedInit baseInit)) ∧
                  ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true) ∧
                (∀ hn : n < seg.records.length, seg.records[n]'hn = (R[k.val]'k.isLt)) ∧ extractRound (R[k.val]'k.isLt) = some done ∧
                done.context = c ∧ done.accepted = true ∧ done.input.parsed = some U ∧
                done.input.selectedFollower = i ∧
                seg.records.take (n + 1) = (R.drop o).take (n + 1) ∧
                (seg.records.take (n + 1)).map (fun (r : RoundRecord (p := p) (rate := rate)) => r.input.time.val + 1) =
                  List.range' u (n + 1) ∧
                seg.records ++ seg.remaining = R.drop o ∧ seg.exit = exitOf seg.remaining ∧
                o = b.val + N ∧ I.assignment.arm = P.assignment.assigned ∧
                I.freezeAt = c.preLedger.freezeAt ∧ I.base = c.preLedger.baseScore ∧
                ∃ (initial : ReferenceActivePhysicalStep.State p rate) (span : s + (p.T - s) ≤ p.T)
                  (active : allActiveAtStart initial s),
                  ReferenceCorrectedInitializationLaunch.correctedLaunch
                    rate source rewards C_star C_h = some initial ∧
                  initial.coordinator = .first ∧
                  R = (run initial source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source)
                    rewards s (p.T - s) span active).records ∧
                  CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                  (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                  I.assignment I.sigma I.cutoff I.freezeAt
                  I.base I.outside seg.inputs =
                    .success ⟨seg.context.preLedger, seg.accepted, seg.final⟩ ∧
                ∃ prefixExecution : CollectionCheckedExecution.Execution p rate.eta.val
                    rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
                    rate.n rate.n_scale,
                    CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                      I.assignment I.sigma I.cutoff I.freezeAt
                      I.base I.outside (seg.inputs.take n) =
                        .success prefixExecution ∧
                    prefixExecution.initial = seg.context.preLedger ∧
                    prefixExecution.final = ReferenceCollectionSegmentExtraction.endpointLedger
                      seg.context.preLedger (seg.records.take n) ∧
                    ∃ recording started decoded bank finished,
                      ((R[k.val]'k.isLt)).output.coordinator.recording = some recording ∧
                      CoordinatorRecorderComplementBridge.run
                        (ReferenceActivePhysicalStep.collectionRecordingInput
                          (ReferenceActivePhysicalStep.prepare ((R[k.val]'k.isLt)).input) done.context.payload
                          done.context.started done.context.weights) = some recording ∧
                      CoordinatorCollectionLedger.startRound done.context.preLedger
                        (((R[k.val]'k.isLt)).input.time.val + 1)
                        (ReferenceActivePhysicalStep.collectionEnabled done.context.preLedger
                          ((R[k.val]'k.isLt)).input.time)
                        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                          .success started ∧
                      (ReferenceActivePhysicalStep.receiveUp
                        (ReferenceActivePhysicalStep.prepare ((R[k.val]'k.isLt)).input) started).result =
                          .success (decoded, bank) ∧
                      CoordinatorCollectionLedger.decodeUp started i (some U) = .success decoded ∧
                      CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
                      finished = done.final ∧
                      done.input = ReferenceCollectionSegmentExtraction.inputOf ((R[k.val]'k.isLt)).input
                        done.context.preLedger recording started ∧
                      let arm := started.assignment.arm i
                      ∃ hbound : started.cutoff - 1 + (started.cursor - started.cutoff) ≤ p.T,
                        ∃ lastIndex : Fin p.T,
                          CoordinatorCollectionLedger.sourceRound lastIndex = started.cursor ∧
                          lastIndex = ((R[k.val]'k.isLt)).input.time ∧
                          started.cursor - started.cutoff = n ∧
                          started.assignment = I.assignment ∧
                          started.sigma = I.sigma ∧
                          started.cutoff = I.cutoff ∧
                          started.freezeAt = I.freezeAt ∧
                          started.baseScore = I.base ∧
                          1 ≤ started.cutoff ∧ started.cutoff ≤ started.cursor ∧
                          started.cursor ≤ p.T ∧
                          prefixExecution.final.currentRegisters arm = none ∧
                          started.currentRegisters arm = none ∧
                          ∃ past current,
                          CoordinatorCollectionLedger.replayRecords? started arm
                              (CoordinatorCollectionLedger.calendarIndices p.T
                                (started.cutoff - 1) (started.cursor - started.cutoff) hbound) =
                            some past ∧
                          CoordinatorCollectionLedger.replayRecords? started arm [lastIndex] =
                            some [current] ∧
                          CollectionBufferProvenance.suppliedReplayRecords?
                              (seg.inputs.take n ++ [done.input]) arm started.freezeAt
                              (CoordinatorCollectionLedger.calendarIndices p.T
                                (started.cutoff - 1) (started.cursor - started.cutoff) hbound ++
                                [lastIndex]) =
                            some (past ++ [current]) ∧
                          past = (seg.records.take n).map
                            (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              seg.context.preLedger arm) ∧
                          current = ReferenceCollectionRawBufferHistory.physicalQueueRecord
                            seg.context.preLedger arm ((R[k.val]'k.isLt)) ∧
                          past ++ [current] = (seg.records.take (n + 1)).map
                            (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              seg.context.preLedger arm) ∧
                          (seg.records.take n).map
                              (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                seg.context.preLedger arm) ++
                            [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              seg.context.preLedger arm ((R[k.val]'k.isLt))] =
                            (seg.records.take (n + 1)).map
                              (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                seg.context.preLedger arm) ∧
                          finished.currentRegisters arm =
                            some ⟨(QueueReplay.replay (4 * rate.n) (0, U.val.q)
                              ((seg.records.take n).map
                                (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                  seg.context.preLedger arm) ++
                                [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                  seg.context.preLedger arm ((R[k.val]'k.isLt))])).2,
                              (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                                ((seg.records.take n).map
                                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                    seg.context.preLedger arm) ++
                                  [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                    seg.context.preLedger arm ((R[k.val]'k.isLt))])).1 -
                              (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                                ((seg.records.take n).map
                                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                    seg.context.preLedger arm))).1⟩ ∧
                          finished.increment arm =
                            (QueueReplay.replay (4 * rate.n) (0, U.val.q)
                              ((seg.records.take n).map
                                (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                  seg.context.preLedger arm) ++
                                [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                                  seg.context.preLedger arm ((R[k.val]'k.isLt))])).1 ∧
                          finished.cutoffRegisters arm =
                            some ⟨started.baseScore i + U.val.S, U.val.q, U.val.delta⟩ ∧
                          started.cutoff = u ∧
                          (∃ saved, ((R[k.val]'k.isLt)).output.next.coordinator = .collection P finished saved) ∧
                          let B0 := I.base i
                          let X := fun v => QueueReplay.replay cap (B0, M.val.q) (A.take v)
                          let H := fun m => (seg.records.take m).map
                            (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a)
                          let Y := fun m => QueueReplay.replay cap (B0, M.val.q) (A ++ H m)
                          H (n + 1) = H n ++
                            [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              seg.context.preLedger a ((R[k.val]'k.isLt))] ∧
                          finished.cutoffRegisters a =
                            some ⟨(X N).1, (X N).2, (X N).1 - (X (N - 1)).1⟩ ∧
                          finished.currentRegisters a =
                            some ⟨(Y (n + 1)).2, (Y (n + 1)).1 - (Y n).1⟩ ∧
                          finished.increment a = (QueueReplay.replay cap (0, U.val.q) (H (n + 1))).1 ∧
                          finished.increment a = (Y (n + 1)).1 - (X N).1 ∧
                          ((X N).1 + finished.increment a, (Y (n + 1)).2) = Y (n + 1) ∧
                          (b.val =
                            (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length +
                              (ReferenceCollectionPhaseHistory.collectionWindow R
                                (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length →
                            ∃ hcross : (ReferenceInitializationRun.output
                              (ActualReferenceInitializationBlock.referenceInput
                                source rewards C_star C_h rate)).crossing.isSome = true,
                            ∃ hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                              source rewards C_star C_h + (p.T - s) ≤ p.T,
                            ∃ hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                              (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                                source rewards C_star C_h hcross (p.T - s) hspan).records).length < p.T - s,
                            (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                              source rewards C_star C_h hcross (p.T - s) hspan).records = R ∧
                            let s0 := ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                              source rewards C_star C_h
                            let L0 := ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                              (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
                                source rewards C_star C_h hcross (p.T - s) hspan).records
                            let Cells0 := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
                              rate source rewards C_star C_h hcross (p.T - s) hspan
                            ∃ seedDispatch : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
                              (p := p) (rate := rate) source rewards C_star C_h (p.T - s) hcross hspan hshort,
                            let out := seedDispatch.stream
                            ∃ (head0 : Choice rate) (initializer0 : Initializer p)
                              (valid0 : CoordinatorRecorderComplementBridge.LocalInputsValid
                                (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
                                  head0.payload head0.started head0.weights))
                              (D0 : List (RecordedQueueRun.RoundInput p.K)),
                              choice out.cutoff.cut.input = some head0 ∧ head0.payload = out.payload ∧
                              head0.initializer = some initializer0 ∧
                              initializer0.checkedStart rate = .success head0.preLedger ∧
                              ∃ hDlen : D0.length = out.ell,
                              D0[0]'(by rw [hDlen]; have h := out.positiveLength; omega) =
                                ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate out.cutoff.cut head0 rewards valid0 ∧
                              (∀ n : Fin out.ell,
                                let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
                                let cell := D0[n.val]'(by rw [hDlen]; exact n.isLt)
                                ∃ (call : Choice rate)
                                  (validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
                                    (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
                                      call.payload call.started call.weights)),
                                  choice record.input = some call ∧ call.payload = out.payload ∧
                                  CollectionBufferProvenance.collectionContext call.preLedger =
                                    CollectionBufferProvenance.collectionContext head0.preLedger ∧
                                  cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate record call rewards validCall ∧
                                  record.input.rows = source.1.2 ∧
                                  record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                                  record.input.rewards = rewards ∧ record.input.time.val = s0 + (L0).length + n.val ∧
                                  cell.enabled = ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time ∧
                                  cell.reward = (fun a => ((rewards record.input.time a).val : ℝ) /
                                    (ConstructorDimensions.D p : ℝ)) ∧ cell.rate = out.payload.rate ∧
                                  (∀ a : Fin p.K,
                                    ReferenceCollectionRawBufferHistory.physicalQueueRecord head0.preLedger a record =
                                      (cell.enabled, RecordedQueueRun.quantizedArrival
                                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
                                  (0 < n.val → ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s0 record = some cell)) ∧
                              (∀ h, h ≤ out.ell → ∀ a : Fin p.K,
                                (out.window.take h).map (ReferenceCollectionRawBufferHistory.physicalQueueRecord head0.preLedger a) =
                                  arrivals rate a (D0.take h)) ∧
                              out.ell = (ReferenceCollectionPhaseHistory.collectionWindow
                                (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)
                                (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                                  (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h)).length).length ∧
                              (∀ f : Fin (p.m - 1), c.preLedger.baseScore f =
                                (QueueReplay.replay (4 * rate.n) (0, 0)
                                  (arrivals rate (c.payload.assignment.assigned f) (Cells0 ++ D0))).1) ∧
                              (∀ a : Fin p.K, c.payload.queues a =
                                (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells0 ++ D0))).2) ∧
                              (∃ (x : RoundInput p rate)
                                (dispatch : ReferenceFirstCollectionStreamEmptyDispatch.ActualNextDispatch
                                  x out.payload seedDispatch.ledger out.saved),
                                x = (ReferenceCompletePhysicalHistory.completeSuffixRecords
                                  rate source rewards C_star C_h)[b.val].input ∧
                                let input := collectionInput x out.payload seedDispatch.ledger
                                  (collectionClock out.payload seedDispatch.ledger out.saved dispatch.cutoffTime) dispatch.cutoffTime
                                let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger input dispatch.core.payload_n_eq
                                ∃ consistent : LaterAssignmentStartOperation.LocalConsistency input.payload operationLedger,
                                ∃ output : LaterAssignmentStartOperation.SuccessfulStart input.payload operationLedger
                                  dispatch.instruction input.row,
                                ∃ hlocal : output.localConsistency = consistent,
                                ∃ clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output,
                                ∃ installed : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData,
                                ∃ selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
                                  dispatch.started dispatch.instruction.time installed.registers.complementWeights input.row,
                                  CoordinatorRoundDispatch.dispatchCollection input =
                                    .laterChosen dispatch.core consistent dispatch.started dispatch.startCheck
                                      dispatch.instruction dispatch.assignmentStart output hlocal clockData installed selection ∧
                                  installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
                                  c.payload = installed.registers.payload ∧
                                  c.preLedger.baseScore = installed.retainedBaseScore ∧
                                  (∀ a, AssignmentScoreReconstruction.sourceScore output.reconstruction a =
                                    (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells0 ++ D0))).1 ∧
                                    AssignmentScoreReconstruction.initialQueue output.reconstruction a =
                                      (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells0 ++ D0))).2) ∧
                                  (∀ a, installed.registers.payload.queues a =
                                    (QueueReplay.replay (4 * rate.n) (0, 0) (arrivals rate a (Cells0 ++ D0))).2) ∧
                                  (∀ f : Fin (p.m - 1),
                                    installed.retainedBaseScore f =
                                      (QueueReplay.replay (4 * rate.n) (0, 0)
                                        (arrivals rate (installed.registers.payload.assignment.assigned f) (Cells0 ++ D0))).1 ∧
                                    (installed.registers.payload.downRecord f).val.q =
                                      (QueueReplay.replay (4 * rate.n) (0, 0)
                                        (arrivals rate (installed.registers.payload.assignment.assigned f) (Cells0 ++ D0))).2)) ∧
                              let Q_a := QueueReplay.replay cap (0, 0) (arrivals rate a (Cells0 ++ D0))
                              let X0 := fun m => QueueReplay.replay cap (0, 0)
                                (arrivals rate a (Cells0 ++ D0) ++ A.take m)
                              let Y0 := fun m => QueueReplay.replay cap (0, 0)
                                (arrivals rate a (Cells0 ++ D0) ++ (A ++ H m))
                              (I.base i, M.val.q) = Q_a ∧
                              (∀ m, X m = X0 m) ∧ (∀ m, Y m = Y0 m) ∧
                              finished.cutoffRegisters a =
                                some ⟨(X0 N).1, (X0 N).2, (X0 N).1 - (X0 (N - 1)).1⟩ ∧
                              finished.currentRegisters a =
                                some ⟨(Y0 (n + 1)).2, (Y0 (n + 1)).1 - (Y0 n).1⟩ ∧
                              finished.increment a = (Y0 (n + 1)).1 - (X0 N).1 ∧
                              ((X0 N).1 + finished.increment a, (Y0 (n + 1)).2) = Y0 (n + 1)) := by
  classical
  intro R
  obtain ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    hscan, hchecked, hq, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    hz, hzk, terminal, terminalMemory, hterminalChoice, hterminalStatus,
    hterminalDown, hterminalRegisters, hterminalDelta, hUsigma,
    hUSterminal, hUdterminal, hUqterminal, hUNumerical, hUDNumerical, hledger⟩ :=
    ReferenceCompleteAcceptedUpLedgerNumericalReplay.complete_accepted_up_collection_ledger_numerical_replay
      (rate := rate) rewards C_star C_h source k i U hacc
  let P := c.payload
  let M := P.downRecord i
  let a := P.assignment.assigned i
  let sigma := P.sigma.val + 1
  let cap := 4 * rate.n
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma bits
  let ell := min u (R[j.val].input.time.val + 2)
  let N := u - sigma
  let d := ell - sigma
  let L := (R.drop b.val).take N
  let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let Cells : Fin N → RecordedQueueRun.RoundInput p.K := fun n =>
    ReferenceFirstWindowNumericalStream.sourceCell
      (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (v n).view.payload
      (v n).view.pendingAtChoice
      (ReferenceLaterLiveNumericalReadout.preparedStates
        (L[n.val]'(Nat.lt_of_lt_of_eq n.isLt hLlen.symm)) (ho n))
      (v n).view.complementWeights (v n).view.cutoff
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid (v n))
  let A := List.ofFn (fun n : Fin N =>
    ((Cells n).enabled, RecordedQueueRun.quantizedArrival qp (Cells n) a))
  let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  let o := u - (s + 1)
  let n := k.val - o
  obtain ⟨seg, done, c0, I, hok, hoR, hn, hsegment, hentry, hsegContext,
    hc0, hP0, hI, hIchecked, hIsigma, hIcutoff, hentryTime, hlive,
    hrecord, hdone, hcontext, haccepted, hparsed, hsender, hprefix,
    hlabels, hpartition, hexit, hoffset, hIarm, hfreeze, hbase,
    initial, span, active, hlaunch, hfirst, hrun, hwhole,
    prefixExecution, hprefixRun, hprefixInitial, hprefixFinal,
    recording, started, decoded, bank, finished, hrecording, hrecorder,
    hstart, hreceive, hdecode, hfinish, hfinished, hinput,
    hbound, lastIndex, hlastRound, hlastIndex, hcursor, hassignment, hstartedSigma,
    hstartedCutoff, hstartedFreeze, hstartedBase, hcutpos, hcutcursor, hcursorT,
    hprefixUnknown, hstartedUnknown, past, current, hpast, hcurrent, hsupplied,
    hpastPhysical, hcurrentPhysical, hpastCurrent, hphysicalAppend,
    hcurrentRegisters, hincrement, hcutoffRegisters, hcutoffTime, hnext,
    hH, hcutnum, hcurrentnum, hincreplay, hincnum, hfinishnum⟩ := hledger
  let H := fun m => (seg.records.take m).map
    (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a)
  refine ⟨c, b, j, logged, after, cut, raw, scan, registers, lastService,
    hc, hbj, hjk, hbirth, hretained, hlogged, hdown, houtcome,
    hscan, hchecked, hq, hdpos, hdle, htimes, hLlen, v, ho,
    hselected, hprepared, hQ, hEd, hAlen, hAenabled, hregisters, hlastService,
    hz, hzk, terminal, terminalMemory, hterminalChoice, hterminalStatus,
    hterminalDown, hterminalRegisters, hterminalDelta, hUsigma,
    hUSterminal, hUdterminal, hUqterminal, hUNumerical, hUDNumerical,
    seg, done, c0, I, hok, hoR, hn, hsegment, hentry, hsegContext,
    hc0, hP0, hI, hIchecked, hIsigma, hIcutoff, hentryTime, hlive,
    hrecord, hdone, hcontext, haccepted, hparsed, hsender, hprefix,
    hlabels, hpartition, hexit, hoffset, hIarm, hfreeze, hbase,
    initial, span, active, hlaunch, hfirst, hrun, hwhole,
    prefixExecution, hprefixRun, hprefixInitial, hprefixFinal,
    recording, started, decoded, bank, finished, hrecording, hrecorder,
    hstart, hreceive, hdecode, hfinish, hfinished, hinput,
    hbound, lastIndex, hlastRound, hlastIndex, hcursor, hassignment, hstartedSigma,
    hstartedCutoff, hstartedFreeze, hstartedBase, hcutpos, hcutcursor, hcursorT,
    hprefixUnknown, hstartedUnknown, past, current, hpast, hcurrent, hsupplied,
    hpastPhysical, hcurrentPhysical, hpastCurrent, hphysicalAppend,
    hcurrentRegisters, hincrement, hcutoffRegisters, hcutoffTime, hnext,
    hH, hcutnum, hcurrentnum, hincreplay, hincnum, hfinishnum, ?_⟩
  exact first_replacement_finish_seed rewards C_star C_h source k i c b hc hbirth I hbase
    N n A H finished hcutnum hcurrentnum hincnum hfinishnum

end Bandits.Support.ReferenceFirstReplacementAcceptedUpNumericalSeed

end
