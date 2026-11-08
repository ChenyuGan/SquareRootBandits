/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionReleaseBoundary

/-!
# Original-source support after the raw replacement collection

This module records the strict-past occurrence event for the actual rawK
release assignment.  The event is read from the existing original-calendar
phase scan, and its gate and pending coordinates are read at one fixed
absolute assignment timestamp.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions BootstrapPrivateRoundStreams
open scoped Classical MeasureTheory
open List

namespace Bandits.Support.ReferencePostReplacementCollectionReleaseSupport

variable {p : ConstructorDimensions.Parameters}

private theorem measurableSet_option_singleton_local {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace]
      ({a} : Set (Option α)) := by
  let e := Equiv.optionEquivSumPUnit α
  have he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e :=
    comap_measurable _
  have hset : ({a} : Set (Option α)) = e ⁻¹' {e a} := by
    ext x
    exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e a with
  | inl value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inr_image (α := α)

local instance {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] :
    @MeasurableSingletonClass (Option α) LaterAssignmentStartMeasurability.optionMeasurableSpace :=
  ⟨measurableSet_option_singleton_local⟩

local instance {p : ConstructorDimensions.Parameters} :
    MeasurableSpace (Option (Finset (Fin (p.m - 1)))) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance {p : ConstructorDimensions.Parameters} :
    MeasurableSpace (Option (Bool × Option (Finset (Fin (p.m - 1))))) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

/-- The original past scan enters the raw replacement collection at timestamp
`u` and closes it on the immediately following calendar record. -/
def postRawKOccurrence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Prop :=
  (ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary
      (ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
        rate rewards C_star C_h u.val z)).1 = 3 ∧
    (ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary
      (ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
        rate rewards C_star C_h (u.val + 1) z)).1 = 4

/-- The tag transition itself is the original later-installation endpoint
test. In particular, the event is computed from the fixed calendar date and
the two adjacent original past scans; it does not choose a date from a future
rawK witness. -/
theorem postRawKOccurrence_iff_actualLaterChosen
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    postRawKOccurrence rate rewards C_star C_h u z ↔
      ∃ payload onset record,
        ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
          rate rewards C_star C_h u.val z = .replacementCollection payload onset ∧
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h u z =
          some record ∧
        ReferenceCollectionPhaseHistory.laterChosen record.input = true := by
  constructor
  · intro h
    cases hstate : ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
        rate rewards C_star C_h u.val z with
    | firstLive => have htag := h.1; simp [hstate, ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary] at htag
    | firstCollection => have htag := h.1; simp [hstate, ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary] at htag
    | replacementLive payload =>
        have htag := h.1
        simp [hstate, ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary] at htag
    | closed => have htag := h.1; simp [hstate, ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary] at htag
    | replacementCollection payload onset =>
        have hnext := h.2
        rw [ReferenceFirstReplacementCollectionPendingFoundation.pastPhase,
          dite_eq_left u.isLt, hstate] at hnext
        cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h u z with
        | none =>
            simp [hr, ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary] at hnext
        | some record =>
            refine ⟨payload, onset, record, rfl, rfl, ?_⟩
            rw [hr] at hnext
            change (ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary
              (ReferenceFirstReplacementCollectionPendingFoundation.advance
                (.replacementCollection payload onset) record)).1 = 4 at hnext
            by_cases hchosen : ReferenceCollectionPhaseHistory.laterChosen record.input = true
            · exact hchosen
            · simp [ReferenceFirstReplacementCollectionPendingFoundation.advance,
                ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary, hchosen] at hnext
  · rintro ⟨payload, onset, record, hphase, hr, hchosen⟩
    constructor
    · simp [hphase, ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary]
    · rw [ReferenceFirstReplacementCollectionPendingFoundation.pastPhase,
        dite_eq_left u.isLt, hphase, hr]
      simp [ReferenceFirstReplacementCollectionPendingFoundation.advance,
        ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary, hchosen]

/-- Once the original past scan closes, its closed state is absorbing at every
later original-calendar date, including dates with no physical record. -/
private theorem pastPhase_closed_after
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n k : ℕ)
    (hclosed : ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
      rate rewards C_star C_h n z = .closed) :
    ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
      rate rewards C_star C_h (n + k) z = .closed := by
  induction k with
  | zero => simpa using hclosed
  | succ k ih =>
      rw [show n + (k + 1) = (n + k) + 1 by omega,
        ReferenceFirstReplacementCollectionPendingFoundation.pastPhase]
      by_cases htime : n + k < p.T
      · simp only [dite_eq_left htime]
        cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
            ⟨n + k, htime⟩ z <;>
          simp [ih, ReferenceFirstReplacementCollectionPendingFoundation.advance]
      · simp only [dite_eq_right htime]
        exact ih

private theorem occurrence_closed_later
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (u : Fin p.T) (hu : postRawKOccurrence rate rewards C_star C_h u z)
    (n : ℕ) (hn : u.val < n) :
    ReferenceFirstReplacementCollectionPendingFoundation.pastPhase rate rewards C_star C_h n z = .closed := by
  have hc : ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
      rate rewards C_star C_h (u.val + 1) z = .closed := by
    have htag := hu.2
    cases he : ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
        rate rewards C_star C_h (u.val + 1) z <;>
      simp only [he, ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary] at htag ⊢
    all_goals omega
  have h := pastPhase_closed_after rate rewards C_star C_h z (u.val + 1)
    (n - (u.val + 1)) hc
  simpa only [Nat.add_sub_of_le (show u.val + 1 ≤ n by omega)] using h

/-- The strict-past occurrence timestamp is unique because its second tag is
the absorbing closed state. -/
theorem postRawKOccurrence_unique
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u v : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hu : postRawKOccurrence rate rewards C_star C_h u z)
    (hv : postRawKOccurrence rate rewards C_star C_h v z) : u = v := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with huv | hvu
  · have hc := occurrence_closed_later rate rewards C_star C_h z u hu v.val huv
    have htag := hv.1
    rw [hc, ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary] at htag
    norm_num at htag
  · have hc := occurrence_closed_later rate rewards C_star C_h z v hv u.val hvu
    have htag := hu.1
    rw [hc, ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary] at htag
    norm_num at htag

private theorem rawCut_not_continuing
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcut : ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = true) :
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen cut = false := by
  unfold ReferenceFirstReplacementCollectionPendingFoundation.isCutoff at hcut
  unfold ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
  cases hstate : cut.output.preparation.coordinator with
  | live registers owned base outcome =>
      rw [hstate] at hcut
      cases outcome <;> simp_all
  | first outcome => simp [hstate] at hcut
  | collection payload ledger saved proposal outcome => simp [hstate] at hcut
  | dagger => simp [hstate] at hcut
  | invalidCollectionCutoff => simp [hstate] at hcut

private theorem raw_scan_endpoint
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
    ∀ birth payload cut, R[v]? = some birth →
      ReferenceFirstReplacementCollectionPendingFoundation.birthPayload birth = some payload →
      R[c]? = some cut → ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = true →
      ReferenceFirstReplacementCollectionPendingFoundation.scan
        (R.take (c + (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
          rate rewards C_star C_h z).length)) =
        .replacementCollection payload (cut.input.time.val + 1) := by
  dsimp only
  intro birth payload cut hb hp hc hcut
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  let c := v + 1 + tail.length
  let W := (R.drop (c + 1)).takeWhile
    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
  let K := cut :: W
  have hraw : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z = K := by
    rw [ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK_eq, hb]
    dsimp only
    rw [hp]
    dsimp only [Option.isSome_some]
    rw [hc]
    dsimp only
    rw [hcut]
    rfl
  have hprefix : K <+: R.drop c := by
    change cut :: (R.drop (c + 1)).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) <+: R.drop c
    exact ReferenceFirstReplacementCollectionPendingFoundation.collection_prefix R c cut hc
  have htake : R.take (c + K.length) = R.take c ++ K := by
    rw [List.take_add]
    exact congrArg (R.take c ++ ·) (List.prefix_iff_eq_take.mp hprefix).symm
  have hbefore : ReferenceFirstReplacementCollectionPendingFoundation.scan
      (R.take c) = .replacementLive payload := by
    dsimp only [c]
    exact ReferenceFirstReplacementCollectionPendingFoundation.scan_before_replacement_cut
      R birth payload hb hp
  have hcutAdvance : ReferenceFirstReplacementCollectionPendingFoundation.advance
      (.replacementLive payload) cut =
        .replacementCollection payload (cut.input.time.val + 1) := by
    have hnot := rawCut_not_continuing rate cut hcut
    simp [ReferenceFirstReplacementCollectionPendingFoundation.advance, hcut, hnot]
  have hWnot : ∀ r ∈ W, ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
    intro r hr
    change r ∈ (R.drop (c + 1)).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) at hr
    have hmem := List.mem_takeWhile_imp hr
    simpa only [Bool.not_eq_true'] using hmem
  have hscanEnd : ReferenceFirstReplacementCollectionPendingFoundation.scan
      (R.take (c + K.length)) = .replacementCollection payload (cut.input.time.val + 1) := by
    rw [htake, ReferenceFirstReplacementCollectionPendingFoundation.scan_append]
    change ReferenceFirstReplacementCollectionPendingFoundation.scan K
      (ReferenceFirstReplacementCollectionPendingFoundation.scan (R.take c)) = _
    rw [hbefore]
    change ReferenceFirstReplacementCollectionPendingFoundation.scan (cut :: W)
      (.replacementLive payload) = _
    rw [ReferenceFirstReplacementCollectionPendingFoundation.scan_cons, hcutAdvance]
    exact ReferenceFirstReplacementCollectionPendingFoundation.scan_collection W payload
      (cut.input.time.val + 1) hWnot
  rw [hraw]
  exact hscanEnd

private theorem complete_record_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hcal : k.val < (ReferenceActivePhysicalHorizon.calendar
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)).length := by
    rw [← htimes, List.length_map]
    exact k.isLt
  have heq : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).map (fun r => r.input.time.val))[k.val]'(by
        rw [List.length_map]; exact k.isLt) =
      (ReferenceActivePhysicalHorizon.calendar
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))[k.val]'hcal := by
    simp only [htimes]
  simpa only [List.getElem_map, ReferenceActivePhysicalHorizon.calendar,
    List.getElem_range', Nat.one_mul] using heq

private theorem complete_record_actual
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h r.input.time z =
      some r := by
  dsimp only
  have ht := complete_record_time rate rewards C_star C_h z k
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  have hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]).input.time.val
    := by omega
  rw [ite_eq_left hs, ht, Nat.add_sub_cancel_left, List.getElem?_eq_getElem k.isLt]

/-- The actual later-chosen endpoint of the computed rawK list is the unique
strict-past tag-3-to-tag-4 occurrence on that same original calendar. The
endpoint uses the suffix index only to select a record; its filtration date
is the absolute physical timestamp `physicalStart + b`. -/
theorem postRawKOccurrence_at_computed_endpoint
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
    let W := (R.drop (c + 1)).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
    ∀ (birth cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (payload : ReferenceFirstReplacementCollectionPendingFoundation.Payload (rate := rate))
      (b : Fin R.length),
      R[v]? = some birth →
      ReferenceFirstReplacementCollectionPendingFoundation.birthPayload birth = some payload →
      R[c]? = some cut →
      ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = true →
      ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z = cut :: W →
      b.val = c + (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z).length →
      ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true →
      ∀ u : Fin p.T,
        postRawKOccurrence rate rewards C_star C_h u z ↔ u.val = s + b.val := by
  dsimp only
  intro birth cut payload b hb hp hc hcut _hraw hbindex hchosen
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hphase : ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
      rate rewards C_star C_h (s + b.val) z =
        .replacementCollection payload (cut.input.time.val + 1) := by
    rw [ReferenceFirstReplacementCollectionPendingFoundation.pastPhase_eq_scan]
    change ReferenceFirstReplacementCollectionPendingFoundation.scan
      (R.take ((s + b.val) - s)) = _
    rw [Nat.add_sub_cancel_left, hbindex]
    exact raw_scan_endpoint rate rewards C_star C_h z birth payload cut hb hp hc hcut
  let u := R[b.val].input.time
  have htime : u.val = s + b.val := complete_record_time rate rewards C_star C_h z b
  have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h u z =
      some R[b.val] := complete_record_actual rate rewards C_star C_h z b
  have hphaseU : ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
      rate rewards C_star C_h u.val z =
        .replacementCollection payload (cut.input.time.val + 1) := by
    rw [htime]
    exact hphase
  have hoccurrence := (postRawKOccurrence_iff_actualLaterChosen rate rewards C_star C_h u z).2
    ⟨payload, cut.input.time.val + 1, R[b.val], hphaseU, hactual, hchosen⟩
  intro t
  constructor
  · intro ht
    have hsame := postRawKOccurrence_unique rate rewards C_star C_h t u z ht hoccurrence
    exact (congrArg Fin.val hsame).trans htime
  · intro ht
    have hsame : t = u := Fin.ext (ht.trans htime.symm)
    simpa only [hsame] using hoccurrence

private theorem complete_record_clock
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
    ReferenceCoordinatorClockDomains.clockAt r.input.rows r.input.selected r.input.time.val r.input.state  := by
  obtain ⟨hc, _, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z k
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  have hl := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z rewards C_star C_h hc
  have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate z rewards C_star C_h initial hl
  have hseed : ReferenceCoordinatorClockDomains.clockAt z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z)
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) initial := by
    have hf := (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h hc).coordinatorFirst
    simp only [ReferenceCoordinatorClockDomains.clockAt, show initial.coordinator = .first from hf]
  have hrun := ReferenceRunClockPreservation.run_clockAt initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (by have := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h; omega)
    (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some rate z rewards C_star C_h initial hl) hseed
  have h := hrun.2.2.2 _ (by rw [← hrecords]; exact List.getElem_mem k.isLt)
  simpa only [h.2.2.1, h.2.2.2.1] using h.1

/-- A release member retains the whole birth payload and the original
incoming-state gate, entry, and pending-at-start observation. This concerns
actual later installations; the rawK selector is applied separately. -/
theorem later_release_member_readouts
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∀ b : Fin R.length,
      ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true →
      ∃ M : ReferenceActivePhysicalStep.Payload rate,
        ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] M ∧
        M.sigma.val = s + b.val ∧
        let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)
        let Rel := (R[b.val] :: W).dropWhile
          ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        ∀ r ∈ Rel,
          ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
          ReferenceRetainedReleasePhaseObservation.localReleaseGate rate (s + b.val)
            r.input.time (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true ∧
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h r.input.time z =
            some r ∧
          ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h (s + b.val)
            r.input.time z = some (true, some
              (ReferencePhysicalReleaseQuota.pendingAtStart M r.input.time r.input.state)) ∧
          ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h (s + b.val)
            r.input.time z = ReferencePhysicalReleaseQuota.pendingAtStart M r.input.time r.input.state := by
  intro R s b hb
  have hh := ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hh
  obtain ⟨rb, qb, beta, bs, _hout, hbirth, _hlater, _hbs, _hbsp, _hbsm,
    _hrbm, _hbe, _hfollowers, _htail, _hnoRelease, hframes⟩ := hh
  have hstamp : rb.payload.sigma.val = s + b.val :=
    (ReferenceAssignmentPayloadChronology.installationBirth_time_eq _ _ hbirth).trans
      (complete_record_time rate rewards C_star C_h z b)
  refine ⟨rb.payload, hbirth, hstamp, ?_⟩
  intro W Rel r hr
  have hrel := ReferencePostReplacementCollectionReleaseBoundary.actual_later_installation_release_suffix_actual_occupied
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hrel
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hr
  obtain ⟨j, hj, heq, selected, hselected, hempty, _hoccupied⟩ := hrel i hi
  change j < W.length at hj
  have hrw : r = W[j]'hj := hir.symm.trans heq
  rw [hrw]
  obtain ⟨incoming, owned, chosen, next, nextOwned, _states, _memories,
    hin, hp, hchosen, _hchosenp, hmissing, hn, hnp, _hupdate, _hchoices,
    _homit, _hclear, _hsteps⟩ := hframes ⟨j, hj⟩
  have hchosenEq : chosen = selected := Option.some.inj (hchosen.symm.trans hselected)
  have hinEmpty : incoming.pendingAtChoice = ∅ := by
    rw [← hmissing, hchosenEq, hempty]
  have hbound : b.val + 1 + j < R.length := by
    have hle := (List.takeWhile_prefix (l := R.drop (b.val + 1))
      (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest (rate := rate))).length_le
    change W.length ≤ (R.drop (b.val + 1)).length at hle
    simp only [List.length_drop] at hle
    have hblt := b.isLt
    omega
  have hindex : W[j]'hj = R[b.val + 1 + j]'hbound := by
    change ((R.drop (b.val + 1)).takeWhile _)[j]'hj = _
    rw [(List.takeWhile_prefix _).getElem hj, List.getElem_drop]
  have htime : (W[j]'hj).input.time.val = s + (b.val + 1 + j) := by
    rw [hindex]
    exact complete_record_time rate rewards C_star C_h z ⟨b.val + 1 + j, hbound⟩
  have hnextStamp : next.payload.sigma.val = s + b.val := by rw [hnp, hstamp]
  obtain ⟨old, oldOwned, oldBase, hold, hstampOld, started, hstart, hf, hs, _hsub,
    _hsNext, _huNext⟩ := ReferenceLocalReleaseGateChronology.step_old_live_predecessor
      (W[j]'hj).input (s + b.val) next nextOwned beta
      (by rw [← (W[j]'hj).output_eq]; exact hn) hnextStamp (by omega)
  have holdEq : old = incoming :=
    (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj (hold.symm.trans hin)).1
  have hcutoff : old.priorClock.u = none := by
    have hclock := complete_record_clock rate rewards C_star C_h z
      ⟨b.val + 1 + j, hbound⟩
    rw [← hindex] at hclock
    simp only [ReferenceCoordinatorClockDomains.clockAt, hold] at hclock
    exact hclock.2.2.2.1
  have holdEmpty : old.pendingAtChoice = ∅ := holdEq.symm ▸ hinEmpty
  have hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate (s + b.val)
      (W[j]'hj).input.time
      (ReferenceActivePhysicalStepMeasurability.encodeState (W[j]'hj).input.state) = true := by
    have hstart' : ReferenceRetainedReleasePhaseObservation.localReleaseStartResult rate
        (W[j]'hj).input.time
        (ReferenceActivePhysicalStepMeasurability.encodeLive old oldOwned oldBase) = .ok started := hstart
    have hf' : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
        (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters old.payload
          (ReferenceActivePhysicalStepMeasurability.encodeLive old oldOwned oldBase)) started := by
      simpa only [CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame,
        ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters,
        ReferenceActivePhysicalStepMeasurability.encodeLive, ReferenceActivePhysicalStep.liveRegistersAt,
        CoordinatorLiveChoiceRecorderStep.Registers.clockPending] using hf
    simp only [ReferenceRetainedReleasePhaseObservation.localReleaseGate,
      ReferenceActivePhysicalStepMeasurability.encodeState,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hold]
    change (decide (old.payload.sigma.val = s + b.val) && decide (old.pendingAtChoice = ∅) &&
      decide (old.priorClock.sigma = some old.payload.sigma) && decide (old.priorClock.u = none) &&
      (match ReferenceRetainedReleasePhaseObservation.localReleaseStartResult rate
        (W[j]'hj).input.time (ReferenceActivePhysicalStepMeasurability.encodeLive old oldOwned oldBase) with
       | .error _ => false
       | .ok result => decide (CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
         (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters old.payload
           (ReferenceActivePhysicalStepMeasurability.encodeLive old oldOwned oldBase)) result))) = true
    rw [hstart']
    simp only [hstampOld, holdEmpty, hs, hcutoff, hf', decide_true, Bool.and_self]
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      (W[j]'hj).input.state.coordinator = some rb.payload := by
    rw [hin]
    exact congrArg some hp
  have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (W[j]'hj).input.time z = some (W[j]'hj) := by
    rw [hindex]
    exact complete_record_actual rate rewards C_star C_h z ⟨b.val + 1 + j, hbound⟩
  have hentry : ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
      (s + b.val) (W[j]'hj).input.time z = some (true, some
        (ReferencePhysicalReleaseQuota.pendingAtStart rb.payload (W[j]'hj).input.time (W[j]'hj).input.state)) := by
    simp only [ReferenceSourcePrefixHistoryFiltration.entry,
      ReferenceSourcePrefixHistoryFiltration.incoming, hactual, Option.map_some,
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry, hgate, ite_true,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
    have hlocal : ReferenceRetainedReleasePhaseObservation.localStoredPayload
        (ReferenceActivePhysicalStepMeasurability.encodeState (W[j]'hj).input.state) = some rb.payload := by
      have hcode : (ReferenceActivePhysicalStepMeasurability.encodeState
          (W[j]'hj).input.state).1 = .inr (.inl
            (incoming.payload, ReferenceActivePhysicalStepMeasurability.encodeLive incoming owned beta)) := by
        change ReferenceActivePhysicalStepMeasurability.encodeCoordinator _ = _
        rw [hin]
        rfl
      unfold ReferenceRetainedReleasePhaseObservation.localStoredPayload
      rw [hcode]
      exact congrArg some hp
    rw [hlocal]
    simp only [ReferenceRetainedReleasePhaseObservation.localReleasePending,
      hgate, ite_true]
  exact ⟨hstored, hgate, hactual, hentry, by
    simp only [ReferenceSourcePrefixHistoryFiltration.pending, hentry, Option.bind_some,
      Option.getD_some]⟩

private theorem gate_start_frame
    (rate : ReferenceActivePhysicalStep.RateInput p) (a : ℕ) (time : Fin p.T)
    (state : ReferenceActivePhysicalStep.State p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hin : state.coordinator = .live r q base)
    (hg : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate a time
      (ReferenceActivePhysicalStepMeasurability.encodeState state) = true) :
    ∃ started, CoordinatorPhaseClock.startRound p rate.eta.val time r.priorClock
      r.clockPending = .ok started ∧
      CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
        (ReferenceActivePhysicalStep.liveRegistersAt r time) started := by
  simp only [ReferenceRetainedReleasePhaseObservation.localReleaseGate,
    ReferenceActivePhysicalStepMeasurability.encodeState,
    ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hin] at hg
  change (decide (r.payload.sigma.val = a) && decide (r.pendingAtChoice = ∅) &&
    decide (r.priorClock.sigma = some r.payload.sigma) && decide (r.priorClock.u = none) &&
    (match ReferenceRetainedReleasePhaseObservation.localReleaseStartResult rate time
      (ReferenceActivePhysicalStepMeasurability.encodeLive r q base) with
      | .error _ => false
      | .ok result => decide (CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
        (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters r.payload
          (ReferenceActivePhysicalStepMeasurability.encodeLive r q base)) result))) = true at hg
  simp only [Bool.and_eq_true] at hg
  cases he : ReferenceRetainedReleasePhaseObservation.localReleaseStartResult rate time
      (ReferenceActivePhysicalStepMeasurability.encodeLive r q base) with
  | error failure => simp only [he, Bool.false_eq_true, and_false] at hg
  | ok started =>
    have hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
        (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters r.payload
          (ReferenceActivePhysicalStepMeasurability.encodeLive r q base)) started := by
      exact of_decide_eq_true (by simpa only [he] using hg.2)
    refine ⟨started, he, ?_⟩
    simpa only [CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame,
      ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters,
      ReferenceActivePhysicalStepMeasurability.encodeLive, ReferenceActivePhysicalStep.liveRegistersAt,
      CoordinatorLiveChoiceRecorderStep.Registers.clockPending] using hframe

/-- Backward propagation uses actual predecessor adjacency and the old birth
stamp, so it cannot jump a cutoff and later reappear with that stamp. -/
private theorem old_live_reaches
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (e n a : ℕ)
    (hbound : e + n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hold : a < ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + e)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next) (base : Fin (p.m - 1) → ℕ)
    (hin : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[e + n]).input.state.coordinator = .live next owned base)
    (ha : next.payload.sigma.val = a) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[e]'(by omega)
    ∃ old q beta, r.input.state.coordinator = .live old q beta ∧
      old.payload.sigma.val = a ∧
      (0 < n → ∃ started,
        CoordinatorPhaseClock.startRound p rate.eta.val r.input.time old.priorClock
          old.clockPending = .ok started ∧
        CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          (ReferenceActivePhysicalStep.liveRegistersAt old r.input.time) started) := by
  induction n generalizing next base with
  | zero => exact ⟨next, owned, base, hin, ha, by omega⟩
  | succ n ih =>
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    change e + (n + 1) < R.length at hbound
    have hprev : e + n < R.length := by omega
    have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
      (rate := rate) rewards C_star C_h z (e + n) (by omega)
    have hout : (ReferenceActivePhysicalStep.step R[e + n].input).next.coordinator =
        .live next owned base := by
      rw [← (R[e + n]).output_eq]
      rw [← hadj]
      simpa only [Nat.add_assoc] using hin
    have ht := complete_record_time rate rewards C_star C_h z ⟨e + n, hprev⟩
    change R[e + n].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + (e + n) at ht
    obtain ⟨previous, pq, pb, hp, hpa, started, hstart, hf, _hs, _hsub, _hns, _hnu⟩ :=
      ReferenceLocalReleaseGateChronology.step_old_live_predecessor R[e + n].input a
        next owned base hout ha (by omega)
    obtain ⟨old, q, beta, hcoord, hstamp, hframes⟩ := ih (by omega) previous pq pb hp hpa
    refine ⟨old, q, beta, hcoord, hstamp, ?_⟩
    intro _
    by_cases hn : n = 0
    · subst n
      have heq : old = previous :=
        (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj (hcoord.symm.trans hp)).1
      cases heq
      exact ⟨started, hstart, hf⟩
    · exact hframes (by omega)

private theorem cutoff_has_no_frame
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hu : r.priorClock.u = none)
    (chosen : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput record.input r q base))
    (htag : match chosen with | .cutoffChosen .. => True | _ => False)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val record.input.time
      r.priorClock r.clockPending = .ok started)
    (hf : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
      (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time) started) : False := by
  cases chosen with
  | cutoffChosen dispatched hcall ledger hinit hledger hvalid hclock hpending hno selection =>
    have heq : started = dispatched.startResult := Except.ok.inj (hstart.symm.trans hcall)
    have h := congrArg CoordinatorPhaseClock.ClockRegisters.u hf.1
    change started.clock.u = r.priorClock.u at h
    rw [heq, hclock] at h
    simp only [hu, reduceCtorEq] at h
  | _ => exact htag

/-- The local gate at a later birth's absolute timestamp selects only that
birth's continuing prefix. The first excluded record is the actual cutoff;
backward chronology rules out any later reappearance of the old stamp. -/
private theorem later_gate_in_continuing_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∀ b : Fin R.length,
      ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true →
      ∀ j : Fin R.length,
      ReferenceRetainedReleasePhaseObservation.localReleaseGate rate (s + b.val)
        R[j.val].input.time (ReferenceActivePhysicalStepMeasurability.encodeState R[j.val].input.state) = true →
      b.val < j.val ∧ j.val < b.val + 1 +
        (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)).length := by
  intro R s b hb j hg
  obtain ⟨current, cq, cb, hc, hstamp, _hempty, _hs, _hu⟩ :=
    ReferenceLocalReleaseGateChronology.gate_live (s + b.val) _ _ hg
  have hj := j.isLt
  change j.val < R.length at hj
  obtain ⟨cross, _hspan, _hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z j
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h cross
  have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate z rewards C_star C_h initial
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState rate z rewards C_star C_h cross)
  obtain ⟨_M, _birth, _hstored, _hMsigma, _hmem, _hbirth, _hbirthtime, _hs, hprior⟩ :=
    ReferenceLocalReleaseGateChronology.run_gate_record_birth initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s
      (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h cross).activeAtStart
      (p.T - s) (by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
        dsimp only [s]
        omega)
      (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h cross).coordinatorFirst
      R[j.val] (by rw [← hrecords]; exact List.getElem_mem j.isLt) (s + b.val) hg
  have ht : R[j.val].input.time.val = s + j.val := complete_record_time rate rewards C_star C_h z j
  have hbj : b.val < j.val := by omega
  refine ⟨hbj, ?_⟩
  have hh := ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hh
  obtain ⟨rb, qb, beta, _bs, hout, _hbirth, hlater, _hbs, _hbsp, _hbsm,
    _hrbm, _hbe, _hfollowers, _htail, _hnoRelease, _hframes⟩ := hh
  let k : Fin R.length := ⟨b.val + 1, by omega⟩
  have hstate : R[k.val].input.state.coordinator = .live rb qb beta := by
    rw [show R[k.val].input.state = R[b.val].output.next from
      ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
        (rate := rate) rewards C_star C_h z b.val (by
          change b.val + 1 < R.length
          omega)]
    exact hout
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z k.val
  have hmax := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_maximal
    rewards C_star C_h z k rb qb beta hstate hlater
  rcases hmax with hend | ⟨he, rv, qv, _hp, hin, chosen, hchosen, htag⟩
  · change j.val < k.val + W.length
    change k.val + W.length = R.length at hend
    omega
  · change k.val + W.length < R.length at he
    by_contra hn
    change ¬ j.val < k.val + W.length at hn
    have hle : k.val + W.length ≤ j.val := by omega
    let e : Fin R.length := ⟨k.val + W.length, he⟩
    change R[e.val].input.state.coordinator = .live rv qv beta at hin
    change CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput R[e.val].input rv qv beta) at chosen
    have hclock := complete_record_clock rate rewards C_star C_h z e
    change ReferenceCoordinatorClockDomains.clockAt R[e.val].input.rows
      R[e.val].input.selected R[e.val].input.time.val R[e.val].input.state at hclock
    simp only [ReferenceCoordinatorClockDomains.clockAt, hin] at hclock
    have hnone : rv.priorClock.u = none := hclock.2.2.2.1
    by_cases heq : e.val = j.val
    · have hsame : e = j := Fin.ext heq
      have hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate (s + b.val)
          R[e.val].input.time (ReferenceActivePhysicalStepMeasurability.encodeState R[e.val].input.state) = true := by
        simpa only [hsame] using hg
      obtain ⟨started, hstart, hf⟩ := gate_start_frame rate (s + b.val) _ _ rv qv beta hin hgate
      exact cutoff_has_no_frame rate R[e.val] rv qv beta hnone chosen (by cases chosen <;> exact htag) started hstart hf
    · have hlt : e.val < j.val := by dsimp only [e] at heq ⊢; omega
      have hreach := old_live_reaches rate rewards C_star C_h z e.val (j.val - e.val)
        (s + b.val) (by
          change e.val + (j.val - e.val) < R.length
          omega) (by dsimp only [e, k, s]; omega)
        current cq cb (by simpa only [Nat.add_sub_of_le (show e.val ≤ j.val from hle)] using hc) hstamp
      obtain ⟨old, oq, ob, ho, _ha, hframe⟩ := hreach
      obtain ⟨started, hstart, hf⟩ := hframe (by omega)
      have heq : old = rv :=
        (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj (ho.symm.trans hin)).1
      subst old
      exact cutoff_has_no_frame rate R[e.val] rv qv beta hnone chosen (by cases chosen <;> exact htag) started hstart hf

/-- Exact ordered identification of the actual later-installation release
suffix with the original incoming-state gate at its absolute birth stamp. -/
theorem later_release_filter_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∀ b : Fin R.length,
      ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true →
      R.filter (fun r => ReferenceRetainedReleasePhaseObservation.localReleaseGate rate (s + b.val)
        r.input.time (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)) =
      (R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (b.val + 1)).dropWhile
          ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice := by
  intro R s b hb
  let gate := fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
    ReferenceRetainedReleasePhaseObservation.localReleaseGate rate (s + b.val)
      r.input.time (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b.val + 1)
  let V := R[b.val] :: W
  let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
  have hV : V <+ R := by
    have hp : V <+: R.drop b.val := by
      rw [List.drop_eq_getElem_cons b.isLt]
      exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
    exact hp.sublist.trans (List.drop_sublist b.val R)
  have hsub : Rel <+ R := (List.dropWhile_sublist _).trans hV
  obtain ⟨M, _hbirth, _hstamp, hread⟩ := later_release_member_readouts
    rate rewards C_star C_h z b hb
  have hforward : ∀ r ∈ Rel, gate r = true := fun r hr => (hread r hr).2.1
  have hreverse : ∀ r ∈ R, gate r = true → r ∈ Rel := by
    intro r hr hg
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hr
    rw [← heq] at hg ⊢
    let jf : Fin R.length := ⟨j, hj⟩
    obtain ⟨hlo, hhi⟩ := later_gate_in_continuing_prefix rate rewards C_star C_h z b hb jf hg
    change b.val < j at hlo
    change j < b.val + 1 + W.length at hhi
    let l := j - (b.val + 1)
    have hl : l < W.length := by dsimp only [l]; omega
    have hidx : b.val + 1 + l = j := by dsimp only [l]; omega
    have hw : W[l]'hl = R[j]'hj := by
      change ((R.drop (b.val + 1)).takeWhile _)[l]'hl = _
      rw [(List.takeWhile_prefix _).getElem hl, List.getElem_drop]
      exact getElem_congr_idx hidx
    have hh := ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
      rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hh
    obtain ⟨_rb, _qb, beta, _bs, _hout, _hb, _hlater, _hbs, _hbsp, _hbsm,
      _hrbm, _hbe, _hfollowers, _htail, _hnoRelease, hframes⟩ := hh
    obtain ⟨incoming, owned, chosen, _next, _nextOwned, _states, _memories,
      hin, _hp, hs, _hpay, hm, _hn, _hnp, _hu, _hc, _homit, _hclear, _hsteps⟩ := hframes ⟨l, hl⟩
    have hgate : gate (W[l]'hl) = true := by rw [hw]; exact hg
    obtain ⟨current, cq, cb, hc, _ha, he, _hclock, _hcut⟩ :=
      ReferenceLocalReleaseGateChronology.gate_live (s + b.val) _ _ hgate
    have hrEq : incoming = current :=
      (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj (hin.symm.trans hc)).1
    have hfalse : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice (W[l]'hl) = false := by
      unfold ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
      rw [hs]
      simp only [hm, hrEq, he, Finset.not_nonempty_empty, decide_false]
    have hmem : (W[l]'hl) ∈ V := List.mem_cons_of_mem _ (List.getElem_mem hl)
    have hsplit : V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice ++ Rel = V :=
      List.takeWhile_append_dropWhile
    rw [← hsplit, List.mem_append] at hmem
    rcases hmem with hH | hRel
    · have htrue := List.mem_takeWhile_imp hH
      rw [hfalse] at htrue
      cases htrue
    · rw [← hw]
      exact hRel
  have hself : Rel.filter gate = Rel := List.filter_eq_self.mpr hforward
  have hfilteredSub : Rel <+ R.filter gate := by
    rw [← hself]
    exact hsub.filter gate
  have hnodup : R.Nodup := by
    have ht := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
      rate z rewards C_star C_h
    have hn : (R.map (fun r => r.input.time.val)).Nodup := by
      rw [ht]
      exact List.nodup_range'
    exact List.Nodup.of_map _ hn
  have hsets : (R.filter gate).toFinset = Rel.toFinset := by
    ext r
    simp only [List.mem_toFinset, List.mem_filter]
    exact ⟨fun h => hreverse r h.1 h.2, fun h => ⟨hsub.subset h, hforward r h⟩⟩
  have hlen : Rel.length = (R.filter gate).length := by
    rw [← List.toFinset_card_of_nodup (hsub.nodup hnodup),
      ← List.toFinset_card_of_nodup (hnodup.filter gate), hsets]
  exact (hfilteredSub.eq_of_length hlen).symm

/-- The launched source run used by the local pending-history APIs is exactly
the same complete suffix. Its launch proof is obtained from the actual birth. -/
theorem later_release_source_gate_records
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∀ b : Fin R.length,
      ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true →
      ∃ hc : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true,
      ReferenceLocalReleasePendingHistory.sourceLocalGateRecords rate z rewards C_star C_h hc
        s (p.T - s) rfl (by
          have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
          dsimp only [s]
          omega) (s + b.val) =
        (R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)).dropWhile
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice := by
  intro R s b hb
  obtain ⟨hc, _hspan, _hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z b
  refine ⟨hc, ?_⟩
  have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate z rewards C_star C_h (ReferenceLocalReleaseGateChronology.sourceSeed
      rate z rewards C_star C_h hc)
    (ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hc)
  change (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hc
    s (p.T - s) rfl _).records.filter _ = _
  have heq : (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h hc
      s (p.T - s) rfl (by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
        dsimp only [s]
        omega)).records = R := hrecords.symm
  rw [heq]
  exact later_release_filter_eq rate rewards C_star C_h z b hb

private theorem occurrence_forces_final_closed
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (u : Fin p.T) (hu : postRawKOccurrence rate rewards C_star C_h u z) :
    ReferenceFirstReplacementCollectionPendingFoundation.scan
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) = .closed := by
  have h := occurrence_closed_later rate rewards C_star C_h z u hu p.T u.isLt
  rw [ReferenceFirstReplacementCollectionPendingFoundation.pastPhase_eq_scan,
    ← ReferenceCompletePhysicalHistory.completeSuffixRecords_length,
    List.take_length] at h
  exact h

private theorem no_occurrence_at_live_close
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (M : ReferenceActivePhysicalStep.Payload rate)
    (hb : ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
      rate rewards C_star C_h n z = .replacementLive M)
    (ha : ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
      rate rewards C_star C_h (n + 1) z = .closed) :
    ∀ u : Fin p.T, ¬ postRawKOccurrence rate rewards C_star C_h u z := by
  intro u hu
  by_cases hlt : u.val < n
  · have h := occurrence_closed_later rate rewards C_star C_h z u hu n hlt
    rw [hb] at h
    cases h
  · have htag := hu.1
    by_cases heq : u.val = n
    · rw [heq, hb, ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary] at htag
      norm_num at htag
    · have h := pastPhase_closed_after rate rewards C_star C_h z (n + 1)
        (u.val - (n + 1)) ha
      rw [Nat.add_sub_of_le (by omega)] at h
      rw [h, ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary] at htag
      norm_num at htag

/-- All original branches are discharged internally. A tag-3-to-tag-4
occurrence is exactly the nonempty rawK endpoint when that endpoint is an
actual physical record, at its absolute timestamp. -/
theorem postRawKOccurrence_iff_endpoint
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
    let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z
    ∀ u : Fin p.T, postRawKOccurrence rate rewards C_star C_h u z ↔
      K ≠ [] ∧ c + K.length < R.length ∧ u.val = s + (c + K.length) := by
  intro R s w v c K
  have hB := ReferencePostReplacementCollectionReleaseBoundary.raw_collection_next_installation_release_boundary
    rate rewards C_star C_h z
  obtain ⟨habs, _hnone, _hterminal, hbranches⟩ := hB
  have final_excludes : ∀ (phase : ReferenceFirstReplacementCollectionPendingFoundation.PastPhase rate),
      phase ≠ .closed → ReferenceFirstReplacementCollectionPendingFoundation.scan R = phase →
      ∀ u : Fin p.T, ¬ postRawKOccurrence rate rewards C_star C_h u z := by
    intro phase hne he u hu
    exact hne (he.symm.trans (occurrence_forces_final_closed rate rewards C_star C_h z u hu))
  cases hb : R[v]? with
  | none =>
    rw [hb] at hbranches
    have hv : v = R.length := hbranches
    have hK : K = [] := habs.mpr (Or.inl hb)
    have hex : ∀ u : Fin p.T, ¬ postRawKOccurrence rate rewards C_star C_h u z := by
      by_cases hw : w < R.length
      · have hscan := ReferenceFirstReplacementCollectionPendingFoundation.scan_before_birth (rate := rate) R hw
        change ReferenceFirstReplacementCollectionPendingFoundation.scan (R.take v) = _ at hscan
        rw [hv, List.take_length] at hscan
        exact final_excludes _ (by intro h; cases h) hscan
      · have hp : ReferenceFirstLiveConfirmationHistory.firstLiveWindow R <+: R := List.takeWhile_prefix _
        have heq : ReferenceFirstLiveConfirmationHistory.firstLiveWindow R = R := hp.eq_of_length (by omega)
        have hscan := ReferenceFirstReplacementCollectionPendingFoundation.scan_firstLiveWindow (rate := rate) R
        rw [heq] at hscan
        exact final_excludes _ (by intro h; cases h) hscan
    intro u
    simp only [hK, ne_eq, not_true_eq_false, false_and, iff_false]
    exact hex u
  | some birth =>
    rw [hb] at hbranches
    dsimp only at hbranches
    obtain ⟨payload, hp, _hcBound, hbranch⟩ := hbranches
    have hscanC := ReferenceFirstReplacementCollectionPendingFoundation.scan_before_replacement_cut
      (rate := rate) R birth payload hb hp
    change ReferenceFirstReplacementCollectionPendingFoundation.scan (R.take c) = _ at hscanC
    cases hc : R[c]? with
    | none =>
      rw [hc] at hbranch
      dsimp only at hbranch
      have hK : K = [] := habs.mpr (Or.inr ⟨birth, payload, hb, hp, Or.inl hc⟩)
      have hscan : ReferenceFirstReplacementCollectionPendingFoundation.scan R = .replacementLive payload := by
        have hceq : c = R.length := hbranch.1
        rw [hceq, List.take_length] at hscanC
        exact hscanC
      intro u
      simp only [hK, ne_eq, not_true_eq_false, false_and, iff_false]
      exact final_excludes _ (by intro h; cases h) hscan u
    | some cut =>
      rw [hc] at hbranch
      dsimp only at hbranch
      by_cases hcut : ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = true
      · rw [ite_eq_left hcut] at hbranch
        have hraw : K = cut :: (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) := by
          change ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z = _
          rw [ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK_eq, hb]
          dsimp only
          rw [hp]
          dsimp only [Option.isSome_some]
          rw [hc]
          dsimp only
          rw [hcut]
          rfl
        have hK : K ≠ [] := by rw [hraw]; exact List.cons_ne_nil _ _
        rcases hbranch with hend | ⟨b, hindex, hchosen, _hrest⟩
        · change c + K.length = R.length at hend
          have hscan := raw_scan_endpoint rate rewards C_star C_h z birth payload cut hb hp hc hcut
          change ReferenceFirstReplacementCollectionPendingFoundation.scan (R.take (c + K.length)) = _ at hscan
          rw [hend, List.take_length] at hscan
          intro u
          have hex := final_excludes _ (by intro h; cases h) hscan u
          simp only [hend, lt_self_iff_false, false_and, and_false, iff_false]
          exact hex
        · change b.val = c + K.length at hindex
          intro u
          have h := postRawKOccurrence_at_computed_endpoint rate rewards C_star C_h z
            birth cut payload b hb hp hc hcut hraw hindex hchosen u
          have hblt : c + K.length < R.length := by rw [← hindex]; exact b.isLt
          simpa only [ne_eq, hK, hblt, not_false_eq_true, true_and, hindex, s] using h
      · have hfalse : ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = false :=
          Bool.eq_false_of_not_eq_true hcut
        have hK : K = [] := habs.mpr (Or.inr ⟨birth, payload, hb, hp,
          Or.inr ⟨cut, hc, hfalse⟩⟩)
        have hsearch := ReferenceFirstReplacementCollectionGlobalDecoderCharge.replacement_search_endpoint
          rate rewards C_star C_h z birth payload hb hp
        have hnoncont := (hsearch.2.2 cut hc).2.1
        obtain ⟨hcLt, hget⟩ := List.getElem?_eq_some_iff.mp hc
        let k : Fin R.length := ⟨c, hcLt⟩
        have ht := complete_record_time rate rewards C_star C_h z k
        have hactual := complete_record_actual rate rewards C_star C_h z k
        rw [hget] at ht hactual
        have hbefore : ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
            rate rewards C_star C_h (s + c) z = .replacementLive payload := by
          rw [ReferenceFirstReplacementCollectionPendingFoundation.pastPhase_eq_scan]
          change ReferenceFirstReplacementCollectionPendingFoundation.scan (R.take ((s + c) - s)) = _
          rw [Nat.add_sub_cancel_left]
          exact hscanC
        have hafter : ReferenceFirstReplacementCollectionPendingFoundation.pastPhase
            rate rewards C_star C_h (s + c + 1) z = .closed := by
          rw [← ht, ReferenceFirstReplacementCollectionPendingFoundation.pastPhase,
            dite_eq_left cut.input.time.isLt, hactual]
          rw [ht, hbefore]
          simp only [ReferenceFirstReplacementCollectionPendingFoundation.advance, hnoncont,
            hfalse, Bool.false_eq_true, ite_false]
        intro u
        simp only [hK, ne_eq, not_true_eq_false, false_and, iff_false]
        exact no_occurrence_at_live_close rate rewards C_star C_h z (s + c) payload hbefore hafter u

/-- Literal post-rawK release records. Empty raw collection and an endpoint
at the horizon contribute no assignment and no fabricated birth payload. -/
def rawReleaseRecords
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :=
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
  let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z
  if K = [] then [] else
    if hb : c + K.length < R.length then
      (R[c + K.length]'hb :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (c + K.length + 1)).dropWhile
          ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    else []

private theorem raw_endpoint_chosen
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
    let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z
    ∀ b : Fin R.length, b.val = c + K.length → K ≠ [] →
      ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true := by
  intro R w v c K b hb hK
  have ht := complete_record_time rate rewards C_star C_h z b
  have he : postRawKOccurrence rate rewards C_star C_h R[b.val].input.time z :=
    (postRawKOccurrence_iff_endpoint rate rewards C_star C_h z _).2
      ⟨hK, by rw [← hb]; exact b.isLt, by simpa only [hb] using ht⟩
  obtain ⟨_M, _onset, record, _hphase, hrecord, hchosen⟩ :=
    (postRawKOccurrence_iff_actualLaterChosen rate rewards C_star C_h _ z).1 he
  have hactual := complete_record_actual rate rewards C_star C_h z b
  have heq : record = R[b.val] := Option.some.inj (hrecord.symm.trans hactual)
  simpa only [heq] using hchosen

/-- On the computed present endpoint branch, the source gate is exactly Rel
in order and every Rel member carries the same whole actual birth payload. -/
theorem raw_release_source_readouts
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
    let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z
    let Rel := rawReleaseRecords rate rewards C_star C_h z
    if _hK : K = [] then Rel = [] else
    if hb : c + K.length < R.length then
      (∃ hc : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true,
        ReferenceLocalReleasePendingHistory.sourceLocalGateRecords rate z rewards C_star C_h hc
          s (p.T - s) rfl (by
            have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
            dsimp only [s]
            omega) (s + (c + K.length)) = Rel) ∧
      ∃ M : ReferenceActivePhysicalStep.Payload rate,
        ReferenceAssignmentPayloadPersistence.InstallationBirth R[c + K.length] M ∧
        M.sigma.val = s + (c + K.length) ∧
        ∀ r ∈ Rel,
          ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
          ReferenceRetainedReleasePhaseObservation.localReleaseGate rate M.sigma.val r.input.time
            (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true ∧
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h r.input.time z = some r ∧
          ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h M.sigma.val r.input.time z =
            some (true, some (ReferencePhysicalReleaseQuota.pendingAtStart M r.input.time r.input.state)) ∧
          ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h M.sigma.val r.input.time z =
            ReferencePhysicalReleaseQuota.pendingAtStart M r.input.time r.input.state
    else Rel = [] := by
  intro R s w v c K Rel
  have hdef : Rel = if K = [] then [] else
      if hb : c + K.length < R.length then
        (R[c + K.length]'hb :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (c + K.length + 1)).dropWhile
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice else [] := rfl
  split
  · rename_i hK
    rw [hdef, ite_eq_left hK]
  · rename_i hK
    split
    · rename_i hb
      let b : Fin R.length := ⟨c + K.length, hb⟩
      have hchosen := raw_endpoint_chosen rate rewards C_star C_h z b rfl hK
      have hRel : Rel = (R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b.val + 1)).dropWhile
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice := by
        rw [hdef, ite_eq_right hK, dite_eq_left hb]
      rw [hRel]
      obtain ⟨hc, hgate⟩ := later_release_source_gate_records rate rewards C_star C_h z b hchosen
      obtain ⟨M, hbirth, hstamp, hread⟩ := later_release_member_readouts rate rewards C_star C_h z b hchosen
      refine ⟨⟨hc, hgate⟩, M, hbirth, hstamp, ?_⟩
      intro r hr
      simpa only [hstamp] using hread r hr
    · rename_i hb
      rw [hdef, ite_eq_right hK, dite_eq_right hb]

/-- The fixed-timestamp release gate selected by the original scan occurrence.
The timestamp `u` is absolute and is strictly earlier than the source round. -/
def postRawKReleaseSupport
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Prop :=
  ∃ u : Fin p.T, u.val < t.val ∧ postRawKOccurrence rate rewards C_star C_h u z ∧
    (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h u.val t z).map
      Prod.fst = some true

/-- Pending membership uses the same fixed earlier assignment timestamp as the
gate occurrence. -/
def postRawKPendingSupport
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Prop :=
  ∃ u : Fin p.T, u.val < t.val ∧ postRawKOccurrence rate rewards C_star C_h u z ∧
    i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h u.val t z

private theorem entry_gate_iff_record
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (a : ℕ) (t : Fin p.T) :
    (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h a t z).map Prod.fst = some true ↔
      ∃ r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h,
        r.input.time = t ∧ ReferenceRetainedReleasePhaseObservation.localReleaseGate rate a t
          (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  constructor
  · intro hg
    cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
    | none => simp only [ReferenceSourcePrefixHistoryFiltration.entry,
        ReferenceSourcePrefixHistoryFiltration.incoming, hr, Option.map_none] at hg; cases hg
    | some r =>
      have hlookup := hr
      unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hlookup
      split at hlookup
      · obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hlookup
        have ht := complete_record_time rate rewards C_star C_h z ⟨t.val - s, hk⟩
        rw [hget] at ht
        have htime : r.input.time = t := Fin.ext (by dsimp only [s] at ht; omega)
        refine ⟨r, hget ▸ List.getElem_mem hk, htime, ?_⟩
        simpa only [ReferenceSourcePrefixHistoryFiltration.entry,
          ReferenceSourcePrefixHistoryFiltration.incoming, hr, Option.map_some,
          ReferenceRetainedReleasePhaseObservation.localReleaseEntry, Option.some.injEq] using hg
      · cases hlookup
  · rintro ⟨r, hr, ht, hg⟩
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hr
    have hactual := complete_record_actual rate rewards C_star C_h z ⟨j, hj⟩
    dsimp only at hactual
    rw [heq, ht] at hactual
    simpa only [ReferenceSourcePrefixHistoryFiltration.entry,
      ReferenceSourcePrefixHistoryFiltration.incoming, hactual, Option.map_some,
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry, Option.some.injEq] using hg

/-- The actual computed Rel support is the finite fixed-timestamp union.
The timestamp in each summand is strictly earlier than this source round. -/
theorem rawReleaseRecords_support_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    (∃ r ∈ rawReleaseRecords rate rewards C_star C_h z, r.input.time = t) ↔
      postRawKReleaseSupport rate rewards C_star C_h t z := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
  let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z
  have hocc := postRawKOccurrence_iff_endpoint rate rewards C_star C_h z
  by_cases hK : K = []
  · have hnil : rawReleaseRecords rate rewards C_star C_h z = [] := by
      unfold rawReleaseRecords
      exact ite_eq_left hK
    rw [hnil]
    simp only [List.not_mem_nil, false_and, exists_false, false_iff, postRawKReleaseSupport, not_exists]
    rintro u ⟨_hut, he, _hg⟩
    exact (hocc u).1 he |>.1 hK
  · by_cases hb : c + K.length < R.length
    · let b : Fin R.length := ⟨c + K.length, hb⟩
      have hchosen := raw_endpoint_chosen rate rewards C_star C_h z b rfl hK
      have hRel : rawReleaseRecords rate rewards C_star C_h z = R.filter
          (fun r => ReferenceRetainedReleasePhaseObservation.localReleaseGate rate (s + b.val)
            r.input.time (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)) := by
        rw [later_release_filter_eq rate rewards C_star C_h z b hchosen]
        unfold rawReleaseRecords
        rw [ite_eq_right hK, dite_eq_left hb]
      rw [hRel]
      constructor
      · rintro ⟨r, hr, htime⟩
        obtain ⟨hrR, hg⟩ := List.mem_filter.mp hr
        obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hrR
        have hgate := hg
        rw [← heq] at hgate
        have hprior := (later_gate_in_continuing_prefix rate rewards C_star C_h z b hchosen ⟨j, hj⟩ hgate).1
        change b.val < j at hprior
        have ht := complete_record_time rate rewards C_star C_h z ⟨j, hj⟩
        change R[j].input.time.val = s + j at ht
        rw [heq, htime] at ht
        let u := R[b.val].input.time
        have hu : u.val = s + b.val := complete_record_time rate rewards C_star C_h z b
        refine ⟨u, by rw [hu, ht]; omega, (hocc u).2 ⟨hK, hb, hu⟩, ?_⟩
        have hentry := (entry_gate_iff_record rate rewards C_star C_h z (s + b.val) t).2
          ⟨r, hrR, htime, by simpa only [htime] using hg⟩
        simpa only [hu] using hentry
      · rintro ⟨u, _hu, he, hg⟩
        have hstamp : u.val = s + b.val := (hocc u).1 he |>.2.2
        rw [hstamp] at hg
        obtain ⟨r, hr, ht, hgate⟩ := (entry_gate_iff_record rate rewards C_star C_h z (s + b.val) t).1 hg
        exact ⟨r, List.mem_filter.mpr ⟨hr, by simpa only [ht] using hgate⟩, ht⟩
    · have hnil : rawReleaseRecords rate rewards C_star C_h z = [] := by
        unfold rawReleaseRecords
        rw [ite_eq_right hK, dite_eq_right hb]
      rw [hnil]
      simp only [List.not_mem_nil, false_and, exists_false, false_iff, postRawKReleaseSupport, not_exists]
      rintro u ⟨_hut, he, _hg⟩
      exact hb ((hocc u).1 he).2.1

private theorem pending_mem_gate
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (a : ℕ) (t : Fin p.T) (i : Fin (p.m - 1))
    (hi : i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h a t z) :
    (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h a t z).map Prod.fst = some true := by
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none => simp [ReferenceSourcePrefixHistoryFiltration.pending,
      ReferenceSourcePrefixHistoryFiltration.entry, ReferenceSourcePrefixHistoryFiltration.incoming, hr] at hi
  | some r =>
    cases hg : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate a t
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) <;>
      simp_all only [ReferenceSourcePrefixHistoryFiltration.pending,
        ReferenceSourcePrefixHistoryFiltration.entry, ReferenceSourcePrefixHistoryFiltration.incoming,
        ReferenceRetainedReleasePhaseObservation.localReleaseEntry, Option.map_some, Bool.false_eq_true,
        ite_false, ite_true, Option.bind_some, Option.getD_none, Finset.notMem_empty]

private theorem raw_member_pending_readout
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : r ∈ rawReleaseRecords rate rewards C_star C_h z) :
    ∃ M, ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
      ∀ u : Fin p.T, postRawKOccurrence rate rewards C_star C_h u z →
        ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h u.val r.input.time z =
          ReferencePhysicalReleaseQuota.pendingAtStart M r.input.time r.input.state := by
  have hd := raw_release_source_readouts rate rewards C_star C_h z
  dsimp only at hd
  split at hd
  · rw [hd] at hr
    cases hr
  · split at hd
    · obtain ⟨_hsource, M, _hbirth, hstamp, hread⟩ := hd
      refine ⟨M, (hread r hr).1, ?_⟩
      intro u hu
      have he := ((postRawKOccurrence_iff_endpoint rate rewards C_star C_h z u).1 hu).2.2
      have hs : u.val = M.sigma.val := he.trans hstamp.symm
      rw [hs]
      exact (hread r hr).2.2.2.2
    · rw [hd] at hr
      cases hr

/-- Actual Rel pending membership uses the same earlier occurrence as the
release gate and the same whole stored payload's incoming StartRound readout. -/
theorem rawReleaseRecords_pending_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    (∃ r ∈ rawReleaseRecords rate rewards C_star C_h z, r.input.time = t ∧
      ∃ M, ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
        i ∈ ReferencePhysicalReleaseQuota.pendingAtStart M r.input.time r.input.state) ↔
      postRawKPendingSupport rate rewards C_star C_h t i z := by
  constructor
  · rintro ⟨r, hr, ht, M, hM, hi⟩
    obtain ⟨N, hN, hread⟩ := raw_member_pending_readout rate rewards C_star C_h z r hr
    have heq : N = M := Option.some.inj (hN.symm.trans hM)
    subst N
    obtain ⟨u, hut, he, _hg⟩ := (rawReleaseRecords_support_iff rate rewards C_star C_h z t).1 ⟨r, hr, ht⟩
    refine ⟨u, hut, he, ?_⟩
    have hp := hread u he
    rw [← ht, hp]
    exact hi
  · rintro ⟨u, hut, he, hi⟩
    have hg := pending_mem_gate rate rewards C_star C_h z u.val t i hi
    obtain ⟨r, hr, ht⟩ := (rawReleaseRecords_support_iff rate rewards C_star C_h z t).2 ⟨u, hut, he, hg⟩
    obtain ⟨M, hM, hread⟩ := raw_member_pending_readout rate rewards C_star C_h z r hr
    refine ⟨r, hr, ht, M, hM, ?_⟩
    rw [← hread u he, ht]
    exact hi

theorem postRawKOccurrence_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (u : Fin p.T) :
    (let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0;
      MeasurableSet[F (u.val + 2)]
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          postRawKOccurrence rate rewards C_star C_h u z}) := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  have hb := ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary_measurable
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) u.val
  have ha := ReferenceFirstReplacementCollectionPendingFoundation.phaseSummary_measurable
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
    (control0 := control0) (u.val + 1)
  let S : Set ((ℕ × Option (ℕ × ℕ)) × (ℕ × Option (ℕ × ℕ))) :=
    {v | v.1.1 = 3 ∧ v.2.1 = 4}
  have hm := ((hb.mono (F.mono (show u.val + 1 ≤ u.val + 2 by omega)) le_rfl).prodMk ha)
  exact (Set.to_countable S).measurableSet.preimage hm

theorem postRawKReleaseSupport_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    (let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0;
      MeasurableSet[F (t.val + 1)]
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          postRawKReleaseSupport rate rewards C_star C_h t z}) := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  have hpart : ∀ u : Fin p.T,
      MeasurableSet[F (t.val + 1)]
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          u.val < t.val ∧ postRawKOccurrence rate rewards C_star C_h u z ∧
            (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
              u.val t z).map Prod.fst = some true} := by
    intro u
    by_cases hu : u.val < t.val
    · have hevent' : MeasurableSet[F (t.val + 1)]
          {z : BootstrapPrivateRoundStreams.SourceInput p |
            postRawKOccurrence rate rewards C_star C_h u z} := by
        exact (F.mono (show u.val + 2 ≤ t.val + 1 by omega)) _
          (postRawKOccurrence_measurable rate rewards C_star C_h control0 u)
      let EntryValue := Bool × Option (Finset (Fin (p.m - 1)))
      let GateValues : Set (Option EntryValue) :=
        {e | e.map Prod.fst = some true}
      have hgateSet : MeasurableSet GateValues :=
        (Set.to_countable GateValues).measurableSet
      have hentry := ReferenceSourcePrefixHistoryFiltration.entry_measurable
        rate rewards C_star C_h control0 u.val t
      have hgate : MeasurableSet[F (t.val + 1)]
          {z : BootstrapPrivateRoundStreams.SourceInput p |
            (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
              u.val t z).map Prod.fst = some true} := by
        change MeasurableSet[F (t.val + 1)]
          ((ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h u.val t) ⁻¹'
            GateValues)
        exact hgateSet.preimage hentry
      simpa only [hu, true_and, Set.ofPred_and] using hevent'.inter hgate
    · simp only [hu, false_and, Set.ofPred_false]
      exact @MeasurableSet.empty (BootstrapPrivateRoundStreams.SourceInput p)
        (F (t.val + 1))
  have hset : {z : BootstrapPrivateRoundStreams.SourceInput p |
        postRawKReleaseSupport rate rewards C_star C_h t z} =
      ⋃ u : Fin p.T,
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          u.val < t.val ∧ postRawKOccurrence rate rewards C_star C_h u z ∧
            (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
              u.val t z).map Prod.fst = some true} := by
    ext z
    simp only [postRawKReleaseSupport, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset]
  exact MeasurableSet.iUnion hpart

theorem postRawKPendingSupport_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    (let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0;
      MeasurableSet[F (t.val + 1)]
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          postRawKPendingSupport rate rewards C_star C_h t i z}) := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  have hpart : ∀ u : Fin p.T,
      MeasurableSet[F (t.val + 1)]
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          u.val < t.val ∧ postRawKOccurrence rate rewards C_star C_h u z ∧
            i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h
              u.val t z} := by
    intro u
    by_cases hu : u.val < t.val
    · have hevent' : MeasurableSet[F (t.val + 1)]
          {z : BootstrapPrivateRoundStreams.SourceInput p |
            postRawKOccurrence rate rewards C_star C_h u z} := by
        exact (F.mono (show u.val + 2 ≤ t.val + 1 by omega)) _
          (postRawKOccurrence_measurable rate rewards C_star C_h control0 u)
      have hpending := ReferenceSourcePrefixHistoryFiltration.pending_measurable
        rate rewards C_star C_h control0 u.val t
      have hpending' : MeasurableSet[F (t.val + 1)]
          {z : BootstrapPrivateRoundStreams.SourceInput p |
            i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h
              u.val t z} := by
        exact (Set.to_countable {q : Finset (Fin (p.m - 1)) | i ∈ q}).measurableSet.preimage
          hpending
      simpa only [hu, true_and, Set.ofPred_and] using hevent'.inter hpending'
    · simp only [hu, false_and, Set.ofPred_false]
      exact @MeasurableSet.empty (BootstrapPrivateRoundStreams.SourceInput p)
        (F (t.val + 1))
  have hset : {z : BootstrapPrivateRoundStreams.SourceInput p |
        postRawKPendingSupport rate rewards C_star C_h t i z} =
      ⋃ u : Fin p.T,
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          u.val < t.val ∧ postRawKOccurrence rate rewards C_star C_h u z ∧
            i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h
              u.val t z} := by
    ext z
    simp only [postRawKPendingSupport, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset]
  exact MeasurableSet.iUnion hpart

/-- Adaptation of the actual raw release calendar in the original analytical
source field; no player's local-information identification is asserted. -/
theorem rawReleaseRecords_support_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z | ∃ r ∈ rawReleaseRecords rate rewards C_star C_h z, r.input.time = t} := by
  simp_rw [rawReleaseRecords_support_iff]
  exact postRawKReleaseSupport_measurable rate rewards C_star C_h control0 t

theorem rawReleaseRecords_pending_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z | ∃ r ∈ rawReleaseRecords rate rewards C_star C_h z, r.input.time = t ∧
        ∃ M, ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
          i ∈ ReferencePhysicalReleaseQuota.pendingAtStart M r.input.time r.input.state} := by
  simp_rw [rawReleaseRecords_pending_iff]
  exact postRawKPendingSupport_measurable rate rewards C_star C_h control0 t i

end Bandits.Support.ReferencePostReplacementCollectionReleaseSupport

end
