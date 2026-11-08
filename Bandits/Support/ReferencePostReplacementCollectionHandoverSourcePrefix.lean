/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionReleaseBoundary

/-!
# Original-source handover support after the raw replacement collection

The handover is taken from the actual later-installation choice history at the
endpoint immediately following the literal raw replacement collection. The
task support reads the selected pending set at the actual arm choice. A
separate diagnostic support intersects that literal support with the two
accepted strict-past gates at the same source date.

Sources: `05_binary_transport.tex:244-289`,
`06_interruptions.tex:246-299,431-490`, and
`appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferencePostReplacementCollectionHandoverSourcePrefix

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

/-- The calendar endpoint of the same initial-birth/cutoff scan used by rawK. -/
def rawKEndpointIndex
    (z : SourceInput p) : ℕ :=
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length

/-- The actual complete-suffix record at the rawK endpoint, absent at the
horizon and on every nonmatching rawK branch. -/
def rawKEndpointRecord?
    (z : SourceInput p) :
    Option (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :=
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
    rate rewards C_star C_h z
  R[rawKEndpointIndex rate rewards C_star C_h z + K.length]?

/-- The actual H segment beginning at the first later installation after the
literal raw replacement collection. Empty and horizon branches have no H. -/
def rawHRecords
    (z : SourceInput p) :
    List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) := by
  classical
  let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
    rate rewards C_star C_h z
  exact if K = [] then [] else
    match rawKEndpointRecord? rate rewards C_star C_h z with
    | none => []
    | some birth =>
        if ReferenceCollectionPhaseHistory.laterChosen birth.input then
          (birth :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z
            (rawKEndpointIndex rate rewards C_star C_h z + K.length + 1)).takeWhile
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
        else []

/-- The rawK endpoint has only two post-collection outcomes: the physical
horizon, or the actual later installation with empty incoming collection
pending. This is the accepted branch split, including its source witnesses. -/
theorem rawK_endpoint_after_cutoff
    (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ []) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
    let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z
    (R[c + K.length]? = none ∧ c + K.length = R.length) ∨
      ∃ b : Fin R.length, b.val = c + K.length ∧
        ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true ∧
        ∃ payload ledger saved,
          R[b.val].input.state.coordinator = .collection payload ledger saved ∧
          ledger.pending = ∅ := by
  classical
  intro R w v c K
  have hBoundary :=
    ReferencePostReplacementCollectionReleaseBoundary.raw_collection_next_installation_release_boundary
      rate rewards C_star C_h z
  rcases hBoundary with ⟨hKempty, _hNoLaunch, _hTerminal, hbranches⟩
  have hnotEarly : ¬ (R[v]? = none ∨ ∃ birth payload,
      R[v]? = some birth ∧
      ReferenceFirstReplacementCollectionPendingFoundation.birthPayload birth = some payload ∧
      (R[c]? = none ∨ ∃ cut, R[c]? = some cut ∧
        ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = false)) := by
    intro hearly
    exact hK (hKempty.mpr hearly)
  cases hv : R[v]? with
  | none => exact False.elim (hnotEarly (Or.inl hv))
  | some birth =>
    rw [hv] at hbranches
    dsimp only at hbranches
    obtain ⟨payload, hpayload, _hbound, hcutBranch⟩ := hbranches
    cases hc : R[c]? with
    | none =>
        exact False.elim (hnotEarly
          (Or.inr ⟨birth, payload, hv, hpayload, Or.inl hc⟩))
    | some cut =>
        by_cases hcut :
            ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = true
        · rw [hc] at hcutBranch
          simp [hcut] at hcutBranch
          rcases hcutBranch with hHorizon | hNext
          · have hnone : R[c + K.length]? = none := by
              rw [hHorizon]
              change R[R.length]? = none
              simp
            exact Or.inl ⟨hnone, hHorizon⟩
          · rcases hNext with ⟨b, hb, hlater, ledger, hstateSaved,
              hempty, _hrest⟩
            rcases hstateSaved with ⟨saved, hstate⟩
            exact Or.inr ⟨b, hb, hlater, payload, ledger, saved,
              hstate, hempty⟩
        · have hcutFalse :
              ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = false := by
            cases heq : ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut <;>
              simp_all
          exact False.elim (hnotEarly
            (Or.inr ⟨birth, payload, hv, hpayload, Or.inr ⟨cut, hc, hcutFalse⟩⟩))

/-- At an actual later-installation birth, the selected choice has all
followers pending. The fresh payload is obtained from that actual choice. -/
theorem laterInstallation_birthChoice_pending_univ
    (z : SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    ∃ selected : ReferenceActivePhysicalStep.Selection
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val].input,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].output.preparation.coordinator.selection =
          some selected ∧
      selected.view.pendingAtChoice = Finset.univ := by
  have hhistory :=
    ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
      rate rewards C_star C_h z b
  rw [ite_eq_left hlater] at hhistory
  rcases hhistory with ⟨rb, qb, beta, selected, hrest⟩
  exact ⟨selected, hrest.2.2.2.1, hrest.2.2.2.2.2.1⟩

/-- A present rawK endpoint is an actual later installation. This follows
from the accepted post-cutoff endpoint split, not from an H success premise. -/
theorem rawKEndpoint_laterChosen
    (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth) :
    ReferenceCollectionPhaseHistory.laterChosen birth.input = true := by
  rcases rawK_endpoint_after_cutoff rate rewards C_star C_h z hK with hHorizon | hBirth
  · have hnone : rawKEndpointRecord? rate rewards C_star C_h z = none := by
      simpa only [rawKEndpointRecord?, rawKEndpointIndex] using hHorizon.1
    rw [hnone] at hbirth
    cases hbirth
  · rcases hBirth with ⟨b, hb, hlater, payload, ledger, saved, _hstate, _hempty⟩
    have hlookup :
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val]? =
          some birth := by
      simpa only [rawKEndpointRecord?, rawKEndpointIndex, hb] using hbirth
    obtain ⟨_, hrecord⟩ := List.getElem?_eq_some_iff.mp hlookup
    rw [← hrecord]
    exact hlater

/-- The same endpoint split derives the birth's actual universal selected
pending set; it is not an assumed success condition. -/
theorem rawKEndpoint_birthPending_univ
    (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth) :
    ∃ selected : ReferenceActivePhysicalStep.Selection birth.input,
      birth.output.preparation.coordinator.selection = some selected ∧
      selected.view.pendingAtChoice = Finset.univ := by
  have hlookup :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[
        rawKEndpointIndex rate rewards C_star C_h z +
          (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
            rate rewards C_star C_h z).length]? = some birth := by
    simpa only [rawKEndpointRecord?] using hbirth
  obtain ⟨hb, hrecord⟩ := List.getElem?_eq_some_iff.mp hlookup
  let b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length :=
    ⟨rawKEndpointIndex rate rewards C_star C_h z +
      (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
        rate rewards C_star C_h z).length, hb⟩
  cases hrecord
  have hlater' := rawKEndpoint_laterChosen rate rewards C_star C_h z hK
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val] hbirth
  exact laterInstallation_birthChoice_pending_univ
    rate rewards C_star C_h z b hlater'

/-- The endpoint row is also the same record in the date-indexed incoming
observer. -/
theorem rawKEndpoint_actualRecord
    (z : SourceInput p)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      birth.input.time z = some birth := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let a := rawKEndpointIndex rate rewards C_star C_h z +
    (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z).length
  have hlookup : R[a]? = some birth := hbirth
  obtain ⟨ha, heq⟩ := List.getElem?_eq_some_iff.mp hlookup
  have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z ⟨a, ha⟩
  change R[a].input.time.val =
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + a at htime
  rw [heq] at htime
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ite_eq_left (show ReferenceCompletePhysicalHistory.physicalStart
    rate z rewards C_star C_h ≤ birth.input.time.val by omega)]
  rw [show birth.input.time.val - ReferenceCompletePhysicalHistory.physicalStart
    rate z rewards C_star C_h = a by omega]
  exact hlookup

/-- The endpoint's actual incoming code is the encoding of that same row's
whole incoming coordinator and follower state. -/
theorem rawKEndpoint_incoming
    (z : SourceInput p)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth) :
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h
      birth.input.time z =
      some (ReferenceActivePhysicalStepMeasurability.encodeState birth.input.state) := by
  unfold ReferenceSourcePrefixHistoryFiltration.incoming
  rw [rawKEndpoint_actualRecord rate rewards C_star C_h z birth hbirth]
  rfl

/-- Both the pointwise incoming code and its strict-source-prefix factor are
available at the rawK endpoint date. -/
theorem rawKEndpoint_incoming_factor
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceInput p)
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth) :
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h
        birth.input.time z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h
        birth.input.time
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0
          birth.input.time.val z) ∧
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h
        birth.input.time z =
      some (ReferenceActivePhysicalStepMeasurability.encodeState birth.input.state) := by
  exact ⟨ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 birth.input.time z,
    rawKEndpoint_incoming rate rewards C_star C_h z birth hbirth⟩

/-- The date-indexed actual incoming state is measurable in the same original
pre-round field used by the diagnostic support. -/
theorem handoverIncoming_measurable
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t) :=
  ReferenceSourcePrefixHistoryFiltration.incoming_measurable
    rate rewards C_star C_h control0 t

/-- With a present later birth at the rawK endpoint, the literal H list is
exactly the actual missing-at-choice prefix from `B/ChoiceHistory`. -/
theorem rawHRecords_eq_actualH_of_endpoint
    (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth) :
    rawHRecords rate rewards C_star C_h z =
      (birth :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z
          (rawKEndpointIndex rate rewards C_star C_h z +
            (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
              rate rewards C_star C_h z).length + 1)).takeWhile
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice := by
  classical
  have hlater := rawKEndpoint_laterChosen rate rewards C_star C_h z hK birth hbirth
  simp [rawHRecords, hK, hbirth, hlater]

/-- The accepted rawK boundary leaves either no incoming endpoint at the
horizon or the same actual later installation with empty collection pending.
The present branch exposes its actual H list from the full B/ChoiceHistory. -/
theorem rawH_endpoint_cases
    (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ []) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
    let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z
    (rawHRecords rate rewards C_star C_h z = [] ∧
      R[c + K.length]? = none ∧ c + K.length = R.length) ∨
    ∃ b : Fin R.length, b.val = c + K.length ∧
      ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true ∧
      ∃ payload ledger saved,
        R[b.val].input.state.coordinator = .collection payload ledger saved ∧
        ledger.pending = ∅ ∧
        rawHRecords rate rewards C_star C_h z =
          (R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z (b.val + 1)).takeWhile
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice := by
  classical
  intro R w v c K
  rcases rawK_endpoint_after_cutoff rate rewards C_star C_h z hK with hHorizon | hBirth
  · have hendpoint : rawKEndpointRecord? rate rewards C_star C_h z = none := by
      simpa only [rawKEndpointRecord?, rawKEndpointIndex] using hHorizon.1
    have hnil : rawHRecords rate rewards C_star C_h z = [] := by
      simp [rawHRecords, hK, hendpoint]
    exact Or.inl ⟨hnil, hHorizon.1, hHorizon.2⟩
  · rcases hBirth with ⟨b, hb, hlater, payload, ledger, saved, hstate, hempty⟩
    have hendpoint : rawKEndpointRecord? rate rewards C_star C_h z =
        some R[b.val] := by
      change R[c + K.length]? = some R[b.val]
      rw [← hb]
      exact List.getElem?_eq_getElem b.isLt
    have hH := rawHRecords_eq_actualH_of_endpoint rate rewards C_star C_h z
      hK R[b.val] hendpoint
    have hindex : rawKEndpointIndex rate rewards C_star C_h z + K.length = b.val := by
      rw [show rawKEndpointIndex rate rewards C_star C_h z = c by rfl]
      exact hb.symm
    rw [hindex] at hH
    exact Or.inr ⟨b, hb, hlater, payload, ledger, saved, hstate, hempty, hH⟩

private theorem takeWhile_take_prefix {α : Type*} (f : α → Bool)
    (xs : List α) (n : ℕ) :
    (xs.take n).takeWhile f = (xs.takeWhile f).take n := by
  induction xs generalizing n with
  | nil => cases n <;> simp
  | cons x xs ih =>
      cases n with
      | zero => simp
      | succ n =>
          cases hf : f x <;> simp [List.takeWhile, hf, ih]

/-- Restricting the actual H scan to any finite current prefix uses only that
prefix's missing-at-choice tests. The witness is not a future H length. -/
theorem rawHRecords_strictPrefix
    (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth)
    (n : ℕ) :
    (rawHRecords rate rewards C_star C_h z).take n =
      ((birth :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z
          (rawKEndpointIndex rate rewards C_star C_h z +
            (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
              rate rewards C_star C_h z).length + 1)).take n).takeWhile
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice := by
  rw [rawHRecords_eq_actualH_of_endpoint rate rewards C_star C_h z hK birth hbirth]
  exact (takeWhile_take_prefix
    ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice _ n).symm

/-- An empty raw replacement collection contributes no post-collection H. -/
theorem rawHRecords_eq_nil_of_rawK_eq_nil
    (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z = []) :
    rawHRecords rate rewards C_star C_h z = [] := by
  classical
  simp [rawHRecords, hK]

/-- A missing endpoint contributes no post-collection H. -/
theorem rawHRecords_eq_nil_of_endpoint_none
    (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (hendpoint : rawKEndpointRecord? rate rewards C_star C_h z = none) :
    rawHRecords rate rewards C_star C_h z = [] := by
  simp [rawHRecords, hK, hendpoint]

/-- A present non-birth endpoint does not start an H segment. -/
theorem rawHRecords_eq_nil_of_endpoint_not_later
    (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth)
    (hnotLater : ReferenceCollectionPhaseHistory.laterChosen birth.input = false) :
    rawHRecords rate rewards C_star C_h z = [] := by
  simp [rawHRecords, hK, hbirth, hnotLater]

/-- The accepted no-launch source branch has no raw replacement collection
and therefore contributes no post-collection H. -/
theorem rawHRecords_eq_nil_of_no_corrected_launch
    (z : SourceInput p)
    (hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) :
    rawHRecords rate rewards C_star C_h z = [] := by
  apply rawHRecords_eq_nil_of_rawK_eq_nil
  exact (ReferencePostReplacementCollectionReleaseBoundary.raw_collection_next_installation_release_boundary
    rate rewards C_star C_h z).2.1 hnone

/-- The accepted terminal-start source branch has no raw replacement
collection and therefore contributes no post-collection H. -/
theorem rawHRecords_eq_nil_of_terminal_start
    (z : SourceInput p)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h = p.T) :
    rawHRecords rate rewards C_star C_h z = [] := by
  apply rawHRecords_eq_nil_of_rawK_eq_nil
  exact (ReferencePostReplacementCollectionReleaseBoundary.raw_collection_next_installation_release_boundary
    rate rewards C_star C_h z).2.2.1 hterminal

/-- A follower is in the literal task support exactly when the actual choice
at a row of H records that follower in its selected pending set. -/
def rawHTaskSupport
    (t : Fin p.T) (i : Fin (p.m - 1))
    (z : SourceInput p) : Prop :=
  ∃ r ∈ rawHRecords rate rewards C_star C_h z,
    r.input.time = t ∧
      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
        r.output.preparation.coordinator.selection = some selected ∧
        i ∈ selected.view.pendingAtChoice

/-- The complete numerical observation before this source date uses the
accepted strict-date factor and retains absent numerical cells. -/
theorem handoverDatePrefix_factor
    (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) (z : SourceInput p) :
    ReferenceCompleteObservationPrefixInformation.datePrefix rate n
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z) =
      ReferenceCompleteObservationPrefixInformation.datePrefix rate n
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z)) :=
  ReferenceCompleteObservationPrefixInformation.datePrefix_factor
    rate rewards C_star C_h control0 n hn z

/-- The accepted date prefix is measurable in the original source-prefix
field, with the whole source arrays retained. -/
theorem handoverDatePrefix_measurable
    (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (n + 1)]
      (fun z : SourceInput p =>
        ReferenceCompleteObservationPrefixInformation.datePrefix rate n
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h z)) :=
  ReferenceCompleteObservationPrefixInformation.datePrefix_measurable
    rate rewards C_star C_h control0 n hn

/-- The original-source pre-round StartRound code factors through the
incoming date and is the same code used by actual choice. -/
theorem handoverPreRoundStart_factor
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p) :
    ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
        rate rewards C_star C_h t i z =
      ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
        rate rewards C_star C_h t i
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) :=
  ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_factor
    rate rewards C_star C_h control0 t i z

/-- The row-free StartRound code is predictable at the original pre-round
source field. -/
theorem handoverPreRoundStart_measurable
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      (ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
        rate rewards C_star C_h t i) :=
  ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_measurable
    rate rewards C_star C_h control0 t i

/-- On an actual ordinary incoming row, the accepted row-free StartRound
producer gives the same follower state at CHOICE. -/
theorem handoverPreRoundStart_actual_choice

    (t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (hc : r.input.state.followers i = .ordinary state memory) :
    ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
      (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary choice memory ∧
      ReferenceFirstReplacementCollectionPredictableStages.preRoundStart
        rate rewards C_star C_h t i z =
        .inr (.success (FollowerDownMeasurability.followerStateCode rate choice)
          (FollowerLifecycleMeasurability.localMemoryCode memory)) :=
  ReferenceFirstReplacementCollectionPredictableStages.preRoundStart_actual_choice
    rate rewards C_star C_h t i z r state memory hr hc

/-- The post-K birth is itself in H, with the actual choice's initial
universal pending set. -/
theorem rawH_birthTaskSupport
    (z : SourceInput p) (i : Fin (p.m - 1))
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth) :
    rawHTaskSupport rate rewards C_star C_h birth.input.time i z := by
  obtain ⟨selected, hs, hpending⟩ :=
    rawKEndpoint_birthPending_univ rate rewards C_star C_h z hK birth hbirth
  have hi : i ∈ selected.view.pendingAtChoice := by
    rw [hpending]
    exact Finset.mem_univ i
  have hmissing : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice birth = true := by
    simp only [ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice, hs]
    exact decide_eq_true ⟨i, hi⟩
  refine ⟨birth, ?_, rfl, selected, hs, hi⟩
  rw [rawHRecords_eq_actualH_of_endpoint rate rewards C_star C_h z hK birth hbirth]
  simp only [List.takeWhile_cons, hmissing, ↓reduceIte, List.mem_cons_self]

/-- On an actual complete-suffix collection input, empty incoming pending
is exactly the later-installation branch. The reverse direction uses the
accepted corrected and renewal producers on their respective sides of the
freeze boundary, including equality on the renewal side. -/
theorem actual_collection_laterChosen_iff_pending_empty
    (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.state.coordinator =
        .collection payload ledger saved) :
    ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input = true ↔ ledger.pending = ∅ := by
  constructor
  · intro hlater
    obtain ⟨other, otherLedger, otherSaved, hother, hempty⟩ :=
      ReferenceCollectionPhaseHistory.laterChosen_pending_empty _ hlater
    rw [hstate] at hother
    cases hother
    exact hempty
  · intro hempty
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]
    have hprepare := ReferenceFirstReplacementCollectionPendingFoundation.preparation_eq r
    by_cases hbefore : r.input.time.val + 1 < ledger.freezeAt
    · obtain ⟨u, _hu, core, started, hstart, instruction, hassignment,
        _htime, _hkind, _hsigma, _hcutoff, consistent, output, hlocal,
        _hlater, clockData, installed, arm, _hprior, _hresult, _hpending,
        _hinstall, _hdispatch, _hscore, _hqueue, _hprevious, _hbase,
        _henvelope, _hpayload, _hanchor, _hlawAnchor, _hcutoffRegisters,
        _hcurrentRegisters, _hsourceScore, _hinitialQueue, _hqueues,
        _hvector, selected, _hselection, _houtputSelection, _hselectedPayload,
        _hstarted, _hselectedCutoff, _harm, _hlive, hprepared, _hrest⟩ :=
        ReferenceCompleteEmptyCorrectedCoordinatorStep.complete_empty_corrected_coordinator_step
          rewards C_star C_h z k payload ledger saved hstate hempty hbefore
      unfold ReferenceCollectionPhaseHistory.laterChosen
      rw [← hprepare, hprepared]
    · have hafter : ledger.freezeAt ≤ r.input.time.val + 1 := Nat.le_of_not_gt hbefore
      obtain ⟨u, _hu, core, _hscore, started, hstart, instruction,
        hassignment, _htime, _hkind, output, hlocal, _hlater, _hsource,
        _hinitial, _hweight, _hanchor, _hqueues, _hdomains, _hbase,
        _hclock, mass, sampled, _hmass, _hsampled, _hvector, arm,
        hdispatch, hprepared, _hrest⟩ :=
        ReferenceCompleteEmptyRenewalCoordinatorStep.complete_empty_renewal_coordinator_step
          rate rewards C_star C_h z k payload ledger saved hstate hempty hafter
      unfold ReferenceCollectionPhaseHistory.laterChosen
      rw [hprepared, hdispatch]

private theorem actual_clock_domain
    (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
    ReferenceCoordinatorClockDomains.clockAt r.input.rows r.input.selected
      r.input.time.val r.input.state := by
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
    have hf := (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate z rewards C_star C_h hc).coordinatorFirst
    simp only [ReferenceCoordinatorClockDomains.clockAt,
      show initial.coordinator = .first from hf]
  have hrun := ReferenceRunClockPreservation.run_clockAt initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (by have := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h; omega)
    (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
      rate z rewards C_star C_h initial hl) hseed
  have h := hrun.2.2.2 _ (by rw [← hrecords]; exact List.getElem_mem k.isLt)
  simpa only [h.2.2.1, h.2.2.2.1] using h.1

private theorem live_startRound_pending
    (rate : ReferenceActivePhysicalStep.RateInput p) (t sigma : Fin p.T)
    (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1))) (out : CoordinatorPhaseClock.StartRoundResult p)
    (hsigma : clock.sigma = some sigma) (hu : clock.u = none)
    (h : CoordinatorPhaseClock.startRound p rate.eta.val t clock pending = .ok out)
    (hout : out.clock.u = none) : out.pending = pending := by
  have horiginal := h
  unfold CoordinatorPhaseClock.startRound at h
  split at h
  next hp =>
    split at h
    next hv =>
      split at h
      next ht =>
        cases hd : CoordinatorPhaseClock.detectCutoff clock t with
        | error failure => simp only [hd, reduceCtorEq] at h
        | ok decision =>
          cases decision with
          | cutoff old hsome =>
              obtain ⟨actual, heq, hclock, _⟩ := CoordinatorPhaseClock.startRound_cutoff_effect
                p rate.eta.val t old clock pending hp hv ht hsome hd
              have he : actual = out := Except.ok.inj (heq.symm.trans horiginal)
              rw [← he, hclock] at hout
              cases hout
          | noCutoff =>
              have hnot : ¬ CoordinatorPhaseClock.sourceStartTest clock.sigma clock.u t pending := by
                simp only [CoordinatorPhaseClock.sourceStartTest, hsigma, hu,
                  CoordinatorPhaseClock.cutoffAtOrBefore, reduceCtorEq, false_and, or_self, not_false_eq_true]
              simp only [hd, hnot, ↓reduceDIte, pure, Except.pure] at h
              cases h
              rfl
      next => cases h
    next => cases h
  next => cases h

/-- Actual continuing LIVE choices retain the SAME incoming pending labels
and payload. A cutoff is excluded by its literal pre-choice constructor, and
all three failure constructors are impossible by the complete producer. -/
theorem actual_live_continuing_pending
    (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.state.coordinator = .live registers owned base)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input = false) :
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val] = true ∧
      ∃ selected : ReferenceActivePhysicalStep.Selection
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val].input,
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val].output.preparation.coordinator.selection =
            some selected ∧
        selected.view.payload = registers.payload ∧
        selected.view.pendingAtChoice = registers.pendingAtChoice := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  have h := ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
    rate rewards C_star C_h z k registers owned base hstate
  obtain ⟨hprep, hbranch⟩ := h
  have hactual := ReferenceFirstReplacementCollectionPendingFoundation.preparation_eq r
  have hclock := actual_clock_domain rate rewards C_star C_h z k
  simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hclock
  cases hd : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput r.input registers owned base) with
  | continuingChosen dispatched hstart continuation arm =>
      rw [hd] at hbranch
      obtain ⟨_hframe, hu, _hvalid, _hgrid, _harm,
        selected, hs, hpayload, hpending, _hcutoff, _hstarted, _hrest⟩ := hbranch
      have hp := live_startRound_pending rate r.input.time registers.payload.sigma
        registers.priorClock registers.pendingAtChoice dispatched.startResult hclock.2.2.1
        hclock.2.2.2.1 (by simpa only [ReferenceActivePhysicalStep.liveInput,
          ReferenceActivePhysicalStep.liveRegistersAt, CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq]
          using hstart) hu
      have hprepared : r.output.preparation.coordinator =
          .live registers owned base (.continuingChosen dispatched hstart continuation arm) := by
        rw [hactual, hprep, hd]
      refine ⟨?_, selected, ?_, hpayload, hpending.trans hp⟩
      · change ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest r = true
        simp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest, hprepared]
      · rw [hactual]
        exact hs
  | cutoffChosen =>
      unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
      rw [hprep, hd] at hcut
      cases hcut
  | clockFailure => rw [hd] at hbranch; exact hbranch.elim
  | initializerFailure => rw [hd] at hbranch; exact hbranch.elim
  | localFailure => rw [hd] at hbranch; exact hbranch.elim

/-- A countable incoming observation, retaining LIVE pending labels and the
empty-collection birth test. It reads no freshly sampled installation payload. -/
def incomingHandoverData {rate : ReferenceActivePhysicalStep.RateInput p} :
    ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate →
      Bool × Option (Finset (Fin (p.m - 1)))
  | .inr (.inl (_, live)) => (false, some live.pending)
  | .inr (.inr (.inl (_, ledger, _))) => (decide (ledger.pending = ∅), none)
  | _ => (false, none)

private theorem measurable_incomingHandoverData
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    Measurable (incomingHandoverData (rate := rate)) := by
  exact measurable_const.sumElim
    (((measurable_of_countable (fun live : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
        (false, some live.pending))).comp measurable_snd).sumElim
      (((measurable_of_countable (fun q : ReferenceActivePhysicalStep.Ledger rate ×
          Option (Fin p.T × Bool) => (decide (q.1.pending = ∅), none))).comp
        measurable_snd).sumElim measurable_const))

/-- The original-source incoming handover query. Absence stays distinct from
a present empty pending set and a present non-birth collection. -/
def handoverIncomingData
    (t : Fin p.T) (z : SourceInput p) :
    Option (Bool × Option (Finset (Fin (p.m - 1)))) :=
  (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z).map
    (fun code => incomingHandoverData code.1)

/-- The complete incoming handover query factors at the strict pre-round
source prefix, independently of the current sampled arm or new payload. -/
theorem handoverIncomingData_factor
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    handoverIncomingData rate rewards C_star C_h t z =
      handoverIncomingData rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
  unfold handoverIncomingData
  rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
    rate rewards C_star C_h control0 t z]

/-- Both incoming birth readiness and the actual stored LIVE pending labels
are measurable at the same pre-round source field. -/
theorem handoverIncomingData_measurable
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] (handoverIncomingData rate rewards C_star C_h t) := by
  have h := (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim none
    (fun code : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
      some (incomingHandoverData code.1))
    ((measurable_of_countable (some : Bool × Option (Finset (Fin (p.m - 1))) →
      Option (Bool × Option (Finset (Fin (p.m - 1)))))).comp
        ((measurable_incomingHandoverData rate).comp measurable_fst))).comp
      (ReferenceSourcePrefixHistoryFiltration.incoming_measurable
        rate rewards C_star C_h control0 t)
  convert h using 1
  funext z
  unfold handoverIncomingData
  dsimp only [Function.comp_apply]
  cases ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z <;> rfl

/-- At the same actual collection row the incoming query recognizes birth
without observing the newly sampled payload or assuming later-choice success. -/
theorem handoverIncomingData_collection_birth
    (z : SourceInput p) (t : Fin p.T)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
      some (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val])
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.state.coordinator =
        .collection payload ledger saved) :
    handoverIncomingData rate rewards C_star C_h t z = some (true, none) ↔
      ReferenceCollectionPhaseHistory.laterChosen
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val].input = true := by
  simp only [handoverIncomingData, ReferenceSourcePrefixHistoryFiltration.incoming,
    hr, Option.map_some, ReferenceActivePhysicalStepMeasurability.encodeState,
    hstate, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
    incomingHandoverData, Option.some.injEq, Prod.mk.injEq, and_true, decide_eq_true_eq]
  exact (actual_collection_laterChosen_iff_pending_empty
    rate rewards C_star C_h z k payload ledger saved hstate).symm

/-- Pending membership anywhere in the same actual birth/continuing segment
already forces membership in H. Empty pending cannot re-enter before cutoff;
the accepted release-suffix theorem derives this from actual updates. -/
theorem rawHTaskSupport_iff_actual_segment
    (z : SourceInput p)
    (hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hbirth : rawKEndpointRecord? rate rewards C_star C_h z = some birth)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    rawHTaskSupport rate rewards C_star C_h t i z ↔
      ∃ r ∈ birth :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z
          (rawKEndpointIndex rate rewards C_star C_h z +
            (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
              rate rewards C_star C_h z).length + 1),
        r.input.time = t ∧
        ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
          r.output.preparation.coordinator.selection = some selected ∧
          i ∈ selected.view.pendingAtChoice := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let a := rawKEndpointIndex rate rewards C_star C_h z +
    (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z).length
  have hlookup : R[a]? = some birth := hbirth
  obtain ⟨ha, heq⟩ := List.getElem?_eq_some_iff.mp hlookup
  let b : Fin R.length := ⟨a, ha⟩
  have hlater := rawKEndpoint_laterChosen rate rewards C_star C_h z hK birth hbirth
  have hbLater : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true := by
    rw [heq]
    exact hlater
  have hfalse :=
    ReferencePostReplacementCollectionReleaseBoundary.actual_later_installation_release_suffix_test_false
      rate rewards C_star C_h z b
  rw [ite_eq_left hbLater] at hfalse
  let V := birth :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (a + 1)
  have hfalse' : ∀ r ∈ V.dropWhile
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice,
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = false := by
    change ∀ r ∈ (R[a] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (a + 1)).dropWhile
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice,
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = false at hfalse
    rw [heq] at hfalse
    exact hfalse
  rw [rawHTaskSupport, rawHRecords_eq_actualH_of_endpoint
    rate rewards C_star C_h z hK birth hbirth]
  constructor
  · rintro ⟨r, hr, htime, selected, hs, hi⟩
    exact ⟨r, (List.takeWhile_prefix _).sublist.subset hr, htime, selected, hs, hi⟩
  · rintro ⟨r, hr, htime, selected, hs, hi⟩
    have hmissing : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = true := by
      simp only [ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice, hs]
      exact decide_eq_true ⟨i, hi⟩
    have hpartition := List.takeWhile_append_dropWhile
      (p := ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice) (l := V)
    change r ∈ V at hr
    rw [← hpartition, List.mem_append] at hr
    rcases hr with hH | hRel
    · exact ⟨r, hH, htime, selected, hs, hi⟩
    · have hnot := hfalse' r hRel
      rw [hmissing] at hnot
      cases hnot

/-- Stages of the original first-cutoff/replacement-cutoff/handover scan.
This analytical state records completed operations only. -/
inductive HandoverPhase where
  | firstLive | firstCollection | replacementLive | replacementCollection | handover | closed
  deriving DecidableEq, Countable

instance : MeasurableSpace HandoverPhase := ⊤
instance : DiscreteMeasurableSpace HandoverPhase := ⟨fun _ => trivial⟩

/-- Advance on the literal cutoff, birth and continuing-choice tags. -/
def handoverAdvance : HandoverPhase → Bool × Bool × Bool → HandoverPhase
  | .firstLive, q => if q.1 then .firstCollection else .firstLive
  | .firstCollection, q => if q.2.1 then .replacementLive else .firstCollection
  | .replacementLive, q => if q.2.2 then .replacementLive
      else if q.1 then .replacementCollection else .closed
  | .replacementCollection, q => if q.2.1 then .handover else .replacementCollection
  | .handover, q => if q.2.2 then .handover else .closed
  | .closed, _ => .closed

/-- Only the post-collection birth and its continuing LIVE records are emitted. -/
def handoverEmit : HandoverPhase → Bool × Bool × Bool → Bool
  | .replacementCollection, q => q.2.1
  | .handover, q => q.2.2
  | _, _ => false

def handoverRecordTags {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Bool × Bool × Bool :=
  (ReferenceFirstReplacementCollectionPendingFoundation.isCutoff r,
    ReferenceCollectionPhaseHistory.laterChosen r.input,
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r)

private theorem continuingTest_eq {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest r =
      ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r := by
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
  cases r.output.preparation.coordinator with
  | live _ _ _ outcome => cases outcome <;> rfl
  | first _ => rfl
  | collection _ _ _ _ _ => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

/-- The same raw post-collection birth/continuing segment, obtained by a
forward scan. Missing confirmations are read separately at actual CHOICE. -/
def scannedHSegment {rate : ReferenceActivePhysicalStep.RateInput p} :
    HandoverPhase → List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) →
      List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
  | _, [] => []
  | phase, r :: rest =>
      let tail := scannedHSegment (handoverAdvance phase (handoverRecordTags r)) rest
      if handoverEmit phase (handoverRecordTags r) then r :: tail else tail

private theorem scannedHSegment_subset {rate : ReferenceActivePhysicalStep.RateInput p}
    (phase : HandoverPhase)
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    scannedHSegment phase R ⊆ R := by
  induction R generalizing phase with
  | nil => simp only [scannedHSegment, List.Subset.refl]
  | cons r R ih =>
      intro x hx
      simp only [scannedHSegment] at hx
      split at hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem r (ih _ hx)
      · exact List.mem_cons_of_mem r (ih _ hx)

private theorem scannedHSegment_closed {rate : ReferenceActivePhysicalStep.RateInput p}
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    scannedHSegment .closed R = [] := by
  induction R with
  | nil => rfl
  | cons r R ih => simpa only [scannedHSegment, handoverAdvance, handoverEmit, Bool.false_eq_true, ↓reduceIte] using ih

private theorem scannedHSegment_handover {rate : ReferenceActivePhysicalStep.RateInput p}
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    scannedHSegment .handover R = R.takeWhile
      ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
  induction R with
  | nil => rfl
  | cons r R ih =>
      cases ht : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r <;>
        simp only [scannedHSegment, handoverRecordTags, handoverAdvance, handoverEmit, ht,
          Bool.false_eq_true, ↓reduceIte, List.takeWhile_cons, scannedHSegment_closed, ih]

private theorem scannedHSegment_dropWhile {rate : ReferenceActivePhysicalStep.RateInput p}
    (phase : HandoverPhase)
    (test : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) → Bool)
    (h : ∀ r, test r = true → handoverAdvance phase (handoverRecordTags r) = phase ∧
      handoverEmit phase (handoverRecordTags r) = false)
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    scannedHSegment phase R = scannedHSegment phase (R.dropWhile test) := by
  induction R with
  | nil => rfl
  | cons r R ih =>
      cases ht : test r with
      | false => simp only [List.dropWhile_cons, ht, Bool.false_eq_true, ↓reduceIte]
      | true =>
          obtain ⟨hn, he⟩ := h r ht
          simp only [List.dropWhile_cons, ht, ↓reduceIte, scannedHSegment, hn, he,
            Bool.false_eq_true, ih]

private theorem drop_takeWhile {α : Type*} (R : List α) (test : α → Bool) :
    R.drop (R.takeWhile test).length = R.dropWhile test := by
  have h := List.takeWhile_append_dropWhile (p := test) (l := R)
  calc
    R.drop (R.takeWhile test).length =
        (R.takeWhile test ++ R.dropWhile test).drop (R.takeWhile test).length :=
      congrArg (fun A => A.drop (R.takeWhile test).length) h.symm
    _ = R.dropWhile test := List.drop_left

private theorem drop_of_lookup {α : Type*} (R : List α) (j : ℕ) (r : α)
    (hr : R[j]? = some r) : R.drop j = r :: R.drop (j + 1) := by
  obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp hr
  simpa only [he] using List.drop_eq_getElem_cons hj

private theorem scannedHSegment_seek {rate : ReferenceActivePhysicalStep.RateInput p}
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
    scannedHSegment .firstLive R =
      match R[v]? with
      | none => []
      | some _ => match R[c]? with
        | none => []
        | some cut => if ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut then
            scannedHSegment .replacementCollection (R.drop (c + 1)) else [] := by
  intro w v c
  have hfirst := scannedHSegment_dropWhile .firstLive
    (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input)
    (fun r hr => by
      have hc : ReferenceFirstReplacementCollectionPendingFoundation.isCutoff r = false := by
        rw [ReferenceFirstReplacementCollectionPendingFoundation.isCutoff_eq]
        simpa only [Bool.not_eq_true'] using hr
      simp [handoverAdvance, handoverEmit, handoverRecordTags, hc]) R
  have hseek (A : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :=
    scannedHSegment_dropWhile (rate := rate) .firstCollection
    (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
    (fun r hr => by
      have hb : ReferenceCollectionPhaseHistory.laterChosen r.input = false :=
        by simpa only [Bool.not_eq_true'] using hr
      simp [handoverAdvance, handoverEmit, handoverRecordTags, hb]) A
  have hlive (A : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) :=
    scannedHSegment_dropWhile (rate := rate) .replacementLive
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
    (fun r hr => by simp [handoverAdvance, handoverEmit, handoverRecordTags, hr]) A
  rw [← drop_takeWhile] at hfirst
  change scannedHSegment .firstLive R = scannedHSegment .firstLive (R.drop w) at hfirst
  rw [hfirst]
  cases hfront : R.drop w with
  | nil =>
      have hlen : R.length ≤ w := List.drop_eq_nil_iff.mp hfront
      have hv : R[v]? = none := List.getElem?_eq_none_iff.mpr (by dsimp only [v]; omega)
      rw [hv]
      rfl
  | cons cut tail =>
      have hcut : ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = true := by
        have hdrop : R.dropWhile (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input) =
            cut :: tail := by rw [← drop_takeWhile]; exact hfront
        have hnot := List.head?_dropWhile_not
          (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input) R
        rw [hdrop] at hnot
        rw [ReferenceFirstReplacementCollectionPendingFoundation.isCutoff_eq]
        simpa only [List.head?_cons, Bool.not_eq_false'] using hnot
      have htail : R.drop (w + 1) = tail := by
        rw [← List.drop_drop, hfront]
        rfl
      have hC : ReferenceCollectionPhaseHistory.collectionWindow R w =
          cut :: tail.takeWhile (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) := by
        simp only [ReferenceCollectionPhaseHistory.collectionWindow, hfront, htail, List.take_one,
          List.head?_cons, Option.toList_some, List.cons_append, List.nil_append]
      have hV : R.drop v = tail.dropWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) := by
        dsimp only [v]
        rw [hC, List.length_cons, show w + ((tail.takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length + 1) =
            (w + 1) + (tail.takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length by omega, ← List.drop_drop, htail, drop_takeWhile]
      simp only [scannedHSegment, handoverRecordTags, handoverAdvance, handoverEmit, hcut, ↓reduceIte]
      rw [hseek, ← hV]
      cases hv : R[v]? with
      | none =>
          have hn : R.drop v = [] := List.drop_eq_nil_iff.mpr (List.getElem?_eq_none_iff.mp hv)
          rw [hn]
          rfl
      | some birth =>
          have hdrop : R.drop v = birth :: R.drop (v + 1) :=
            drop_of_lookup R v birth hv
          have hborn : ReferenceCollectionPhaseHistory.laterChosen birth.input = true := by
            have hb := (ReferenceFirstReplacementCollectionGlobalDecoderCharge.birth_endpoint rate R).2.2 birth hv
            rwa [ReferenceFirstReplacementCollectionPendingFoundation.birthPayload_isSome] at hb
          rw [hdrop]
          simp only [scannedHSegment, handoverRecordTags, handoverAdvance, handoverEmit, hborn, ↓reduceIte]
          rw [hlive, ← drop_takeWhile]
          have hdropC : (R.drop (v + 1)).drop
              ((R.drop (v + 1)).takeWhile ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen).length =
                R.drop c := by
            rw [List.drop_drop]
            rfl
          rw [hdropC]
          cases hc : R[c]? with
          | none =>
              rw [List.drop_eq_nil_iff.mpr (List.getElem?_eq_none_iff.mp hc)]
              rfl
          | some boundary =>
              rw [drop_of_lookup R c boundary hc]
              have hn : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen boundary = false := by
                have hd := List.head?_dropWhile_not
                  ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen (R.drop (v + 1))
                rw [← drop_takeWhile, hdropC, drop_of_lookup R c boundary hc] at hd
                exact hd
              cases hcut : ReferenceFirstReplacementCollectionPendingFoundation.isCutoff boundary <;>
                simp only [scannedHSegment, handoverRecordTags, handoverAdvance, handoverEmit, hn, hcut,
                  Bool.false_eq_true, ↓reduceIte, scannedHSegment_closed]

private theorem scannedHSegment_raw (z : SourceInput p) :
    scannedHSegment .firstLive
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) =
      if ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z = [] then []
      else match rawKEndpointRecord? rate rewards C_star C_h z with
        | none => []
        | some birth => birth :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z (rawKEndpointIndex rate rewards C_star C_h z +
              (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
                rate rewards C_star C_h z).length + 1) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
  let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z
  have hk := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK_eq rate rewards C_star C_h z
  have hs := scannedHSegment_seek (rate := rate) R
  change K = (match R[v]? with
    | none => []
    | some birth => if (ReferenceFirstReplacementCollectionPendingFoundation.birthPayload birth).isSome then
        match R[c]? with
        | none => []
        | some cut => if ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut then
            cut :: (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) else []
      else []) at hk
  change scannedHSegment .firstLive R = (match R[v]? with
    | none => []
    | some _ => match R[c]? with
      | none => []
      | some cut => if ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut then
          scannedHSegment .replacementCollection (R.drop (c + 1)) else []) at hs
  change scannedHSegment .firstLive R = if K = [] then [] else
    match R[c + K.length]? with
    | none => []
    | some birth => birth :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (c + K.length + 1)
  cases hv : R[v]? with
  | none =>
      simp only [hv] at hk hs
      simp only [show K = [] from hk, ↓reduceIte]
      exact hs
  | some oldBirth =>
      have hb := (ReferenceFirstReplacementCollectionGlobalDecoderCharge.birth_endpoint rate R).2.2 oldBirth hv
      simp only [hv, hb, ↓reduceIte] at hk hs
      cases hc : R[c]? with
      | none =>
          simp only [hc] at hk hs
          simp only [show K = [] from hk, ↓reduceIte]
          exact hs
      | some cut =>
          cases hcut : ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut with
          | false =>
              simp only [hc, hcut, Bool.false_eq_true, ↓reduceIte] at hk hs
              simp only [show K = [] from hk, ↓reduceIte]
              exact hs
          | true =>
              simp only [hc, hcut, ↓reduceIte] at hk hs
              have hK : K ≠ [] := by rw [hk]; exact List.cons_ne_nil _ _
              rw [ite_eq_right hK]
              rw [hs]
              have hseek := scannedHSegment_dropWhile .replacementCollection
                (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
                (fun r hr => by
                  have hb : ReferenceCollectionPhaseHistory.laterChosen r.input = false :=
                    by simpa only [Bool.not_eq_true'] using hr
                  simp [handoverAdvance, handoverEmit, handoverRecordTags, hb]) (R.drop (c + 1))
              let a := c + K.length
              have hlength : K.length = ((R.drop (c + 1)).takeWhile
                  (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length + 1 := by
                simpa only [List.length_cons] using congrArg List.length hk
              have hindex : a = c + 1 + ((R.drop (c + 1)).takeWhile
                  (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length := by
                dsimp only [a]
                rw [hlength]
                omega
              have hd : R.drop a = (R.drop (c + 1)).dropWhile
                  (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) := by
                rw [← drop_takeWhile, List.drop_drop, ← hindex]
              rw [hseek, ← hd]
              change scannedHSegment .replacementCollection (R.drop a) =
                match R[a]? with
                | none => []
                | some birth => birth ::
                    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                      rate rewards C_star C_h z (a + 1)
              cases ha : R[a]? with
              | none =>
                  rw [List.drop_eq_nil_iff.mpr (List.getElem?_eq_none_iff.mp ha)]
                  rfl
              | some birth =>
                  have hborn : ReferenceCollectionPhaseHistory.laterChosen birth.input = true := by
                    have hhead := List.head?_dropWhile_not
                      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input) (R.drop (c + 1))
                    rw [← hd, drop_of_lookup R a birth ha] at hhead
                    simpa only [List.head?_cons, Bool.not_eq_false'] using hhead
                  rw [drop_of_lookup R a birth ha]
                  simp only [scannedHSegment, handoverRecordTags, handoverAdvance, handoverEmit,
                    hborn, ↓reduceIte, scannedHSegment_handover,
                    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix]
                  rw [show ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest =
                    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen from
                      funext continuingTest_eq]

/-- The whole raw support is an actual phase-scan support. The missing-set
prefix cannot discard a later nonempty selected pending set in this segment. -/
theorem rawHTaskSupport_iff_scanned (z : SourceInput p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    rawHTaskSupport rate rewards C_star C_h t i z ↔
      ∃ r ∈ scannedHSegment .firstLive
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h),
        r.input.time = t ∧ ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
          r.output.preparation.coordinator.selection = some selected ∧
          i ∈ selected.view.pendingAtChoice := by
  rw [scannedHSegment_raw]
  by_cases hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z = []
  · simp only [hK, ↓reduceIte, rawHTaskSupport,
      rawHRecords_eq_nil_of_rawK_eq_nil rate rewards C_star C_h z hK,
      List.not_mem_nil, false_and, exists_false]
  · rw [ite_eq_right hK]
    cases hb : rawKEndpointRecord? rate rewards C_star C_h z with
    | none =>
        simp only [rawHTaskSupport, rawHRecords_eq_nil_of_endpoint_none
          rate rewards C_star C_h z hK hb, List.not_mem_nil, false_and, exists_false]
    | some birth =>
        exact rawHTaskSupport_iff_actual_segment rate rewards C_star C_h z hK birth hb t i

private theorem scannedHSegment_mem_index {rate : ReferenceActivePhysicalStep.RateInput p}
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hR : R.Nodup) (phase : HandoverPhase) (k : ℕ) (hk : k < R.length) :
    R[k] ∈ scannedHSegment phase R ↔
      handoverEmit ((R.take k).foldl
        (fun q r => handoverAdvance q (handoverRecordTags r)) phase) (handoverRecordTags R[k]) = true := by
  induction R generalizing phase k with
  | nil => simp at hk
  | cons r R ih =>
      obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hR
      cases k with
      | zero =>
          have hn : r ∉ scannedHSegment (handoverAdvance phase (handoverRecordTags r)) R :=
            fun h => hnot (scannedHSegment_subset _ _ h)
          cases he : handoverEmit phase (handoverRecordTags r) <;>
            simp only [scannedHSegment, he, Bool.false_eq_true, ↓reduceIte,
              List.getElem_cons_zero, List.take_zero, List.foldl_nil, List.mem_cons,
              true_or, hn, iff_self]
      | succ k =>
          have hk' : k < R.length := by simp only [List.length_cons] at hk; omega
          have hne : R[k] ≠ r := fun h => hnot (h ▸ List.getElem_mem hk')
          cases he : handoverEmit phase (handoverRecordTags r) <;>
            simp only [scannedHSegment, he, Bool.false_eq_true, ↓reduceIte,
              List.getElem_cons_succ, List.mem_cons, hne, false_or, List.take_succ_cons,
              List.foldl_cons, ih htail _ k hk']

/-- Exact current support from the completed strict prefix and this actual
choice. The scan reads no future H length. -/
theorem rawHTaskSupport_iff_strictPrefix_choice (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (i : Fin (p.m - 1)) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    rawHTaskSupport rate rewards C_star C_h R[k.val].input.time i z ↔
      handoverEmit ((R.take k.val).foldl
        (fun q r => handoverAdvance q (handoverRecordTags r)) .firstLive)
        (handoverRecordTags R[k.val]) = true ∧
      ∃ selected : ReferenceActivePhysicalStep.Selection R[k.val].input,
        R[k.val].output.preparation.coordinator.selection = some selected ∧
        i ∈ selected.view.pendingAtChoice := by
  intro R
  have hnodup : R.Nodup := by
    apply List.Nodup.of_map (fun r => r.input.time.val)
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values]
    exact List.nodup_range'
  rw [rawHTaskSupport_iff_scanned]
  have htime : ∀ r ∈ R, r.input.time = R[k.val].input.time → r = R[k.val] := by
    intro r hr ht
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
    have h1 := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z ⟨j, hj⟩
    have h2 := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z k
    change R[j].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + j at h1
    change R[k.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val at h2
    have heq : j = k.val := by have := congrArg Fin.val ht; omega
    subst j
    rfl
  constructor
  · rintro ⟨r, hr, ht, selected, hs, hi⟩
    have heq := htime r (scannedHSegment_subset _ _ hr) ht
    subst r
    exact ⟨(scannedHSegment_mem_index R hnodup .firstLive k.val k.isLt).mp hr, selected, hs, hi⟩
  · rintro ⟨hemits, selected, hs, hi⟩
    exact ⟨R[k.val], (scannedHSegment_mem_index R hnodup .firstLive k.val k.isLt).mpr hemits,
      rfl, selected, hs, hi⟩

/-- The actual birth branch contributes every follower, exactly when its
incoming collection is ready. No new payload is fixed by this test. -/
theorem actual_birth_task_iff_incoming_empty (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (i : Fin (p.m - 1)) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
    (ReferenceCollectionPhaseHistory.laterChosen r.input = true ∧
      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
        r.output.preparation.coordinator.selection = some selected ∧
        i ∈ selected.view.pendingAtChoice) ↔
      ∃ payload ledger saved,
        r.input.state.coordinator = .collection payload ledger saved ∧ ledger.pending = ∅ := by
  intro r
  constructor
  · rintro ⟨hlater, _⟩
    exact ReferenceCollectionPhaseHistory.laterChosen_pending_empty r.input hlater
  · rintro ⟨payload, ledger, saved, hstate, hempty⟩
    have hlater := (actual_collection_laterChosen_iff_pending_empty
      rate rewards C_star C_h z k payload ledger saved hstate).mpr hempty
    obtain ⟨selected, hs, hpending⟩ :=
      laterInstallation_birthChoice_pending_univ rate rewards C_star C_h z k hlater
    exact ⟨hlater, selected, hs, by rw [hpending]; exact Finset.mem_univ i⟩

/-- On an actual LIVE input, the task test is precisely incoming pending
membership with the next cutoff excluded BEFORE choice. -/
theorem actual_live_task_iff_incoming_pending (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.state.coordinator = .live registers owned base)
    (i : Fin (p.m - 1)) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
    (ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = true ∧
      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
        r.output.preparation.coordinator.selection = some selected ∧
        i ∈ selected.view.pendingAtChoice) ↔
      ReferenceCollectionPhaseHistory.cutoffChosen r.input = false ∧
        i ∈ registers.pendingAtChoice := by
  intro r
  constructor
  · rintro ⟨hcontinue, selected, hs, hi⟩
    have hcut : ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
      unfold ReferenceCollectionPhaseHistory.cutoffChosen
      rw [← ReferenceFirstReplacementCollectionPendingFoundation.preparation_eq r]
      unfold ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen at hcontinue
      cases hc : r.output.preparation.coordinator with
      | live _ _ _ outcome => cases outcome <;> simp_all
      | first _ => rfl
      | collection _ _ _ _ _ => rfl
      | invalidCollectionCutoff => rfl
      | dagger => rfl
    obtain ⟨_, actual, ha, _hpayload, hpending⟩ :=
      actual_live_continuing_pending rate rewards C_star C_h z k registers owned base hstate hcut
    have heq := Option.some.inj (hs.symm.trans ha)
    subst selected
    exact ⟨hcut, by rwa [← hpending]⟩
  · rintro ⟨hcut, hi⟩
    obtain ⟨hc, selected, hs, _hpayload, hpending⟩ :=
      actual_live_continuing_pending rate rewards C_star C_h z k registers owned base hstate hcut
    exact ⟨(continuingTest_eq _).symm.trans hc, selected, hs, by rwa [hpending]⟩

/-- Literal stopped H support, using the global decoder strict-past safety
and the original launch-based strict-past queue word. -/
def literalStoppedHTaskSupport
    (t : Fin p.T) (i : Fin (p.m - 1))
    (z : SourceInput p) : Prop :=
  rawHTaskSupport rate rewards C_star C_h t i z ∧
    ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
      rate rewards C_star C_h z t.val ∧
    ∃ N,
      ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
        rate rewards C_star C_h t z = some N ∧
      ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N

/-- The same-date diagnostic envelope for an actual H task. -/
def diagnosticHTaskSupport
    (t : Fin p.T) (i : Fin (p.m - 1)) : Set (SourceInput p) :=
  {z | rawHTaskSupport rate rewards C_star C_h t i z ∧
    ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt
      rate rewards C_star C_h z t ∧
    z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t}

/-- The two same-date diagnostic gates have the accepted source-prefix
adaptations; raw H support remains a separate factorization obligation. -/
theorem diagnosticGates_measurable
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      {z : SourceInput p |
        ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt
            rate rewards C_star C_h z t ∧
          z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t} := by
  exact (ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt_measurable_preRound
      rate rewards C_star C_h control0 t).inter
    (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
      rate rewards C_star C_h control0 t)

private theorem literalQueueSafe_iff_run_not_overflow
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (N : List (RecordedQueueRun.RoundInput p.K)) :
    ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N ↔
      (RecordedQueueRun.run
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) N).overflow = false := by
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have hsafeIff :=
    _root_.Bandits.Support.ReferenceFirstReplacementCollectionInclusiveStoppedCharge.literalQueueSafe_take_iff_before_first
      rate N N.length (by rfl)
  rw [List.take_length] at hsafeIff
  have hover := UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
    q N N.length (by rfl)
  rw [List.take_length] at hover
  change ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N ↔
    N.length < UnstoppedRecordedQueueComparison.firstOverflowPrefix q N at hsafeIff
  constructor
  · intro hsafeN
    cases hrun : (RecordedQueueRun.run q N).overflow with
    | false => rfl
    | true =>
        have hle := hover.mp hrun
        have hlt := hsafeIff.mp hsafeN
        omega
  · intro hfalse
    apply hsafeIff.mpr
    have hnot : ¬ UnstoppedRecordedQueueComparison.firstOverflowPrefix q N ≤ N.length := by
      intro hle
      have htrue := hover.mpr hle
      rw [hfalse] at htrue
      cases htrue
    exact Nat.lt_of_not_ge hnot

private theorem retainedGate_iff_literalQueueSafe
    (t : Fin p.T) (z : SourceInput p)
    (N : List (RecordedQueueRun.RoundInput p.K))
    (hN : ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
      rate rewards C_star C_h t z = some N) :
    z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t ↔
      ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N := by
  have hPast : ReferenceFirstCollectionCurrentRetainedGate.pastCells?
      rate rewards C_star C_h t z = some N := by
    rw [← _root_.Bandits.Support.ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs_eq_pastCells?
      rate rewards C_star C_h t z]
    exact hN
  unfold ReferenceFirstCollectionCurrentRetainedGate.H
  simp only [Set.mem_ofPred_eq]
  rw [ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hPast]
  simp only [Option.map_some]
  constructor
  · rintro ⟨v, hv, hflag⟩
    have heq := Option.some.inj hv
    subst v
    change (RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) N).overflow = false at hflag
    exact (literalQueueSafe_iff_run_not_overflow rate N).2 hflag
  · intro hsafe
    refine ⟨ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) N),
      rfl, ?_⟩
    change (RecordedQueueRun.run
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) N).overflow = false
    exact (literalQueueSafe_iff_run_not_overflow rate N).1 hsafe

/-- A source-safe literal H task passes the inclusive decoder gate and the
same-date retained queue gate. Decoder coverage is the forward implication
from literal source failures to the diagnostic past flag. -/
theorem literalStoppedHTaskSupport_mem_diagnostic
    (t : Fin p.T) (i : Fin (p.m - 1))
    (z : SourceInput p)
    (h : literalStoppedHTaskSupport rate rewards C_star C_h t i z) :
    z ∈ diagnosticHTaskSupport rate rewards C_star C_h t i := by
  rcases h with ⟨hraw, hsafe, N, hN, hqueue⟩
  have hliteral : ∀ u : Fin p.T, u.val < t.val →
      ¬ (ReferenceLiteralSourceDecoderCoverage.S_false
          rate rewards C_star C_h z u ∨
        ReferenceLiteralSourceDecoderCoverage.S_amb
          rate rewards C_star C_h z u) := by
    intro u hu
    have huSafe := hsafe u hu
    change ¬ (ReferenceLiteralSourceDecoderCoverage.S_false
        rate rewards C_star C_h z u ∨
      ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z u) at huSafe
    exact huSafe
  have hflag := ReferenceLiteralSourceDecoderCoverage.decoderPastFlag_false_of_no_earlier_literal_failure
    rate rewards C_star C_h z t.val (Nat.le_of_lt t.isLt) hliteral
  have hkept :=
    (ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt_iff_gate_false
      rate rewards C_star C_h z t).2 hflag
  have hgate := (retainedGate_iff_literalQueueSafe rate rewards C_star C_h t z N hN).2 hqueue
  exact ⟨hraw, hkept, hgate⟩

end Bandits.Support.ReferencePostReplacementCollectionHandoverSourcePrefix

end
