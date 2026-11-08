/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLiteralSourceDecoderCoverage
public import Bandits.Support.ReferenceFirstCollectionAwaitedWaitingCost
public import Bandits.Support.ReferenceFirstCollectionRawQueueStoppingCalendar

/-!
# Literal stopped charge of the first collection

Sources: ZIP4 `05_binary_transport.tex:23-55`,
`06_interruptions.tex:140-177,355-431,459-487`,
`appendix_a_local_protocol.tex:87-157`, and
`appendix_b_communication.tex:94-99,725-751`.

The mask below reads the independent physical decoder events on the original
source and replays the whole recorded numerical inputs from zero queues.
Strict-past tests retain the detecting update. The waiting estimate is in the
awaited phase-start field; identifying a source transfer-start field and using
a tower is a separate successor obligation. No manuscript closure is claimed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionLiteralStoppedCharge

variable {p : ConstructorDimensions.Parameters}

abbrev Cell (p : ConstructorDimensions.Parameters) := RecordedQueueRun.RoundInput p.K

/-- Unstopped calendar queue replay, including deferred numerical updates.
Disabled inputs preserve registers; enabled zero arrivals still serve backlog. -/
def calendarQueue (rate : ReferenceActivePhysicalStep.RateInput p)
    (N : List (Cell p)) (h : ℕ) (a : Fin p.K) : ℕ × ℕ :=
  QueueReplay.replay (4 * rate.n) (0, 0)
    ((N.take h).map fun c =>
      (c.enabled, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a))

/-- No queue overflow on any completed strict-past calendar prefix. -/
def literalQueueSafe (rate : ReferenceActivePhysicalStep.RateInput p)
    (N : List (Cell p)) : Prop :=
  ∀ h, h ≤ N.length → ∀ a : Fin p.K,
    32 * (calendarQueue rate N h a).2 ≤ D p

/-- This is the literal all-arm arithmetic, not a stopped-machine flag. -/
theorem literalQueueSafe_iff_allPrefixes
    (rate : ReferenceActivePhysicalStep.RateInput p) (N : List (Cell p)) :
    literalQueueSafe rate N ↔
      ReferenceFirstCollectionActiveBoundaryQueueQuery.allPrefixes rate
        (ReferenceFirstCollectionActiveBoundaryQueueQuery.numericalArrivals rate N) := by
  simp only [literalQueueSafe, calendarQueue,
    ReferenceFirstCollectionActiveBoundaryQueueQuery.allPrefixes,
    ReferenceFirstCollectionActiveBoundaryQueueQuery.numericalArrivals,
    List.length_map, List.map_take, List.map_map]
  rfl

/-- The literal replay starts with the source's zero launch registers. -/
theorem calendarQueue_zero (rate : ReferenceActivePhysicalStep.RateInput p)
    (N : List (Cell p)) (a : Fin p.K) : calendarQueue rate N 0 a = (0, 0) := rfl

/-- Every full numerical coordinate contributes its own calendar recurrence. -/
theorem calendarQueue_succ (rate : ReferenceActivePhysicalStep.RateInput p)
    (N : List (Cell p)) (h : ℕ) (hh : h < N.length) (a : Fin p.K) :
    calendarQueue rate N (h + 1) a =
      if N[h].enabled then
        let arrival := RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) N[h] a
        let service := min (4 * rate.n) ((calendarQueue rate N h a).2 + arrival)
        ((calendarQueue rate N h a).1 + service,
          (calendarQueue rate N h a).2 + arrival - service)
      else calendarQueue rate N h a := by
  unfold calendarQueue
  rw [← List.take_append_getElem hh, List.map_append, QueueReplay.replay_append]
  rfl

/-- Physical append/quota/clear fields reconstruct the completed DOWN
readout. This direction is needed for the Borel equality, independently of
the forward safety direction used for waiting domination. -/
theorem completedDownBatch_of_physical
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceLiteralSourceDecoderCoverage.Record (rate := rate))
    (i : Fin (p.m - 1)) (W : ReferenceLiteralSourceDecoderCoverage.Batch (p := p))
    (h : ReferenceLiteralSourceDecoderCoverage.physicalDownCompletedAt r i W) :
    ReferenceFirstLiveDownCompletionReadout.completedDownBatch r i = some W := by
  obtain ⟨logged, cut, hi, hd, hsel, hstatus, hreg, hbank, hbuffer,
    hW, hlen, _hclear, _hraw⟩ := h
  have hactual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    r i logged cut hi hd
  have hc : cut.rawComparison.isSome = true := by
    rw [hactual]
    unfold ReferenceDownReception.referenceDownCut
    simp only [dite_eq_left hsel, dite_eq_left hstatus, dite_eq_left hreg,
      dite_eq_left hbank, dite_eq_left hbuffer]
    split <;> rfl
  apply (ReferenceFirstLiveDownCompletionReadout.completedDownBatch_eq_some_iff r i W).mpr
  refine ⟨logged, cut, hi, hd, hc, ?_, ?_⟩
  · rw [← hlen, hW]
    exact Nat.le_refl _
  · exact hW.symm

/-- The corresponding UP dictionary preserves the carried bank and current
append, even when subsequent ledger completion fails. -/
theorem completedUpBatch_of_physical
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceLiteralSourceDecoderCoverage.Record (rate := rate))
    (i : Fin (p.m - 1)) (W : ReferenceLiteralSourceDecoderCoverage.Batch (p := p))
    (h : ReferenceLiteralSourceDecoderCoverage.physicalUpCompletedAt r i W) :
    ReferenceCollectionUpFailureReadoutV2.completedUpBatch rate r i = some W := by
  obtain ⟨d, hd, hi, hdom, hel, hW, hlen, _hclear, _hraw⟩ := h
  have hc := (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mpr hdom
  have happ : ReferenceCollectionUpFailureReadoutV2.appendedUp rate d = W := by
    simpa only [ReferenceCollectionUpFailureReadoutV2.appendedUp, hi] using hW.symm
  unfold ReferenceCollectionUpFailureReadoutV2.completedUpBatch
  simp only [hd]
  rw [ite_eq_left ⟨hi, hc, hel, by rw [happ, hlen]⟩]
  exact congrArg some happ

/-- Negating the literal safe-prefix predicate gives an actual calendar
queue crossing with the source integer threshold. -/
theorem not_literalQueueSafe_iff (rate : ReferenceActivePhysicalStep.RateInput p)
    (N : List (Cell p)) :
    ¬ literalQueueSafe rate N ↔
      ∃ h, h ≤ N.length ∧ ∃ a : Fin p.K,
        D p < 32 * (calendarQueue rate N h a).2 := by
  simp only [literalQueueSafe, not_forall, not_le, exists_prop]

/-- Disabled calendar inputs preserve both registers. -/
theorem calendarQueue_succ_disabled (rate : ReferenceActivePhysicalStep.RateInput p)
    (N : List (Cell p)) (h : ℕ) (hh : h < N.length) (a : Fin p.K)
    (hd : N[h].enabled = false) :
    calendarQueue rate N (h + 1) a = calendarQueue rate N h a := by
  rw [calendarQueue_succ rate N h hh a, hd]
  rfl

/-- Enabled zero-arrival inputs still serve existing backlog, including
zero values produced by the quantization floor. -/
theorem calendarQueue_succ_enabled_zero (rate : ReferenceActivePhysicalStep.RateInput p)
    (N : List (Cell p)) (h : ℕ) (hh : h < N.length) (a : Fin p.K)
    (he : N[h].enabled = true)
    (hz : RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) N[h] a = 0) :
    calendarQueue rate N (h + 1) a =
      ((calendarQueue rate N h a).1 + min (4 * rate.n) (calendarQueue rate N h a).2,
        (calendarQueue rate N h a).2 - min (4 * rate.n) (calendarQueue rate N h a).2) := by
  rw [calendarQueue_succ rate N h hh a, he]
  simp only [ite_true, hz, Nat.add_zero]

section Actual

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "R" z:max =>
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "b" z:max =>
  ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "w" z:max => List.length (ReferenceFirstLiveConfirmationHistory.firstLiveWindow (R z))
local notation "B" z:max => ReferenceCollectionPhaseHistory.collectionWindow (R z) (w z)
local notation "obs" z:max =>
  ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate rewards C_star C_h z

/-- Exact finite-coordinate characterization of the literal DOWN event.
The reverse map drops redundant original-coordinate fields, while the forward
map reconstructs them. Both maps retain every positive and every selected
zero date in the fixed-awaited interval. -/
theorem literalDownAmbiguityAt_iff
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt rate rewards C_star C_h z t ↔
      ReferenceFirstCollectionAwaitedDownFailureReadout.fixedAwaitedDownFailureAt
        rate rewards C_star C_h z t := by
  constructor
  · rintro ⟨r, i, word, W, a, hr, hW, hat, hmulti, hentries, hcalendar⟩
    refine ⟨r, i, word, W, a, hr, completedDownBatch_of_physical r i W hW,
      hat, (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff W).mpr hmulti, ?_, ?_⟩
    · intro e he
      obtain ⟨ha, ht, heq, re, hre, _hrows, _hselected, _htime, _hrewards,
        _hsample, hpositive, haw⟩ := hentries e he
      exact ⟨ha, ht, heq, re, hre, hpositive,
        ReferenceLiteralSourceDecoderCoverage.awaitedDownAt_of_physicalAwaitedDownAt re i word haw⟩
    · intro v ha ht hchannel
      obtain ⟨rv, hrv, _hrows, _hselected, _htime, _hrewards, haw⟩ :=
        hcalendar v ha ht hchannel
      exact ⟨rv, hrv,
        ReferenceLiteralSourceDecoderCoverage.awaitedDownAt_of_physicalAwaitedDownAt rv i word haw⟩
  · exact ReferenceLiteralSourceDecoderCoverage.literalDownAmbiguityAt_of_fixedAwaitedDownFailureAt
      rate rewards C_star C_h z t

/-- Exact UP characterization on the same completed bank, original positive
origins, fixed encoded ordinary record, and selected calendar interval. -/
theorem literalUpAmbiguityAt_iff
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt rate rewards C_star C_h z t ↔
      ReferenceCollectionUpFailureReadoutV2.fixedAwaitedUpFailureAt rate rewards C_star C_h z t := by
  constructor
  · rintro ⟨r, i, M, W, a, hr, hW, hat, hsigma, hmulti, hentries, hcalendar⟩
    refine ⟨r, i, M, W, a, hr, completedUpBatch_of_physical r i W hW,
      hat, hsigma, (ReferenceFirstLiveDownCompletionReadout.multipleSolutions_iff W).mpr hmulti,
      ?_, ?_⟩
    · intro e he
      obtain ⟨ha, ht, heq, re, hre, _hrows, _hselected, _htime, _hrewards,
        _hsample, hpositive, haw⟩ := hentries e he
      exact ⟨ha, ht, heq, re, hre, hpositive,
        ReferenceLiteralSourceDecoderCoverage.awaitedUpAt_of_physicalAwaitedUpAt re i M haw⟩
    · intro v ha ht hchannel
      obtain ⟨rv, hrv, _hrows, _hselected, _htime, _hrewards, haw⟩ :=
        hcalendar v ha ht hchannel
      exact ⟨rv, hrv,
        ReferenceLiteralSourceDecoderCoverage.awaitedUpAt_of_physicalAwaitedUpAt rv i M haw⟩
  · exact ReferenceLiteralSourceDecoderCoverage.literalUpAmbiguityAt_of_fixedAwaitedUpFailureAt
      rate rewards C_star C_h z t

/-- Two-sided characterization, used only to establish real Borel
measurability. Waiting support below consumes the forward safety theorem. -/
theorem literalFailure_iff_decoderFailureAt
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    (ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z t ∨
      ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z t) ↔
      ReferenceFirstCollectionInclusiveDecoderStop.decoderFailureAt rate rewards C_star C_h z t := by
  constructor
  · intro h
    apply (ReferenceFirstCollectionInclusiveDecoderStop.decoderFailureAt_sourceWitnesses
      rate rewards C_star C_h z t).mpr
    rcases h with (hpre | hwrong) | (hdown | hup)
    · obtain ⟨i, hi⟩ := hpre
      exact Or.inl ⟨i, (ReferenceSourceRawDecoderDecision.prelaunch_down_wrong_iff
        rate rewards C_star C_h z t i).mp hi⟩
    · exact Or.inr (Or.inl
        ((ReferenceSourceRawDecoderDecision.actual_raw_wrong_decision_iff_saved_diagnostic
          rate rewards C_star C_h z t).mp hwrong))
    · exact Or.inr (Or.inr (Or.inl
        ((literalDownAmbiguityAt_iff rate rewards C_star C_h z t).mp hdown)))
    · exact Or.inr (Or.inr (Or.inr
        ((literalUpAmbiguityAt_iff rate rewards C_star C_h z t).mp hup)))
  · exact ReferenceLiteralSourceDecoderCoverage.decoderFailureAt_implies_literal_source_failure
      rate rewards C_star C_h z t

/-- The literal source failure union is Borel on the original continuous
source carrier. The proof uses the exact finite-coordinate characterization,
not one-sided event inclusion. -/
theorem literalFailure_borel (t : Fin p.T) :
    MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
      ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z t ∨
        ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z t} := by
  have heq : {z : BootstrapPrivateRoundStreams.SourceInput p |
      ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z t ∨
        ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z t} =
      {z | ReferenceFirstCollectionInclusiveDecoderStop.decoderFailureAt
        rate rewards C_star C_h z t} := by
    ext z
    exact literalFailure_iff_decoderFailureAt rate rewards C_star C_h z t
  rw [heq]
  exact ReferenceFirstCollectionInclusiveDecoderStop.decoderFailureAt_borel
    rate rewards C_star C_h t

/-- The source decoder is tested only at strictly earlier physical dates. -/
def noEarlierLiteralFailure (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) : Prop :=
  ∀ v : Fin p.T, v.val < t.val →
    ¬ (ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z v ∨
      ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z v)

/-- Candidate strict-past detection successor, including the horizon
sentinel. The predicate uses the independent literal source events. -/
def literalDetectorIndexOccurs (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) : Prop :=
  n = p.T ∨ ∃ t : Fin p.T, t.val + 1 = n ∧
    (ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z t ∨
      ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z t)

/-- The source horizon always supplies a finite scan candidate. -/
theorem literalDetectorIndexOccurs_exists (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ∃ n, literalDetectorIndexOccurs rate rewards C_star C_h z n :=
  ⟨p.T, Or.inl rfl⟩

/-- First excluded one-based decoder date. A failure at zero-based `f`
excludes from `min (T+1) (f+2)` onward, retaining the detecting update. -/
def literalDecoderEndpoint (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  min (p.T + 1)
    (Nat.find (literalDetectorIndexOccurs_exists rate rewards C_star C_h z) + 1)

/-- The literal scan agrees with the checked diagnostic scan by an exact
predicate equality, rather than by a safety inclusion alone. -/
theorem literalDecoderEndpoint_eq (z : BootstrapPrivateRoundStreams.SourceInput p) :
    literalDecoderEndpoint rate rewards C_star C_h z =
      ReferenceFirstCollectionInclusiveDecoderStop.firstExcludedDate rate rewards C_star C_h z := by
  have hfind : Nat.find (literalDetectorIndexOccurs_exists rate rewards C_star C_h z) =
      ReferenceFirstCollectionInclusiveDecoderStop.firstDetectionIndex rate rewards C_star C_h z := by
    apply Nat.find_congr'
    intro n
    unfold literalDetectorIndexOccurs ReferenceFirstCollectionInclusiveDecoderStop.detectorIndexOccurs
    simp only [literalFailure_iff_decoderFailureAt]
  exact congrArg (fun n => min (p.T + 1) (n + 1)) hfind

/-- Exact inclusive endpoint characterization on every original source date. -/
theorem noEarlierLiteralFailure_iff_endpoint
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    noEarlierLiteralFailure rate rewards C_star C_h z t ↔
      t.val + 1 < literalDecoderEndpoint rate rewards C_star C_h z := by
  rw [literalDecoderEndpoint_eq]
  have h := ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt_iff_no_earlier
    rate rewards C_star C_h z t
  simpa only [noEarlierLiteralFailure, literalFailure_iff_decoderFailureAt,
    ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt] using h.symm

/-- Decoder endpoints include the no-failure horizon sentinel. -/
theorem literalDecoderEndpoint_bounds (z : BootstrapPrivateRoundStreams.SourceInput p) :
    2 ≤ literalDecoderEndpoint rate rewards C_star C_h z ∧
      literalDecoderEndpoint rate rewards C_star C_h z ≤ p.T + 1 := by
  rw [literalDecoderEndpoint_eq]
  exact ReferenceFirstCollectionInclusiveDecoderStop.firstExcludedDate_bounds
    rate rewards C_star C_h z

/-- An actual first literal failure has the stated inclusive clipped
endpoint, including detection in the last physical round. -/
theorem literalDecoderEndpoint_of_first_failure
    (z : BootstrapPrivateRoundStreams.SourceInput p) (f : Fin p.T)
    (hf : ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z f ∨
      ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z f)
    (hno : noEarlierLiteralFailure rate rewards C_star C_h z f) :
    literalDecoderEndpoint rate rewards C_star C_h z = min (p.T + 1) (f.val + 2) := by
  let h := literalDetectorIndexOccurs_exists rate rewards C_star C_h z
  have hle : Nat.find h ≤ f.val + 1 := Nat.find_min' h (Or.inr ⟨f, rfl, hf⟩)
  have hspec := Nat.find_spec h
  change Nat.find h = p.T ∨ ∃ t : Fin p.T, t.val + 1 = Nat.find h ∧
    (ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z t ∨
      ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z t) at hspec
  have heq : Nat.find h = f.val + 1 := by
    rcases hspec with hsent | ⟨t, ht, hfail⟩
    · have := f.isLt
      omega
    · have hnot : ¬ t.val < f.val := fun htf => hno t htf hfail
      omega
  change min (p.T + 1) (Nat.find h + 1) = _
  rw [heq]

/-- With no literal source failure the endpoint is the horizon sentinel. -/
theorem literalDecoderEndpoint_of_no_failure
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hno : ∀ t : Fin p.T,
      ¬ (ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z t ∨
        ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z t)) :
    literalDecoderEndpoint rate rewards C_star C_h z = p.T + 1 := by
  let h := literalDetectorIndexOccurs_exists rate rewards C_star C_h z
  have hspec := Nat.find_spec h
  change Nat.find h = p.T ∨ ∃ t : Fin p.T, t.val + 1 = Nat.find h ∧
    (ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z t ∨
      ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z t) at hspec
  have heq : Nat.find h = p.T := hspec.elim id (fun ⟨t, _, ht⟩ => (hno t ht).elim)
  change min (p.T + 1) (Nat.find h + 1) = _
  rw [heq, Nat.min_self]

/-- Original raw collection date, whole actual numerical prefix through its
current cell, literal strict-past decoder safety, and literal queue recurrence.
The matching pair is produced below; it is never a caller-supplied premise. -/
def literalDateKept (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) : Prop :=
  (∃ k : Fin (B z).length, (B z)[k.val].input.time = t) ∧
    noEarlierLiteralFailure rate rewards C_star C_h z t ∧
    ∃ (N : List (Cell p)) (c : Cell p),
      ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches rate (b z) (b z + w z) t (obs z) N c ∧
      literalQueueSafe rate N

/-- Finite physical calendar selected by the literal source predicates. -/
def literalCalendar (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset (Fin p.T) :=
  Finset.univ.filter (literalDateKept rate rewards C_star C_h z)

/-- The capped collection weight on the same original physical reward row. -/
def barG (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  min (p.m : ℝ) (ReferenceFirstCollectionRoundEndObservation.g rewards t.val z)

/-- The literal stopped first-collection component of the transfer charge. -/
def literalCharge (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ∑ t ∈ literalCalendar rate rewards C_star C_h z, barG rewards t z

/-- Literal queue alignment is derived at each original raw date using its
unique complete numerical pair. No queue survival premise is required. -/
theorem literalDateKept_iff_queueEvent
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    literalDateKept rate rewards C_star C_h z t ↔
      (∃ k : Fin (B z).length, (B z)[k.val].input.time = t) ∧
      noEarlierLiteralFailure rate rewards C_star C_h z t ∧
      z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (b z) (b z + w z) t := by
  constructor
  · rintro ⟨⟨k, hk⟩, hs, N, c, hm, hq⟩
    obtain ⟨_, _, _, hC, _⟩ :=
      ReferenceFirstCollectionRawCalendarNumericalCoverage.original_raw_calendar_numerical_coverage
        rate rewards C_star C_h z k
    refine ⟨⟨k, hk⟩, hs, ?_⟩
    exact ⟨by simpa only [hk] using hC, N, c, hm,
      (literalQueueSafe_iff_allPrefixes rate N).mp hq⟩
  · rintro ⟨hr, hs, _, N, c, hm, hq⟩
    exact ⟨hr, hs, N, c, hm, (literalQueueSafe_iff_allPrefixes rate N).mpr hq⟩

/-- The raw queue calendar is consumed only after literal alignment. -/
theorem literalDateKept_iff_rawQueueCalendar
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    literalDateKept rate rewards C_star C_h z t ↔
      noEarlierLiteralFailure rate rewards C_star C_h z t ∧
      t ∈ ReferenceFirstCollectionRawQueueStoppingCalendar.rawQueueCalendar rate rewards C_star C_h z := by
  rw [literalDateKept_iff_queueEvent, ReferenceFirstCollectionRawQueueStoppingCalendar.mem_rawQueueCalendar_iff]
  tauto

/-- Every source-kept date belongs to the checked awaited support, at exactly
the original raw record's physical time. Pending nonemptiness is produced by
the admitted calendar theorem, not assumed here. -/
theorem literalDateKept_mem_awaited_support
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T)
    (ht : literalDateKept rate rewards C_star C_h z t) :
    t.val ∈ ReferenceFirstCollectionAwaitedPhaseSupport.supportIndices
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z := by
  obtain ⟨⟨k, hk⟩, hs, _⟩ := ht
  have hflag := ReferenceLiteralSourceDecoderCoverage.pastFailureFlag_false_of_no_earlier_literal_failure
    rate rewards C_star C_h z t.val hs
  have hsupport :=
    ReferenceFirstCollectionRawCalendarNumericalCoverage.original_raw_calendar_awaited_support_of_no_past_failure
      rate rewards C_star C_h z k (by simpa only [hk] using hflag)
  simpa only [hk] using hsupport

/-- Every raw date produces one unique full actual numerical pair. The
literal queue test on that pair is independent of the choice of witness in
the definition of the source mask. All numerical coordinates, including the
current cell, occur in `Matches`. -/
theorem original_raw_literal_numerical_characterization
    (z : BootstrapPrivateRoundStreams.SourceInput p) (k : Fin (B z).length) :
    ∃! pair : List (Cell p) × Cell p,
      ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches rate (b z) (b z + w z)
        (B z)[k.val].input.time (obs z) pair.1 pair.2 ∧
      (literalDateKept rate rewards C_star C_h z (B z)[k.val].input.time ↔
        noEarlierLiteralFailure rate rewards C_star C_h z (B z)[k.val].input.time ∧
          literalQueueSafe rate pair.1) := by
  obtain ⟨_, _, _, _, pair, hm, hu⟩ :=
    ReferenceFirstCollectionRawCalendarNumericalCoverage.original_raw_calendar_numerical_coverage
      rate rewards C_star C_h z k
  refine ⟨pair, ⟨hm, ?_⟩, fun other ho => hu other ho.1⟩
  constructor
  · rintro ⟨_, hs, N, c, hm', hq⟩
    have heq : (N, c) = pair := hu (N, c) hm'
    exact ⟨hs, by simpa only [← heq] using hq⟩
  · rintro ⟨hs, hq⟩
    exact ⟨⟨k, rfl⟩, hs, pair.1, pair.2, hm, hq⟩

/-- On a nonempty collection, the LAST full actual pair supplies one common
queue endpoint for all original dates. Intersecting it with the independent
literal decoder endpoint gives the exact source mask. No shorter prefix's
sentinel is used as the common endpoint. -/
theorem original_literal_calendar_common_endpoint
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hB : B z ≠ []) :
    ∃! pair : List (Cell p) × Cell p,
      ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches rate (b z) (b z + w z)
        (List.getLast (B z) hB).input.time (obs z) pair.1 pair.2 ∧
      let e_q := ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded
        rate (b z) (pair.1 ++ [pair.2])
      let e_s := literalDecoderEndpoint rate rewards C_star C_h z
      2 ≤ e_q ∧ e_q ≤ p.T + 1 ∧
      ∀ t : Fin p.T, literalDateKept rate rewards C_star C_h z t ↔
        b z + w z ≤ t.val ∧ t.val < b z + w z + (B z).length ∧
          t.val + 1 < min e_s e_q := by
  obtain ⟨pair, ⟨hm, hlo, hhi, hcalendar, _himage, _hcard⟩, hu⟩ :=
    ReferenceFirstCollectionRawQueueStoppingCalendar.original_raw_queue_calendar_characterization
      rate rewards C_star C_h z hB
  refine ⟨pair, ⟨hm, hlo, hhi, ?_⟩, ?_⟩
  · intro t
    rw [literalDateKept_iff_rawQueueCalendar, hcalendar t,
      noEarlierLiteralFailure_iff_endpoint, Nat.lt_min]
    tauto
  · intro other ho
    exact ReferenceFirstCollectionActiveBoundaryQueueQuery.matches_unique
      (b z) (b z + w z) (List.getLast (B z) hB).input.time (obs z) ho.1 hm

/-- The actual first overflow cell is retained whenever no strictly earlier
literal decoder failure occurred. Every later raw date is excluded, and the
same first-overflow endpoint stabilizes in every later whole prefix. -/
theorem original_literal_calendar_first_overflow
    (z : BootstrapPrivateRoundStreams.SourceInput p) (k0 : Fin (B z).length) :
    ∃! pair : List (Cell p) × Cell p,
      ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches rate (b z) (b z + w z)
        (B z)[k0.val].input.time (obs z) pair.1 pair.2 ∧
      (UnstoppedRecordedQueueComparison.firstOverflowPrefix
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) (pair.1 ++ [pair.2]) =
          pair.1.length + 1 →
        (literalDateKept rate rewards C_star C_h z (B z)[k0.val].input.time ↔
          noEarlierLiteralFailure rate rewards C_star C_h z (B z)[k0.val].input.time) ∧
        (∀ k1 : Fin (B z).length, k0 < k1 →
          ¬ literalDateKept rate rewards C_star C_h z (B z)[k1.val].input.time) ∧
        (∀ k1 : Fin (B z).length, k0 ≤ k1 →
          ∃! later : List (Cell p) × Cell p,
            ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches rate (b z) (b z + w z)
              (B z)[k1.val].input.time (obs z) later.1 later.2 ∧
            UnstoppedRecordedQueueComparison.firstOverflowPrefix
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) (later.1 ++ [later.2]) =
                pair.1.length + 1 ∧
            ReferenceFirstCollectionQueuePrefixChronology.prefixOverflowExcluded
              rate (b z) (later.1 ++ [later.2]) =
                min (p.T + 1) ((B z)[k0.val].input.time.val + 2))) := by
  obtain ⟨pair, ⟨hm, hcross⟩, _hu⟩ :=
    ReferenceFirstCollectionRawQueueStoppingCalendar.original_raw_calendar_first_detecting_cell
      rate rewards C_star C_h z k0
  refine ⟨pair, ⟨hm, ?_⟩, fun other ho =>
    ReferenceFirstCollectionActiveBoundaryQueueQuery.matches_unique
      (b z) (b z + w z) (B z)[k0.val].input.time (obs z) ho.1 hm⟩
  · intro hc
    obtain ⟨_hdate, hkept, hlater, hstable⟩ := hcross hc
    refine ⟨?_, ?_, hstable⟩
    · rw [literalDateKept_iff_rawQueueCalendar]
      exact and_iff_left hkept
    · intro k1 hk hkept'
      exact hlater k1 hk
        ((literalDateKept_iff_rawQueueCalendar rate rewards C_star C_h z _).mp hkept').2

/-- The charge is exactly the sum over ORIGINAL kept collection records.
Calendar injectivity is essential here: no physical date can be counted twice. -/
theorem literalCharge_eq_raw_sum (z : BootstrapPrivateRoundStreams.SourceInput p) :
    literalCharge rate rewards C_star C_h z =
      ∑ k ∈ (Finset.univ : Finset (Fin (B z).length)).filter
        (fun k => literalDateKept rate rewards C_star C_h z (B z)[k.val].input.time),
          barG rewards (B z)[k.val].input.time z := by
  let indices := (Finset.univ : Finset (Fin (B z).length)).filter
    (fun k => literalDateKept rate rewards C_star C_h z (B z)[k.val].input.time)
  have himage : literalCalendar rate rewards C_star C_h z =
      indices.image (fun k => (B z)[k.val].input.time) := by
    ext t
    simp only [literalCalendar, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, indices]
    constructor
    · intro ht
      obtain ⟨k, hk⟩ := ht.1
      exact ⟨k, by simpa only [hk] using ht, hk⟩
    · rintro ⟨k, hk, rfl⟩
      exact hk
  unfold literalCharge
  rw [himage, Finset.sum_image]
  exact fun _ _ _ _ heq =>
    ReferenceFirstCollectionRawQueueStoppingCalendar.original_raw_calendar_injective
      rate rewards C_star C_h z heq

/-- Overflow strictly before collection makes the entire literal mask
empty. Its test is on the uniquely produced actual first raw pair: that
pair's strict-past prefixes include every launch-to-cutoff queue update. -/
theorem original_literal_calendar_empty_of_prior_overflow
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hB : B z ≠ []) :
    ∃! pair : List (Cell p) × Cell p,
      ReferenceFirstCollectionActiveBoundaryQueueQuery.Matches rate (b z) (b z + w z)
        (List.head (B z) hB).input.time (obs z) pair.1 pair.2 ∧
      (¬ literalQueueSafe rate pair.1 →
        literalCalendar rate rewards C_star C_h z = ∅ ∧
          literalCharge rate rewards C_star C_h z = 0) := by
  have hpos : 0 < (B z).length := List.length_pos_iff.mpr hB
  let first : Fin (B z).length := ⟨0, hpos⟩
  have hfirst : (B z)[first.val] = List.head (B z) hB := by
    simp only [List.head_eq_getElem, first]
  obtain ⟨_hbu, _hut, _hw, _hC, pair, hm, hu⟩ :=
    ReferenceFirstCollectionRawCalendarNumericalCoverage.original_raw_calendar_numerical_coverage
      rate rewards C_star C_h z first
  refine ⟨pair, ⟨by simpa only [hfirst] using hm, ?_⟩, ?_⟩
  · intro hunsafe
    have hnot : (B z)[first.val].input.time ∉
        ReferenceFirstCollectionRawQueueStoppingCalendar.rawQueueCalendar rate rewards C_star C_h z := by
      intro hq
      obtain ⟨_, _, N, c, hm', hsafe⟩ :=
        (ReferenceFirstCollectionRawQueueStoppingCalendar.mem_rawQueueCalendar_iff
          rate rewards C_star C_h z _).mp hq
      have heq : (N, c) = pair := hu (N, c) hm'
      apply hunsafe
      have hs := (literalQueueSafe_iff_allPrefixes rate N).mpr hsafe
      simpa only [← heq] using hs
    obtain ⟨last, ⟨_hm, _hlo, _hhi, hcalendar, _himage, _hcard⟩, _hu⟩ :=
      ReferenceFirstCollectionRawQueueStoppingCalendar.original_raw_queue_calendar_characterization
        rate rewards C_star C_h z hB
    have hdate := ReferenceFirstCollectionRawQueueStoppingCalendar.original_raw_calendar_date
      rate rewards C_star C_h z first
    have hdate0 : (B z)[first.val].input.time.val = b z + w z := by
      change (B z)[first.val].input.time.val = b z + w z + 0 at hdate
      exact hdate.trans (Nat.add_zero _)
    have hempty : literalCalendar rate rewards C_star C_h z = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have hq := ((literalDateKept_iff_rawQueueCalendar rate rewards C_star C_h z t).mp
        (Finset.mem_filter.mp ht).2).2
      have ht' := (hcalendar t).mp hq
      apply hnot
      apply (hcalendar (B z)[first.val].input.time).mpr
      exact ⟨by omega, by omega, by omega⟩
    exact ⟨hempty, by simp only [literalCharge, hempty, Finset.sum_empty]⟩
  · intro other ho
    exact hu other (by simpa only [← hfirst] using ho.1)

/-- Empty collection windows contribute zero, including absent cutoff. -/
theorem literalCharge_eq_zero_of_window_empty
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hB : B z = []) :
    literalCharge rate rewards C_star C_h z = 0 := by
  have hempty : literalCalendar rate rewards C_star C_h z = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hk := (Finset.mem_filter.mp ht).2.1
    obtain ⟨k, _⟩ := hk
    have hlen : (B z).length = 0 := by rw [hB]; rfl
    have := k.isLt
    omega
  simp only [literalCharge, hempty, Finset.sum_empty]

/-- If the physical suffix has no chosen cutoff, its first collection
window is empty. Failure and rejected records remain in that suffix. -/
theorem literalCharge_eq_zero_of_no_cutoff
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hno : ∀ r ∈ R z, ReferenceCollectionPhaseHistory.cutoffChosen r.input = false) :
    literalCharge rate rewards C_star C_h z = 0 := by
  have hwindow : ReferenceFirstLiveConfirmationHistory.firstLiveWindow (R z) = R z := by
    apply List.takeWhile_eq_self_iff.mpr
    intro r hr
    simp only [hno r hr, Bool.not_false]
  apply literalCharge_eq_zero_of_window_empty rate rewards C_star C_h z
  have hw : w z = (R z).length := congrArg List.length hwindow
  simp only [ReferenceCollectionPhaseHistory.collectionWindow, hw, List.drop_length,
    List.take_nil, List.drop_eq_nil_of_le (by omega : (R z).length ≤ (R z).length + 1),
    List.takeWhile_nil, List.append_nil]

/-- Capping keeps the original nonnegative reward count. -/
theorem barG_bounds (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    0 ≤ barG rewards t z ∧
      barG rewards t z ≤ ReferenceFirstCollectionRoundEndObservation.g rewards t.val z := by
  have hg := (ReferenceFirstCollectionRoundEndObservation.g_mem_Icc rewards t.val z).1
  exact ⟨le_min (Nat.cast_nonneg _) hg, min_le_right _ _⟩

/-- Pointwise domination of the literal source charge by the checked waiting
charge. Finite physical dates are counted once, with no mask-alignment input. -/
theorem literalCharge_bounds (z : BootstrapPrivateRoundStreams.SourceInput p) :
    0 ≤ literalCharge rate rewards C_star C_h z ∧
      literalCharge rate rewards C_star C_h z ≤
        ReferenceFirstCollectionAwaitedWaitingCost.actualFirstCollectionAwaitedWaitingCharge
          rate rewards C_star C_h z := by
  let dates : Fin (B z).length → Fin p.T := fun k => (B z)[k.val].input.time
  let indices : Finset (Fin (B z).length) := Finset.univ.filter
    (fun k => literalDateKept rate rewards C_star C_h z (dates k))
  let supported := ReferenceFirstCollectionAwaitedPhaseSupport.supportIndices
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) z
  let weight : ℕ → ℝ := fun n => ReferenceFirstCollectionRoundEndObservation.g rewards n z
  have hraw : literalCharge rate rewards C_star C_h z =
      ∑ k ∈ indices, barG rewards (dates k) z :=
    literalCharge_eq_raw_sum rate rewards C_star C_h z
  have hinj : Function.Injective (fun k => (dates k).val) := by
    intro k l h
    exact ReferenceFirstCollectionRawQueueStoppingCalendar.original_raw_calendar_injective
      rate rewards C_star C_h z (Fin.ext h)
  have hsubset : indices.image (fun k => (dates k).val) ⊆ supported := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    exact literalDateKept_mem_awaited_support rate rewards C_star C_h z (dates k)
      (Finset.mem_filter.mp hk).2
  have hsum : (∑ k ∈ indices, weight (dates k).val) ≤ ∑ n ∈ supported, weight n :=
    Finset.sum_le_sum_of_injOn (fun k => (dates k).val) hinj.injOn hsubset
      (fun _ _ => le_rfl)
      (fun n _ _ => (ReferenceFirstCollectionRoundEndObservation.g_mem_Icc rewards n z).1)
  constructor
  · exact Finset.sum_nonneg fun t _ => (barG_bounds rewards t z).1
  · calc
      literalCharge rate rewards C_star C_h z = ∑ k ∈ indices, barG rewards (dates k) z := hraw
      _ ≤ ∑ k ∈ indices, weight (dates k).val :=
        Finset.sum_le_sum fun k _ => (barG_bounds rewards (dates k) z).2
      _ ≤ ∑ n ∈ supported, weight n := hsum
      _ = _ :=
        (ReferenceFirstCollectionAwaitedWaitingCost.actualFirstCollectionAwaitedWaitingCharge_eq_supported_sum
          rate rewards C_star C_h z).symm

/-- The literal mask has an actual-boundary, finite-observation
characterization. The reverse direction produces its original raw date and
identifies both boundaries; it does not postulate mask alignment. -/
theorem literalDateKept_iff_exists_queueEvent
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    literalDateKept rate rewards C_star C_h z t ↔
      noEarlierLiteralFailure rate rewards C_star C_h z t ∧
      ∃ s u : ℕ, s ≤ u ∧ u ≤ t.val ∧
        z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s u t := by
  rw [literalDateKept_iff_queueEvent]
  constructor
  · rintro ⟨⟨k, hk⟩, hs, hq⟩
    obtain ⟨hbu, hut, _⟩ :=
      ReferenceFirstCollectionRawCalendarNumericalCoverage.original_raw_calendar_numerical_coverage
        rate rewards C_star C_h z k
    exact ⟨hs, b z, b z + w z, hbu, by simpa only [hk] using hut, hq⟩
  · rintro ⟨hs, s, u, hsu, hut, hq⟩
    have hP := ReferenceFirstCollectionActiveBoundaryQueueQuery.C_subset_Praw s u t hq.1
    obtain ⟨k, hk⟩ := ReferenceFirstCollectionPendingObservation.Praw_localization
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) t z hP
    obtain ⟨hbu, hut', _, hC, _⟩ :=
      ReferenceFirstCollectionRawCalendarNumericalCoverage.original_raw_calendar_numerical_coverage
        rate rewards C_star C_h z k
    have hC' : z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.C
        rate rewards C_star C_h (b z) (b z + w z) t := by simpa only [hk] using hC
    have heq := ReferenceFirstCollectionQueuePrefixChronology.active_cutoff_unique_across_dates
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      hsu hut hbu (by simpa only [hk] using hut') hq.1 hC'
    exact ⟨⟨k, hk⟩, hs, by simpa only [heq.1, heq.2] using hq⟩

/-- Borel strict-past source safety, including original zero observations. -/
theorem noEarlierLiteralFailure_borel (t : Fin p.T) :
    MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
      noEarlierLiteralFailure rate rewards C_star C_h z t} := by
  have heq : {z : BootstrapPrivateRoundStreams.SourceInput p |
      noEarlierLiteralFailure rate rewards C_star C_h z t} =
      ⋂ v : Fin p.T, {z | v.val < t.val →
        ¬ (ReferenceLiteralSourceDecoderCoverage.S_false rate rewards C_star C_h z v ∨
          ReferenceLiteralSourceDecoderCoverage.S_amb rate rewards C_star C_h z v)} := by
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, noEarlierLiteralFailure]
  rw [heq]
  apply MeasurableSet.iInter
  intro v
  by_cases hv : v.val < t.val
  · simpa only [hv, true_implies, Set.compl_def, Set.mem_ofPred_eq] using
      (literalFailure_borel rate rewards C_star C_h v).compl
  · simp only [hv, false_implies, Set.ofPred_true]
    exact MeasurableSet.univ

/-- Borel measurability of the actual literal mask. Queue queries are exact
strict-prefix finite-observation events, and both actual boundaries are
produced by the preceding characterization. -/
theorem literalDateKept_borel (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    MeasurableSet {z : BootstrapPrivateRoundStreams.SourceInput p |
      literalDateKept rate rewards C_star C_h z t} := by
  have heq : {z : BootstrapPrivateRoundStreams.SourceInput p |
      literalDateKept rate rewards C_star C_h z t} =
      {z | noEarlierLiteralFailure rate rewards C_star C_h z t} ∩
      ⋃ s : ℕ, ⋃ u : ℕ, {z | s ≤ u ∧ u ≤ t.val ∧
        z ∈ ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) s u t} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
      literalDateKept_iff_exists_queueEvent]
  rw [heq]
  apply (noEarlierLiteralFailure_borel rate rewards C_star C_h t).inter
  apply MeasurableSet.iUnion
  intro s
  apply MeasurableSet.iUnion
  intro u
  by_cases hsu : s ≤ u
  · by_cases hut : u ≤ t.val
    · simp only [hsu, hut, true_and]
      exact ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le _) _
        (ReferenceFirstCollectionActiveBoundaryQueueQuery.queueEvent_measurable
          control0 s u t hsu hut)
    · simp only [hut, and_false, false_and, Set.ofPred_false]
      exact MeasurableSet.empty
  · simp only [hsu, false_and, Set.ofPred_false]
    exact MeasurableSet.empty

/-- The literal finite sum is measurable under the original source Borel
structure, rather than an artificially discrete source carrier. -/
theorem literalCharge_measurable (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (literalCharge rate rewards C_star C_h) := by
  have heq : literalCharge rate rewards C_star C_h =
      fun z => ∑ t : Fin p.T,
        if literalDateKept rate rewards C_star C_h z t then barG rewards t z else 0 := by
    funext z
    simp only [literalCharge, literalCalendar, Finset.sum_filter]
  rw [heq]
  apply Finset.measurable_sum
  intro t _
  apply Measurable.ite (literalDateKept_borel rate rewards C_star C_h control0 t)
  · have hg : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
        ReferenceFirstCollectionRoundEndObservation.g rewards t.val z) := by
      exact (ReferenceFirstCollectionRoundEndObservation.g_stronglyMeasurable
        rewards control0 t.val).measurable.mono
          ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le _) le_rfl
    exact measurable_const.min hg
  · exact measurable_const

/-- Integrability follows by domination by the checked awaited waiting
charge under the unchanged source law. -/
theorem literalCharge_integrable (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (literalCharge rate rewards C_star C_h)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  exact (ReferenceFirstCollectionAwaitedWaitingCost.actual_first_collection_awaited_waiting_charge_integrable
    rate rewards C_star C_h control0).mono_nonneg
      (literalCharge_measurable rate rewards C_star C_h control0).aestronglyMeasurable
      (.of_forall fun z => (literalCharge_bounds rate rewards C_star C_h z).1)
      (.of_forall fun z => (literalCharge_bounds rate rewards C_star C_h z).2)

/-- Localized bound in exactly the awaited phase-start sigma algebra. It
makes no claim that its first support date is a source transfer start. -/
theorem literalCharge_setIntegral_bound
    (control0 : ContinuousLearningRows.TimeControl p)
    (Bset : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hBset : MeasurableSet[
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
        (ReferenceFirstCollectionAwaitedPhaseSupport.sigma
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h))
        (ReferenceFirstCollectionAwaitedPhaseSupport.sigma_is_pre_round_stopping_time
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0)] Bset) :
    (∫ z in Bset, literalCharge rate rewards C_star C_h z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) *
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real Bset := by
  calc
    _ ≤ ∫ z in Bset,
        ReferenceFirstCollectionAwaitedWaitingCost.actualFirstCollectionAwaitedWaitingCharge
          rate rewards C_star C_h z ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
      apply integral_mono_ae
        (literalCharge_integrable rate rewards C_star C_h control0).integrableOn
        (ReferenceFirstCollectionAwaitedWaitingCost.actual_first_collection_awaited_waiting_charge_integrable
          rate rewards C_star C_h control0).integrableOn
      exact .of_forall fun z => (literalCharge_bounds rate rewards C_star C_h z).2
    _ ≤ _ :=
      ReferenceFirstCollectionAwaitedWaitingCost.actual_first_collection_awaited_waiting_charge_setIntegral_bound
        rate rewards C_star C_h control0 Bset hBset

/-- Conditional bound in the same awaited phase-start field and original
source law. A source transfer-start field/tower assembly remains separate. -/
theorem literalCharge_condExp_bound (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[literalCharge rate rewards C_star C_h |
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
        (ReferenceFirstCollectionAwaitedPhaseSupport.sigma
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h))
        (ReferenceFirstCollectionAwaitedPhaseSupport.sigma_is_pre_round_stopping_time
          (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) control0)]
      ≤ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
        fun _ => ReferenceFirstCollectionAwaitedWaitingCost.Bcol (p := p) := by
  exact (condExp_mono
    (literalCharge_integrable rate rewards C_star C_h control0)
    (ReferenceFirstCollectionAwaitedWaitingCost.actual_first_collection_awaited_waiting_charge_integrable
      rate rewards C_star C_h control0)
    (.of_forall fun z => (literalCharge_bounds rate rewards C_star C_h z).2)).trans
      (ReferenceFirstCollectionAwaitedWaitingCost.actual_first_collection_awaited_waiting_charge_condExp_bound
        rate rewards C_star C_h control0)

end Actual

end Bandits.Support.ReferenceFirstCollectionLiteralStoppedCharge

end
