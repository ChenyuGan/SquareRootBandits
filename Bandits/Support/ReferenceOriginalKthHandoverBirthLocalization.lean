/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalFixedInstallationHandoverSupport
public import Bandits.Support.ReferenceOriginalKthBirthMarkLocalization

import Mathlib.Tactic

/-!
# Original ranked handover birth localization

The original ranked H dates agree, on the existing predictable birth mark,
with the literal fixed-installation pending support. Nonempty ranked H constructs
its own mark from the actual initial or later installation record. Both original
and capped support charges admit exact marked reindexing at every natural prefix;
the marked ranked-start event is measurable in the existing raw H-start field.

These internal structural results use the original ZIP4 phase definitions
(`05_binary_transport.tex:244-289`, `06_interruptions.tex:431-490,493-533`).
They supply no service, waiting, conditional-cost, or regret bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceOriginalKthHandoverBirthLocalization

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)


/-- The actual ranked H dates, cut down by the existing stopped transfer
window. -/
public def kthHDates (k : Fin (p.T + 1)) (z : SourceInput p) : Finset (Fin p.T) :=
  ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates rate rewards C_star C_h z k ∩
    ReferenceOriginalCalendarTransferPhaseCover.handoverPhaseDates rate rewards C_star C_h z

/-- The fixed-calendar H support dates from the original inclusive pending
mask. -/
public def fixedHDates (ell : Fin p.T) (z : SourceInput p) : Finset (Fin p.T) :=
  Finset.univ.filter fun t => ∃ i : Fin (p.m - 1),
    ReferenceOriginalFixedInstallationHandoverSupport.pending rate rewards C_star C_h ell t i z

/-- The original positive-arm charge on a ranked H prefix. -/
public def kthHChargePrefix (k : Fin (p.T + 1)) (v : ℕ) (z : SourceInput p) : ℝ :=
  ∑ t ∈ (kthHDates rate rewards C_star C_h k z).filter (fun t => t.val < v),
    (((ReferenceActualLiveEmptySignedRewardCalendar.positiveArms rewards t).card : ℕ) : ℝ)

/-- The capped original support charge on a ranked H prefix. -/
public def kthHCappedChargePrefix (k : Fin (p.T + 1)) (v : ℕ) (z : SourceInput p) : ℝ :=
  ∑ t ∈ (kthHDates rate rewards C_star C_h k z).filter (fun t => t.val < v),
    ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t

/-- The original positive-arm charge on a fixed-birth H prefix. -/
public def fixedHChargePrefix (ell : Fin p.T) (v : ℕ) (z : SourceInput p) : ℝ :=
  ∑ t ∈ (fixedHDates rate rewards C_star C_h ell z).filter (fun t => t.val < v),
    (((ReferenceActualLiveEmptySignedRewardCalendar.positiveArms rewards t).card : ℕ) : ℝ)

/-- The capped original support charge on a fixed-birth H prefix. -/
public def fixedHCappedChargePrefix (ell : Fin p.T) (v : ℕ) (z : SourceInput p) : ℝ :=
  ∑ t ∈ (fixedHDates rate rewards C_star C_h ell z).filter (fun t => t.val < v),
    ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t

/-- Every literal ranked birth mark identifies the same actual original
installation record and its payload; the raw H start is exactly the date
following that birth. -/
public theorem marked_installation_rawSigma
    (k : Fin (p.T + 1)) (ell : Fin p.T) (z : SourceInput p)
    (hmark : z ∈ ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell) :
    ∃ b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      ∃ payload : ReferenceActivePhysicalStep.Payload rate,
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val].input.time = ell ∧
        ReferenceAssignmentPayloadPersistence.InstallationBirth
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val]
          payload ∧
        ReferenceOriginalFixedInstallationHandoverSupport.installationBirthAt
          rate rewards C_star C_h ell z ∧
        ReferenceOriginalFixedInstallationHandoverSupport.rawSigma
          rate rewards C_star C_h ell z = ell.val + 1 := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  obtain ⟨b, payload, hbdate, hbirth, hbranch⟩ :=
    ReferenceOriginalKthBirthMarkLocalization.mark_actual_installation rate rewards C_star C_h k ell z hmark
  have htime : R[b.val].input.time = ell := by
    apply Fin.ext
    have := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
      rate rewards C_star C_h z b
    change R[b.val].input.time.val + 1 = s + b.val + 1 at this
    change s + b.val = ell.val at hbdate
    omega
  have hlookup :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h ell z = some R[b.val] := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
    have hval : R[b.val].input.time.val = ell.val := congrArg Fin.val htime
    have hs : s ≤ ell.val := by
      have hsource := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
        rate rewards C_star C_h z b
      change R[b.val].input.time.val + 1 = s + b.val + 1 at hsource
      change s + b.val = ell.val at hbdate
      omega
    rw [ite_eq_left hs]
    have hindex : ell.val - s = b.val := by
      change s + b.val = ell.val at hbdate
      omega
    rw [hindex]
    exact List.getElem?_eq_getElem b.isLt
  rcases hbranch with ⟨hbzero, hfirst, hstart, hkzero⟩ |
      ⟨hlater, hstart⟩
  · have hi : ReferenceOriginalFixedInstallationHandoverSupport.initialBirthAt rate rewards C_star C_h ell z :=
      (ReferenceOriginalFixedInstallationHandoverSupport.initialBirthAt_iff_actual_first rate rewards C_star C_h ell z).2
        ⟨R[b.val], hlookup, by simpa only [htime] using hfirst⟩
    have hraw : ReferenceOriginalFixedInstallationHandoverSupport.rawSigma
        rate rewards C_star C_h ell z = ell.val + 1 := by
      simp only [ReferenceOriginalFixedInstallationHandoverSupport.rawSigma,
      ReferenceOriginalFixedInstallationHandoverSupport.installationBirthAt,
      hi, true_or, ite_true]
    exact ⟨b, payload, htime, hbirth, Or.inl hi, hraw⟩
  · have hstate :=
      ReferenceCollectionPhaseHistory.laterChosen_pending_empty R[b.val].input hlater
    obtain ⟨oldPayload, ledger, saved, hcollection, hempty⟩ := hstate
    have hi : ReferenceOriginalFixedInstallationHandoverSupport.laterBirthAt rate rewards C_star C_h ell z := by
      refine ⟨b, ?_, htime, hlookup, oldPayload, ledger, saved, hcollection,
        hempty, payload, hbirth⟩
      change b.val = ell.val - s
      rw [← htime]
      omega
    have hraw : ReferenceOriginalFixedInstallationHandoverSupport.rawSigma
        rate rewards C_star C_h ell z = ell.val + 1 := by
      simp only [ReferenceOriginalFixedInstallationHandoverSupport.rawSigma,
      ReferenceOriginalFixedInstallationHandoverSupport.installationBirthAt,
      hi, or_true, ite_true]
    exact ⟨b, payload, htime, hbirth, Or.inr hi, hraw⟩

/-- The marked event is measurable in the raw stopped H-start field. Only the
intersection with the original ranked-start event is transported. -/
public theorem marked_event_at_rawSigma
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (ell : Fin p.T) (B0 : Set (SourceInput p))
    (hB0 : MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate rate rewards C_star C_h k)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
        rate rewards C_star C_h control0 k)] B0) :
    MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (ReferenceOriginalFixedInstallationHandoverSupport.rawSigma rate rewards C_star C_h ell)
      (ReferenceOriginalFixedInstallationHandoverSupport.rawSigma_preRoundStoppingTime rate rewards C_star C_h control0 ell)]
      (B0 ∩ ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell) := by
  let F0 := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let E := ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell
  let start := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate rate rewards C_star C_h k
  let sigma := ReferenceOriginalFixedInstallationHandoverSupport.rawSigma rate rewards C_star C_h ell
  have hE : MeasurableSet[F0 (ell.val + 1)] E :=
    ReferenceOriginalKthBirthMarkLocalization.mark_preRound_measurable rate rewards C_star C_h control0 k ell
  have hcut : MeasurableSet[F0 (ell.val + 1)]
      (B0 ∩ {z | start z ≤ ell.val + 1}) := by
    have hset : {z | (start z : WithTop ℕ) ≤ ((ell.val + 1 : ℕ) : WithTop ℕ)} =
        {z | start z ≤ ell.val + 1} := by
      ext z
      norm_cast
    have h := hB0.2 (ell.val + 1)
    change MeasurableSet[F0 (ell.val + 1)]
      (B0 ∩ {z | (start z : WithTop ℕ) ≤ ((ell.val + 1 : ℕ) : WithTop ℕ)}) at h
    rw [hset] at h
    exact h
  have horder : B0 ∩ {z | start z ≤ ell.val + 1} ∩ E = B0 ∩ E := by
    ext z
    constructor
    · rintro ⟨⟨hz, _⟩, he⟩
      exact ⟨hz, he⟩
    · rintro ⟨hz, he⟩
      exact ⟨⟨hz,
        ReferenceOriginalKthBirthMarkLocalization.markedStart_le_markedDate rate rewards C_star C_h k ell z he⟩, he⟩
  have hBE : MeasurableSet[F0 (ell.val + 1)] (B0 ∩ E) := by
    rw [← horder]
    exact hcut.inter hE
  change MeasurableSet[(PhaseStartConditionalWaiting.isStoppingTime_of_preRound
    F0 sigma (ReferenceOriginalFixedInstallationHandoverSupport.rawSigma_preRoundStoppingTime rate rewards C_star C_h control0 ell)).measurableSpace]
    (B0 ∩ E)
  refine ⟨le_iSup F0 (ell.val + 1) _ hBE, ?_⟩
  intro n
  change MeasurableSet[F0 n]
    ((B0 ∩ E) ∩ {z | (sigma z : WithTop ℕ) ≤ (n : WithTop ℕ)})
  have hset : {z | (sigma z : WithTop ℕ) ≤ (n : WithTop ℕ)} = {z | sigma z ≤ n} := by
    ext z
    norm_cast
  rw [hset]
  by_cases hn : ell.val + 1 ≤ n
  · exact (F0.mono hn _ hBE).inter
      (ReferenceOriginalFixedInstallationHandoverSupport.rawSigma_preRoundStoppingTime rate rewards C_star C_h control0 ell n)
  · have hempty : (B0 ∩ E) ∩ {z | sigma z ≤ n} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨hzBE, hz⟩
      obtain ⟨_, _, _, _, _, hraw⟩ :=
        marked_installation_rawSigma rate rewards C_star C_h k ell z hzBE.2
      change ReferenceOriginalFixedInstallationHandoverSupport.rawSigma
        rate rewards C_star C_h ell z ≤ n at hz
      rw [hraw] at hz
      omega
    rw [hempty]
    exact @MeasurableSet.empty (SourceInput p) (F0 n)

public theorem fixedHDate_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (ell t : Fin p.T) :
    MeasurableSet[(ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0) (t.val + 1)]
      {z : SourceInput p | t ∈ fixedHDates rate rewards C_star C_h ell z} := by
  classical
  have heq : {z : SourceInput p | t ∈ fixedHDates rate rewards C_star C_h ell z} =
      ⋃ i : Fin (p.m - 1),
        {z : SourceInput p | ReferenceOriginalFixedInstallationHandoverSupport.pending rate rewards C_star C_h ell t i z} := by
    ext z
    simp [fixedHDates]
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    ReferenceOriginalFixedInstallationHandoverSupport.pending_measurableSet rate rewards C_star C_h control0 ell t i

private theorem fixedHWeightedChargePrefix_integrable
    (ell : Fin p.T) (v : ℕ) (weight : Fin p.T → ℝ) :
    Integrable (fun z : SourceInput p =>
      ∑ t ∈ (fixedHDates rate rewards C_star C_h ell z).filter
        (fun t : Fin p.T => t.val < v), weight t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  classical
  let control0 : ContinuousLearningRows.TimeControl p :=
    (fun _ => ⟨0, by norm_num⟩, fun _ => (fun _ => 0, 0))
  let dates := Finset.univ.filter (fun t : Fin p.T => t.val < v)
  have hsum :
      (fun z : SourceInput p =>
        ∑ t ∈ (fixedHDates rate rewards C_star C_h ell z).filter
            (fun t : Fin p.T => t.val < v), weight t) =
        fun z => ∑ t ∈ dates,
          if t ∈ fixedHDates rate rewards C_star C_h ell z then weight t else 0 := by
    have hsets (z : SourceInput p) :
        (fixedHDates rate rewards C_star C_h ell z).filter
            (fun t : Fin p.T => t.val < v) =
          dates.filter (fun t => t ∈ fixedHDates rate rewards C_star C_h ell z) := by
      ext t
      simp [dates, and_comm]
    funext z
    classical
    rw [hsets z, Finset.sum_filter]
  have hExpanded : Integrable
      (fun z : SourceInput p => ∑ t ∈ dates,
        if t ∈ fixedHDates rate rewards C_star C_h ell z then weight t else 0)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
    apply integrable_finsetSum (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
      (s := dates)
    intro t ht
    let A : Set (SourceInput p) := {z | t ∈ fixedHDates rate rewards C_star C_h ell z}
    have hA : MeasurableSet A := by
      exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
        (t.val + 1) A (fixedHDate_measurable rate rewards C_star C_h control0 ell t)
    have hconst : Integrable (fun _ : SourceInput p =>
        weight t : SourceInput p → ℝ) (BootstrapPrivateRoundStreams.sourceInputLaw p) :=
      integrable_const _
    have hind := hconst.indicator hA
    have hterm : (fun z : SourceInput p =>
        if t ∈ fixedHDates rate rewards C_star C_h ell z then weight t else 0) =
        A.indicator (fun _ : SourceInput p => weight t) := by
      funext z
      simp [A, Set.indicator]
    rw [hterm]
    exact hind
  exact hsum ▸ hExpanded

public theorem fixedHChargePrefix_integrable
    (ell : Fin p.T) (v : ℕ) :
    Integrable (fixedHChargePrefix rate rewards C_star C_h ell v)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  unfold fixedHChargePrefix
  exact fixedHWeightedChargePrefix_integrable rate rewards C_star C_h ell v
    (fun t => (((ReferenceActualLiveEmptySignedRewardCalendar.positiveArms rewards t).card : ℕ) : ℝ))

public theorem fixedHCappedChargePrefix_integrable
    (ell : Fin p.T) (v : ℕ) :
    Integrable (fixedHCappedChargePrefix rate rewards C_star C_h ell v)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  unfold fixedHCappedChargePrefix
  exact fixedHWeightedChargePrefix_integrable rate rewards C_star C_h ell v
    (ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards)

/-- The capped fixed-calendar H charge is bounded by its original positive-arm
charge, using the exact rowwise `min(m, g_t)` envelope. -/
public theorem fixedHCappedChargePrefix_le
    (ell : Fin p.T) (v : ℕ) (z : SourceInput p) :
    fixedHCappedChargePrefix rate rewards C_star C_h ell v z ≤
      fixedHChargePrefix rate rewards C_star C_h ell v z := by
  classical
  unfold fixedHCappedChargePrefix fixedHChargePrefix
  apply Finset.sum_le_sum
  intro t ht
  exact min_le_right _ _

open ReferenceActivePhysicalStep ReferenceCollectionSegmentExtraction
open ReferenceOriginalInitialTransferWindowGeometry

local notation "R" z:arg => ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "S" z:arg => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "W" z:arg => rawInitialTransferWindow rate rewards C_star C_h z
local notation "HSupport" => ReferenceOriginalFixedInstallationHandoverSupport.pending

private theorem record_time (z : SourceInput p) (b : Fin (R z).length) :
    (R z)[b.val].input.time.val = S z + b.val := by
  have h := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
    rate rewards C_star C_h z b
  change (R z)[b.val].input.time.val + 1 = S z + b.val + 1 at h
  omega

private theorem record_lookup (z : SourceInput p) (b : Fin (R z).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (R z)[b.val].input.time z = some (R z)[b.val] := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [record_time rate rewards C_star C_h z b,
    ite_eq_left (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact List.getElem?_eq_getElem b.isLt

private theorem shifted_date_eq (d a q : ℕ) (hd : d + 1 = a + 1)
    (ha : a = q) : d = q := (Nat.succ.inj hd).trans ha

/-- The fixed H prefix has no new physical transfer start after its own
birth. This is a statement about the original contiguous record lists. -/
private theorem rawPending_no_new_start (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : SourceInput p)
    (hp : ReferenceOriginalFixedInstallationHandoverSupport.rawPending
      rate rewards C_star C_h ell t i z) :
    ∀ q : Fin p.T, ell.val < q.val → q.val ≤ t.val →
      ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h q z := by
  rcases hp with ⟨birth, _hb, _hf, _htb, hstart, j, _hj, ht, _⟩ |
    ⟨b, _hb, hbt, _hlookup, payload, ledger, saved, hc, he, _installed, _hinst,
      j, ht, _⟩
  · have hdate := (raw_window_record_calendar rate rewards C_star C_h z j).1
    change (W z)[j.val].input.time.val = S z + j.val at hdate
    rw [ht, hstart] at hdate
    intro q hq hqt
    let u : Fin (W z).length := ⟨q.val - ell.val, by have := j.isLt; omega⟩
    have hudate := (raw_window_record_calendar rate rewards C_star C_h z u).1
    have hu : (W z)[u.val].input.time = q := by
      apply Fin.ext
      change (W z)[u.val].input.time.val = S z + u.val at hudate
      have huval : S z + u.val = q.val := by dsimp only [u]; omega
      exact hudate.trans huval
    rw [← hu]
    exact raw_window_no_positive_transfer_start rate rewards C_star C_h z u
      (by dsimp only [u]; omega)
  · let V := (R z)[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let H := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
      rate rewards C_star C_h z b
    have hprefix : H.IsPrefix V := List.takeWhile_prefix _
    let jV : Fin V.length := ⟨j.val, lt_of_lt_of_le j.isLt hprefix.length_le⟩
    have hget : H[j.val] = V[jV.val] := hprefix.getElem j.isLt
    have hl := ReferenceOriginalFixedInstallationHandoverSupport.laterBirthAt_is_laterChosen
      rate rewards C_star C_h z b payload ledger saved hc he
    have hfields := ReferenceOriginalInstalledLiveStartExclusion.actual_later_installation_live_start_exclusion
      rate rewards C_star C_h z b hl
    have hdate := (hfields.1 jV).2.1
    have hbdate := record_time rate rewards C_star C_h z b
    rw [hbt] at hbdate
    change H[j.val].input.time = t at ht
    rw [← hget, ht] at hdate
    intro q hq hqt
    let u : Fin V.length := ⟨q.val - ell.val, by have := jV.isLt; omega⟩
    have hudate := (hfields.1 u).2.1
    have hu : V[u.val].input.time = q := by
      apply Fin.ext
      change V[u.val].input.time.val + 1 = S z + b.val + u.val + 1 at hudate
      have huval : S z + b.val + u.val = q.val := by
        rw [← hbdate]
        exact Nat.add_sub_of_le (Nat.le_of_lt hq)
      exact shifted_date_eq (V[u.val].input.time.val) (S z + b.val + u.val) q.val hudate huval
    rw [← hu]
    exact (hfields.1 u).2.2.2.2.2.2.2.2.2.2

private theorem pending_startCount (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : SourceInput p) (hp : HSupport rate rewards C_star C_h ell t i z) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
        rate rewards C_star C_h (ell.val + 1) z =
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
        rate rewards C_star C_h (t.val + 1) z := by
  have hle := (ReferenceOriginalFixedInstallationHandoverSupport.rawPending_actual_choice
    rate rewards C_star C_h ell t i z hp.2).1
  have hno := rawPending_no_new_start rate rewards C_star C_h ell t i z hp.2
  unfold ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
  congr 1
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hq, hdate⟩
    exact ⟨hq, by omega⟩
  · rintro ⟨hq, hdate⟩
    refine ⟨hq, ?_⟩
    by_contra hn
    exact hno q (by omega) (by omega) (Finset.mem_filter.mp hq).2.1

private theorem ranked_window_startCount (k : Fin (p.T + 1)) (t : Fin p.T)
    (z : SourceInput p)
    (ht : t ∈ ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates
      rate rewards C_star C_h z k) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
      rate rewards C_star C_h (t.val + 1) z = k.val + 1 := by
  have hbounds := (Finset.mem_filter.mp ht).2
  have hgt := (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
    rate rewards C_star C_h k (t.val + 1) (Nat.succ_le_of_lt t.isLt) z).mp hbounds.1
  have hcard : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
      rate rewards C_star C_h (t.val + 1) z ≤ p.T := by
    unfold ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin _)
  let next : Fin (p.T + 1) := ⟨k.val + 1, by omega⟩
  have hnext : ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h next z ≤ t.val + 1 := by
    intro hle
    have hE := Nat.min_le_left
      (ReferenceOriginalTransferPhysicalIntervals.nextStoppedTransferStartDate rate rewards C_star C_h k z)
      (min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) p.T + 1)
    change ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
      rate rewards C_star C_h k z ≤
        ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h next z at hE
    omega
  have hnlt := mt (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
    rate rewards C_star C_h next (t.val + 1) (Nat.succ_le_of_lt t.isLt) z).mpr hnext
  change ¬ k.val + 1 < _ at hnlt
  omega

/-- An actual fixed pending date inside the ranked window constructs the
existing predictable mark at its own birth, without a coverage premise. -/
public theorem pending_in_window_mark (k : Fin (p.T + 1)) (ell t : Fin p.T)
    (i : Fin (p.m - 1)) (z : SourceInput p)
    (hp : HSupport rate rewards C_star C_h ell t i z)
    (ht : t ∈ ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates
      rate rewards C_star C_h z k) :
    z ∈ ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell := by
  have ⟨hle, hbirth, _⟩ := ReferenceOriginalFixedInstallationHandoverSupport.rawPending_actual_choice
    rate rewards C_star C_h ell t i z hp.2
  have hcount := pending_startCount rate rewards C_star C_h ell t i z hp
  have hrank := ranked_window_startCount rate rewards C_star C_h k t z ht
  refine ⟨?_, by have := hp.1; omega, hcount.trans hrank⟩
  rcases hbirth with hi | hl
  · obtain ⟨r, hr, hf, _⟩ := hi
    exact Or.inl ((ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_iff_record_first
      rate rewards C_star C_h ell z).mpr ⟨r, hr, hf⟩)
  · obtain ⟨b, _hb, _htb, hr, payload, ledger, saved, hc, he, _⟩ := hl
    have hlater := ReferenceOriginalFixedInstallationHandoverSupport.laterBirthAt_is_laterChosen
      rate rewards C_star C_h z b payload ledger saved hc he
    exact Or.inr ((ReferencePostReplacementCollectionHandoverSourcePrefix.handoverIncomingData_collection_birth
      rate rewards C_star C_h z ell b payload ledger saved hr hc).mpr hlater)

private theorem count_mem_window (k : Fin (p.T + 1)) (t : Fin p.T)
    (z : SourceInput p)
    (hbad : t.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z)
    (hcount : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
      rate rewards C_star C_h (t.val + 1) z = k.val + 1) :
    t ∈ ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates
      rate rewards C_star C_h z k := by
  have hbound : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
      rate rewards C_star C_h (t.val + 1) z ≤ p.T := by
    unfold ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin _)
  let next : Fin (p.T + 1) := ⟨k.val + 1, by omega⟩
  have hnext : ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h next z ≤ t.val + 1 := by
    intro hn
    have hgt :=
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
        rate rewards C_star C_h next (t.val + 1) (Nat.succ_le_of_lt t.isLt) z).mp hn
    change k.val + 1 < _ at hgt
    omega
  have hnext' : t.val + 1 < ReferenceOriginalTransferPhysicalIntervals.nextStoppedTransferStartDate
      rate rewards C_star C_h k z := by
    change t.val + 1 <
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h next z
    omega
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · apply (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
      rate rewards C_star C_h k (t.val + 1) (Nat.succ_le_of_lt t.isLt) z).mpr
    rw [hcount]
    omega
  · unfold ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
    exact lt_min hnext' (by have ht := t.isLt; omega)

private theorem lookup_index (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    ∃ b : Fin (R z).length, (R z)[b.val] = r ∧ r.input.time = t := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split at hr
  next hs =>
    obtain ⟨hb, he⟩ := List.getElem?_eq_some_iff.mp hr
    let b : Fin (R z).length := ⟨t.val - S z, hb⟩
    refine ⟨b, he, ?_⟩
    have hdate := record_time rate rewards C_star C_h z b
    rw [he] at hdate
    apply Fin.ext
    exact hdate.trans (Nat.add_sub_of_le hs)
  next hs => cases hr

private theorem first_live_choice_none
    (x : RoundInput p rate)
    (hstate : x.state.coordinator = .first ∨
      ∃ r q base, x.state.coordinator = .live r q base)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = false) : choice x = none := by
  rcases hstate with hf | ⟨r, q, base, hl⟩
  · simp only [choice, (prepare x).coordinator_eq, dispatch_first x hf, choiceOfCut, ite_self]
  · have hd : (prepare x).coordinator =
        .live r q base (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
      simp only [(prepare x).coordinator_eq, dispatch, hl, CoordinatorRoundDispatch.dispatch]
      rfl
    unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
    unfold choice
    rw [hd] at hcut ⊢
    cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) <;>
      simp only [ho, choiceOfCut, ite_self, Bool.true_eq_false] at hcut ⊢

private theorem rawPending_choice_none (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : SourceInput p)
    (hp : ReferenceOriginalFixedInstallationHandoverSupport.rawPending
      rate rewards C_star C_h ell t i z) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      choice r.input = none := by
  rcases hp with ⟨_birth, _hb, _hf, _htb, _hstart, j, _hj, ht, _⟩ |
    ⟨b, _hb, _htb, _hlookup, payload, ledger, saved, hc, he, _installed, _hinst,
      j, ht, _⟩
  · refine ⟨(W z)[j.val], ht ▸ (raw_window_record_calendar rate rewards C_star C_h z j).2, ?_⟩
    obtain hempty | ⟨_hpos, _installed, _selected, _hs, _hi, _hp, _hempty, _hp0, hfields⟩ :=
      raw_initial_transfer_window_provenance rate rewards C_star C_h z
    · have := j.isLt; omega
    obtain ⟨_sel, _hsel, _hpay, hphase, _⟩ := hfields j
    have hstate : (W z)[j.val].input.state.coordinator = .first ∨
        ∃ r q base, (W z)[j.val].input.state.coordinator = .live r q base := by
      cases hc : (W z)[j.val].input.state.coordinator with
      | first => exact Or.inl rfl
      | live r q base => exact Or.inr ⟨r, q, base, rfl⟩
      | collection _ _ _ => simp only [List.get_eq_getElem, hc] at hphase
      | dagger => simp only [List.get_eq_getElem, hc] at hphase
    exact first_live_choice_none rate (W z)[j.val].input hstate
      (raw_window_no_collection_choice rate rewards C_star C_h z j)
  · let V := (R z)[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let H := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
      rate rewards C_star C_h z b
    have hprefix : H.IsPrefix V := List.takeWhile_prefix _
    let jV : Fin V.length := ⟨j.val, lt_of_lt_of_le j.isLt hprefix.length_le⟩
    have hget : H[j.val] = V[jV.val] := hprefix.getElem j.isLt
    have hl := ReferenceOriginalFixedInstallationHandoverSupport.laterBirthAt_is_laterChosen
      rate rewards C_star C_h z b payload ledger saved hc he
    refine ⟨H[j.val], ht ▸ ReferenceOriginalFixedInstallationHandoverSupport.actualHandover_actualRecord
      rate rewards C_star C_h z b j, ?_⟩
    rw [hget]
    exact ReferenceOriginalTransferPhysicalIntervals.actual_later_installation_no_collection_choice
      rate rewards C_star C_h z b hl jV

private theorem launch_date (z : SourceInput p) :
    ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z = S z + 1 := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hround := ReferenceCompletePhysicalHistory.no_launch_sentinel_round
        rate z rewards C_star C_h hlaunch
      have hstart := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
        rate z rewards C_star C_h hlaunch
      change ReferenceInitializationRun.launchRound
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) = _
      rw [hround, hstart]
  | some active =>
      have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate z rewards C_star C_h).isSome = true := by rw [hlaunch]; rfl
      have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp hsome
      have hcross' : (ReferenceInitializationRun.output
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)).crossing.isSome = true := by
        simpa [ReferenceCompletePhysicalHistory.generatedInput] using hcross
      change ReferenceInitializationRun.launchRound
          (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) =
        ReferenceInitializationRun.elapsed p
          (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).completed + 1
      unfold ReferenceInitializationRun.launchRound
      rw [hcross']
      rfl

private theorem pending_handover (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : SourceInput p) (hp : HSupport rate rewards C_star C_h ell t i z) :
    t ∈ ReferenceOriginalCalendarTransferPhaseCover.handoverPhaseDates rate rewards C_star C_h z := by
  obtain ⟨_hle, _hbirth, r, hr, selected, hs, hi⟩ :=
    ReferenceOriginalFixedInstallationHandoverSupport.rawPending_actual_choice
      rate rewards C_star C_h ell t i z hp.2
  obtain ⟨r', hr', hc⟩ := rawPending_choice_none rate rewards C_star C_h ell t i z hp.2
  have hrr : r' = r := Option.some.inj (hr'.symm.trans hr)
  subst r'
  obtain ⟨b, hb, htime⟩ := lookup_index rate rewards C_star C_h t z r hr
  have hphase := ReferenceOriginalCalendarTransferPhaseCover.actual_suffix_phase_availability
    rate rewards C_star C_h z b
  have hH : ReferenceOriginalCalendarTransferPhaseCover.actualHandoverSelection rate r := by
    change ReferenceOriginalCalendarTransferPhaseCover.actualCollectionChoice rate (R z)[b.val] ∨
      ReferenceOriginalCalendarTransferPhaseCover.actualHandoverSelection rate (R z)[b.val] ∨
      ReferenceOriginalCalendarTransferPhaseCover.actualReleaseSelection rate (R z)[b.val] at hphase
    rw [hb] at hphase
    rcases hphase with ⟨c, hchoice⟩ | hh | ⟨sel, hsel, _hlive, hempty⟩
    · rw [hc] at hchoice; cases hchoice
    · exact hh
    · have heq : sel = selected := Option.some.inj (hsel.symm.trans hs)
      subst sel
      rw [hempty] at hi
      exact (Finset.notMem_empty i hi).elim
  apply Finset.mem_image.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
  · change ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z ≤
        (R z)[b.val].input.time.val + 1 ∧
      (R z)[b.val].input.time.val + 1 ≤ min
        (ReferenceOriginalCalendarTransferPhaseCover.firstBadDate rate rewards C_star C_h z) p.T
    rw [launch_date rate rewards C_star C_h z, record_time rate rewards C_star C_h z b]
    have hdate := record_time rate rewards C_star C_h z b
    rw [hb, htime] at hdate
    change _ ≤ _ ∧ _ ≤ min
      (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) p.T
    exact ⟨by omega, le_min (by have := hp.1; omega) (by have := t.isLt; omega)⟩
  · change ReferenceOriginalCalendarTransferPhaseCover.actualHandoverSelection rate (R z)[b.val]
    exact hb ▸ hH
  · exact (congrArg (fun r => r.input.time) hb).trans htime

/-- The original marked fixed H support lies in the exact ranked H dates,
including the first detecting update and without a success condition. -/
public theorem marked_fixedHDates_subset (k : Fin (p.T + 1)) (ell : Fin p.T)
    (z : SourceInput p)
    (he : z ∈ ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell) :
    fixedHDates rate rewards C_star C_h ell z ⊆ kthHDates rate rewards C_star C_h k z := by
  intro t ht
  obtain ⟨i, hp⟩ := (Finset.mem_filter.mp ht).2
  apply Finset.mem_inter.mpr
  refine ⟨?_, pending_handover rate rewards C_star C_h ell t i z hp⟩
  apply count_mem_window rate rewards C_star C_h k t z hp.1
  exact (pending_startCount rate rewards C_star C_h ell t i z hp).symm.trans he.2.2

/-- Every actual ranked H date constructs the mark of its original
installation, from the selected pending set on the same physical record. -/
public theorem kthHDate_mark_pending (k : Fin (p.T + 1)) (t : Fin p.T)
    (z : SourceInput p) (ht : t ∈ kthHDates rate rewards C_star C_h k z) :
    ∃ ell : Fin p.T,
      z ∈ ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell ∧
      t ∈ fixedHDates rate rewards C_star C_h ell z := by
  obtain ⟨hwindow, hH⟩ := Finset.mem_inter.mp ht
  suffices ∃ (ell : Fin p.T) (i : Fin (p.m - 1)),
      HSupport rate rewards C_star C_h ell t i z by
    obtain ⟨ell, i, hp⟩ := this
    exact ⟨ell, pending_in_window_mark rate rewards C_star C_h k ell t i z hp hwindow,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hp⟩⟩
  obtain ⟨q, hq, hqt⟩ := Finset.mem_image.mp hH
  have hqR : q.val < (R z).length := q.isLt
  change (R z)[q.val].input.time = t at hqt
  have hphase : ReferenceOriginalCalendarTransferPhaseCover.actualHandoverSelection rate (R z)[q.val] :=
    (Finset.mem_filter.mp hq).2.2
  have hbad : t.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h z := by
    have hret := (Finset.mem_filter.mp hq).2.1.2
    change (R z)[q.val].input.time.val + 1 ≤ min
      (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) p.T at hret
    rw [hqt] at hret
    exact hret.trans (min_le_left _ _)
  have hbounds := (Finset.mem_filter.mp hwindow).2
  have hqdate := record_time rate rewards C_star C_h z q
  rw [hqt] at hqdate
  have hk : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ p.T := by have := t.isLt; omega
  obtain ⟨a, ha, hbranch⟩ :=
    ReferenceOriginalStoppedTransferPhaseIntervals.present_stopped_transfer_collection_intervals
      rate rewards C_star C_h k z hk
  rcases hbranch with ⟨hazero, hafirst, _hchoice⟩ |
    ⟨registers, owned, base, seg, _hstate, _hseg, _hentry, _hpay, _hne,
      hCfields, _hClookups, _hCdates, hboundary⟩
  · have hstart : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z = S z + 1 := by
      change _ = S z + a.val + 1 at ha
      simpa only [hazero, Nat.add_zero] using ha
    obtain ⟨_hW, _hE, _hclip, hglobal, _payload, _hpayload, hfields, _⟩ :=
      ReferenceOriginalStoppedTransferPhaseIntervals.initial_rank_stopped_transfer_phase_intervals
        rate rewards C_star C_h k z hk hstart
    have hqW : q.val < (W z).length :=
      ((hglobal q).mp (by rw [hqt]; exact hbounds.2)).1
    let j : Fin (W z).length := ⟨q.val, hqW⟩
    have hslot := (hfields j).1
    change (R z)[q.val]? = some (W z)[j.val] at hslot
    rw [List.getElem?_eq_getElem hqR] at hslot
    have hget : (R z)[q.val] = (W z)[j.val] := Option.some.inj hslot
    obtain ⟨selected, hsel, _hpay, hmissing, _⟩ := (hfields j).2.2.2.2
    have hphaseW : ReferenceOriginalCalendarTransferPhaseCover.actualHandoverSelection rate (W z)[j.val] :=
      hget ▸ hphase
    obtain ⟨selectedH, hselH, _hliveH, hpendH⟩ := hphaseW
    have heq : selectedH = selected := Option.some.inj (hselH.symm.trans hsel)
    subst selectedH
    have hj : j.val < rawMissingPrefixLength rate rewards C_star C_h z := hmissing.mp hpendH
    obtain ⟨i, hi⟩ := hpendH
    let ell := (R z)[a.val].input.time
    have hell : S z = ell.val := by
      have hd := record_time rate rewards C_star C_h z a
      change ell.val = S z + a.val at hd
      omega
    refine ⟨ell, i, hbad, Or.inl ⟨(R z)[a.val],
      record_lookup rate rewards C_star C_h z a, hafirst, rfl, hell, j, hj, ?_⟩⟩
    exact ⟨hget ▸ hqt, selected, hsel, hi⟩
  · have haq : a.val ≤ q.val := by
      change _ = S z + a.val + 1 at ha
      omega
    rcases hboundary with ⟨_hterminal, _hE, hchoices, _habsent⟩ |
      ⟨b, hb, hlater, _hexit, ⟨saved, hcoord⟩, hempty, _hlen, _hE, _hclip,
        hglobal, newPayload, hbirth, hfields, _hlookups, _hHdates, _⟩
    · have hc := hchoices q haq
      have hsome : ∃ c, choice (R z)[q.val].input = some c := Option.isSome_iff_exists.mp hc
      exact (ReferenceOriginalCalendarTransferPhaseCover.actual_suffix_collection_handover_disjoint
        rate rewards C_star C_h z q ⟨hsome, hphase⟩).elim
    · have hqb : b.val ≤ q.val := by
        by_contra hn
        let j : Fin seg.records.length := ⟨q.val - a.val, by omega⟩
        have hslot := (hCfields j).1
        have hindex : a.val + j.val = q.val := by dsimp only [j]; omega
        rw [hindex, List.getElem?_eq_getElem hqR] at hslot
        have hget : (R z)[q.val] = seg.records[j.val] := Option.some.inj hslot
        obtain ⟨c, hc, _⟩ := (hCfields j).2.2
        have hsome : ∃ c, choice (R z)[q.val].input = some c := ⟨c, hget ▸ hc⟩
        exact ReferenceOriginalCalendarTransferPhaseCover.actual_suffix_collection_handover_disjoint
          rate rewards C_star C_h z q ⟨hsome, hphase⟩
      let V := (R z)[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (b.val + 1)
      have hqV : q.val < b.val + V.length :=
        ((hglobal q).mp ⟨haq, by rw [hqt]; exact hbounds.2⟩).2.1
      let j : Fin V.length := ⟨q.val - b.val, by omega⟩
      have hslot := (hfields j).1
      have hindex : b.val + j.val = q.val := by dsimp only [j]; omega
      rw [hindex, List.getElem?_eq_getElem hqR] at hslot
      have hget : (R z)[q.val] = V[j.val] := Option.some.inj hslot
      obtain ⟨selected, hsel, _hpay, hmissing, _⟩ := (hfields j).2.2.2
      have hphaseV : ReferenceOriginalCalendarTransferPhaseCover.actualHandoverSelection rate V[j.val] :=
        hget ▸ hphase
      obtain ⟨selectedH, hselH, _hliveH, hpendH⟩ := hphaseV
      have heq : selectedH = selected := Option.some.inj (hselH.symm.trans hsel)
      subst selectedH
      let H := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
        rate rewards C_star C_h z b
      have hj : j.val < H.length := hmissing.mp hpendH
      let jH : Fin H.length := ⟨j.val, hj⟩
      have hprefix : H.IsPrefix V := List.takeWhile_prefix _
      have hgetH : H[jH.val] = V[j.val] := hprefix.getElem jH.isLt
      obtain ⟨i, hi⟩ := hpendH
      let ell := (R z)[b.val].input.time
      have hindexb : b.val = ell.val - S z := by
        have hd := record_time rate rewards C_star C_h z b
        change ell.val = S z + b.val at hd
        omega
      refine ⟨ell, i, hbad, Or.inr ⟨b, hindexb, rfl,
        record_lookup rate rewards C_star C_h z b, registers.payload, seg.final,
        saved, hcoord, hempty, newPayload, hbirth, jH, ?_⟩⟩
      change H[jH.val].input.time = t ∧ ∃ selected : Selection H[jH.val].input,
        H[jH.val].output.preparation.coordinator.selection = some selected ∧
          i ∈ selected.view.pendingAtChoice
      rw [hgetH]
      exact ⟨hget ▸ hqt, selected, hsel, hi⟩

/-- Exact full H-date localization on the existing birth mark, including
empty handover phases. -/
public theorem marked_dates_eq (k : Fin (p.T + 1)) (ell : Fin p.T)
    (z : SourceInput p)
    (he : z ∈ ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell) :
    kthHDates rate rewards C_star C_h k z = fixedHDates rate rewards C_star C_h ell z := by
  apply Finset.Subset.antisymm
  · intro t ht
    obtain ⟨ell', he', hfixed⟩ := kthHDate_mark_pending rate rewards C_star C_h k t z ht
    have heq : ell' = ell := by
      by_contra hn
      exact Set.disjoint_left.mp
        (ReferenceOriginalKthBirthMarkLocalization.marks_disjoint rate rewards C_star C_h k ell' ell hn) he' he
    simpa only [heq] using hfixed
  · exact marked_fixedHDates_subset rate rewards C_star C_h k ell z he

/-- Nonempty actual H constructs its own literal predictable birth mark. -/
public theorem nonempty_handover_mark (k : Fin (p.T + 1)) (z : SourceInput p)
    (hne : (kthHDates rate rewards C_star C_h k z).Nonempty) :
    ∃ ell : Fin p.T,
      z ∈ ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell ∧
      kthHDates rate rewards C_star C_h k z = fixedHDates rate rewards C_star C_h ell z := by
  obtain ⟨t, ht⟩ := hne
  obtain ⟨ell, he, _⟩ := kthHDate_mark_pending rate rewards C_star C_h k t z ht
  exact ⟨ell, he, marked_dates_eq rate rewards C_star C_h k ell z he⟩

public theorem no_mark_handover_empty (k : Fin (p.T + 1)) (z : SourceInput p)
    (hz : ∀ ell : Fin p.T,
      z ∉ ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell) :
    kthHDates rate rewards C_star C_h k z = ∅ := by
  by_contra hn
  obtain ⟨ell, he, _⟩ := nonempty_handover_mark rate rewards C_star C_h k z
    (Finset.nonempty_iff_ne_empty.mpr hn)
  exact hz ell he

private theorem weighted_prefix_mark_reindex (k : Fin (p.T + 1)) (v : ℕ)
    (z : SourceInput p) (weight : Fin p.T → ℝ) :
    (∑ t ∈ (kthHDates rate rewards C_star C_h k z).filter (fun t => t.val < v), weight t) =
      ∑ ell : Fin p.T,
        (ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell).indicator
          (fun z => ∑ t ∈ (fixedHDates rate rewards C_star C_h ell z).filter
            (fun t => t.val < v), weight t) z := by
  by_cases hex : ∃ ell : Fin p.T,
      z ∈ ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell
  · obtain ⟨ell, he⟩ := hex
    rw [marked_dates_eq rate rewards C_star C_h k ell z he]
    symm
    calc
      _ = (ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell).indicator
          (fun z => ∑ t ∈ (fixedHDates rate rewards C_star C_h ell z).filter
            (fun t => t.val < v), weight t) z := by
        apply Finset.sum_eq_single ell
        · intro l _hl hne
          apply Set.indicator_of_notMem
          intro hl
          exact Set.disjoint_left.mp
            (ReferenceOriginalKthBirthMarkLocalization.marks_disjoint rate rewards C_star C_h k l ell hne) hl he
        · intro hn
          exact (hn (Finset.mem_univ ell)).elim
      _ = _ := Set.indicator_of_mem he _
  · have hnone : ∀ ell : Fin p.T,
        z ∉ ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell := by
      intro ell he
      exact hex ⟨ell, he⟩
    rw [no_mark_handover_empty rate rewards C_star C_h k z hnone,
      Finset.filter_empty, Finset.sum_empty]
    symm
    apply Finset.sum_eq_zero
    intro ell _hell
    exact Set.indicator_of_notMem (hnone ell) _

/-- Exact finite marked reindex for the original positive-arm charge, for
all natural prefix endpoints. -/
public theorem chargePrefix_mark_reindex (k : Fin (p.T + 1)) (v : ℕ) (z : SourceInput p) :
    kthHChargePrefix rate rewards C_star C_h k v z =
      ∑ ell : Fin p.T,
        (ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell).indicator
          (fixedHChargePrefix rate rewards C_star C_h ell v) z := by
  exact weighted_prefix_mark_reindex rate rewards C_star C_h k v z
    (fun t => (((ReferenceActualLiveEmptySignedRewardCalendar.positiveArms rewards t).card : ℕ) : ℝ))

/-- Exact finite marked reindex for the existing capped support envelope,
with the same birth marks and the same whole rounded reward rows. -/
public theorem cappedChargePrefix_mark_reindex (k : Fin (p.T + 1)) (v : ℕ) (z : SourceInput p) :
    kthHCappedChargePrefix rate rewards C_star C_h k v z =
      ∑ ell : Fin p.T,
        (ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell).indicator
          (fixedHCappedChargePrefix rate rewards C_star C_h ell v) z := by
  exact weighted_prefix_mark_reindex rate rewards C_star C_h k v z
    (ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards)

private theorem mark_measurable (k : Fin (p.T + 1)) (ell : Fin p.T) :
    MeasurableSet
      (ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell) := by
  let control0 : ContinuousLearningRows.TimeControl p :=
    (fun _ => ⟨0, by norm_num⟩, fun _ => (fun _ => 0, 0))
  exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
    (ell.val + 1) _
    (ReferenceOriginalKthBirthMarkLocalization.mark_preRound_measurable
      rate rewards C_star C_h control0 k ell)

/-- Literal ranked H membership is a finite union of measurable marked
fixed-calendar H memberships. -/
public theorem kthHDate_measurable (k : Fin (p.T + 1)) (t : Fin p.T) :
    MeasurableSet {z : SourceInput p | t ∈ kthHDates rate rewards C_star C_h k z} := by
  let control0 : ContinuousLearningRows.TimeControl p :=
    (fun _ => ⟨0, by norm_num⟩, fun _ => (fun _ => 0, 0))
  have hset : {z : SourceInput p | t ∈ kthHDates rate rewards C_star C_h k z} =
      ⋃ ell : Fin p.T,
        ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell ∩
          {z | t ∈ fixedHDates rate rewards C_star C_h ell z} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · exact kthHDate_mark_pending rate rewards C_star C_h k t z
    · rintro ⟨ell, he, ht⟩
      exact marked_fixedHDates_subset rate rewards C_star C_h k ell z he ht
  rw [hset]
  apply MeasurableSet.iUnion
  intro ell
  apply (mark_measurable rate rewards C_star C_h k ell).inter
  exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
    (t.val + 1) _ (fixedHDate_measurable rate rewards C_star C_h control0 ell t)

private theorem kthHWeightedChargePrefix_integrable
    (k : Fin (p.T + 1)) (v : ℕ) (weight : Fin p.T → ℝ) :
    Integrable (fun z : SourceInput p =>
      ∑ t ∈ (kthHDates rate rewards C_star C_h k z).filter
        (fun t : Fin p.T => t.val < v), weight t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hsum : (fun z : SourceInput p =>
      ∑ t ∈ (kthHDates rate rewards C_star C_h k z).filter
        (fun t : Fin p.T => t.val < v), weight t) =
      fun z => ∑ ell : Fin p.T,
        (ReferenceOriginalKthBirthMarkLocalization.kthBirthMark rate rewards C_star C_h k ell).indicator
          (fun z => ∑ t ∈ (fixedHDates rate rewards C_star C_h ell z).filter
            (fun t => t.val < v), weight t) z := by
    funext z
    exact weighted_prefix_mark_reindex rate rewards C_star C_h k v z weight
  rw [hsum]
  apply integrable_finsetSum
  intro ell _hell
  exact (fixedHWeightedChargePrefix_integrable rate rewards C_star C_h ell v weight).indicator
    (mark_measurable rate rewards C_star C_h k ell)

public theorem kthHChargePrefix_integrable (k : Fin (p.T + 1)) (v : ℕ) :
    Integrable (kthHChargePrefix rate rewards C_star C_h k v)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  exact kthHWeightedChargePrefix_integrable rate rewards C_star C_h k v
    (fun t => (((ReferenceActualLiveEmptySignedRewardCalendar.positiveArms rewards t).card : ℕ) : ℝ))

public theorem kthHCappedChargePrefix_integrable (k : Fin (p.T + 1)) (v : ℕ) :
    Integrable (kthHCappedChargePrefix rate rewards C_star C_h k v)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  exact kthHWeightedChargePrefix_integrable rate rewards C_star C_h k v
    (ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards)

/-- Integrability of the actual full original ranked H charge. -/
public theorem kthHCharge_integrable (k : Fin (p.T + 1)) :
    Integrable (fun z : SourceInput p =>
      ∑ t ∈ kthHDates rate rewards C_star C_h k z,
        (((ReferenceActualLiveEmptySignedRewardCalendar.positiveArms rewards t).card : ℕ) : ℝ))
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hfilter (z : SourceInput p) :
      (kthHDates rate rewards C_star C_h k z).filter (fun t => t.val < p.T) =
        kthHDates rate rewards C_star C_h k z :=
    Finset.filter_true_of_mem (fun t _ => t.isLt)
  have heq : (fun z : SourceInput p =>
      ∑ t ∈ kthHDates rate rewards C_star C_h k z,
        (((ReferenceActualLiveEmptySignedRewardCalendar.positiveArms rewards t).card : ℕ) : ℝ)) =
      kthHChargePrefix rate rewards C_star C_h k p.T := by
    funext z
    simp only [kthHChargePrefix, hfilter]
  rw [heq]
  exact kthHChargePrefix_integrable rate rewards C_star C_h k p.T

public theorem kthHCappedCharge_integrable (k : Fin (p.T + 1)) :
    Integrable (fun z : SourceInput p =>
      ∑ t ∈ kthHDates rate rewards C_star C_h k z,
        ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hfilter (z : SourceInput p) :
      (kthHDates rate rewards C_star C_h k z).filter (fun t => t.val < p.T) =
        kthHDates rate rewards C_star C_h k z :=
    Finset.filter_true_of_mem (fun t _ => t.isLt)
  have heq : (fun z : SourceInput p =>
      ∑ t ∈ kthHDates rate rewards C_star C_h k z,
        ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t) =
      kthHCappedChargePrefix rate rewards C_star C_h k p.T := by
    funext z
    simp only [kthHCappedChargePrefix, hfilter]
  rw [heq]
  exact kthHCappedChargePrefix_integrable rate rewards C_star C_h k p.T

public theorem kthHCappedChargePrefix_le (k : Fin (p.T + 1)) (v : ℕ) (z : SourceInput p) :
    kthHCappedChargePrefix rate rewards C_star C_h k v z ≤
      kthHChargePrefix rate rewards C_star C_h k v z := by
  unfold kthHCappedChargePrefix kthHChargePrefix
  apply Finset.sum_le_sum
  intro t _ht
  exact min_le_right _ _

end Bandits.Support.ReferenceOriginalKthHandoverBirthLocalization

end
