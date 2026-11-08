/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalKthReleaseSignedChargeLocalization
public import Bandits.Support.ReferenceOriginalKthCollectionCutoffAlignment

import Mathlib.Tactic

/-!
# Finite birth marks for the original ranked stopped release

The mark records the actual initial or incoming collection-birth tag, its
inclusive survival through the first bad date, and the exact stopped-start
count at that date. The signed prefix retains every supported fixed-label
release deficit, including supported dates with empty pending sets.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open MeasureTheory
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceOriginalKthBirthMarkLocalization

local instance kthBirthMarkOptionMeasurableSpace {Y : Type*} [MeasurableSpace Y] :
    MeasurableSpace (Option Y) :=
  Bandits.Support.LaterAssignmentStartMeasurability.optionMeasurableSpace

private theorem measurableSet_option_singleton {Y : Type*}
    [MeasurableSpace Y] [MeasurableSingletonClass Y] (a : Option Y) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace] {a} := by
  let e := Equiv.optionEquivSumPUnit Y
  have he : @Measurable (Option Y) (Y ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e :=
    comap_measurable _
  have hset : ({a} : Set (Option Y)) = e ⁻¹' {e a} := by
    ext x
    exact ⟨congrArg e, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e a with
  | inl value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inr_image (α := Y)

local instance {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y] :
    @MeasurableSingletonClass (Option Y)
      LaterAssignmentStartMeasurability.optionMeasurableSpace :=
  ⟨measurableSet_option_singleton⟩

abbrev Parameters := ConstructorDimensions.Parameters
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The literal finite birth mark for the original `k`th stopped transfer.
The incoming tag is read before sampling the newly installed payload. -/
public def kthBirthMark (k : Fin (p.T + 1)) (ell : Fin p.T) : Set (SourceInput p) :=
  {z | (ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
        rate rewards C_star C_h ell z ∨
      ReferencePostReplacementCollectionHandoverSourcePrefix.handoverIncomingData
        rate rewards C_star C_h ell z = some (true, none)) ∧
    ell.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
      rate rewards C_star C_h z ∧
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
      rate rewards C_star C_h (ell.val + 1) z = k.val + 1}

/-- The finite original signed prefix at a fixed release label. Only the
original stopped release support masks the signed deficit. -/
public def fixedSignedPrefix (ell : Fin p.T) (v : ℕ) : SourceInput p → ℝ :=
  fun z =>
    ∑ t ∈ Finset.univ.filter (fun t : Fin p.T => t.val < v),
      if ReferenceOriginalInstallationStoppedReleasePhase.supportAt
          rate rewards C_star C_h ell.val t.val z then
        ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
          rate rewards C_star C_h ell.val t z
      else 0

private theorem stoppedStartCountThrough_prefix_factor
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (z : SourceInput p) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
        rate rewards C_star C_h n z =
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
        rate rewards C_star C_h n
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n - 1) z) := by
  classical
  unfold ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartRounds
  apply congrArg Finset.card
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨hstart, hdate⟩ <;> refine ⟨?_, hdate⟩
  · have hfactor := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartAt_prefix_factor
      rate rewards C_star C_h control0 q z
    have hfactor' := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartAt_prefix_factor
      rate rewards C_star C_h control0 q
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n - 1) z)
    have hq : q.val ≤ n - 1 := by omega
    have hzq := hfactor.mp hstart
    rw [← ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
      control0 q.val (n - 1) hq z] at hzq
    exact hfactor'.mpr hzq
  · have hfactor := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartAt_prefix_factor
      rate rewards C_star C_h control0 q
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (n - 1) z)
    have hfactor' := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartAt_prefix_factor
      rate rewards C_star C_h control0 q z
    have hq : q.val ≤ n - 1 := by omega
    have hpref := hfactor.mp hstart
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
      control0 q.val (n - 1) hq z] at hpref
    exact hfactor'.mpr hpref

private theorem measurable_optionElim {α : Type*} {β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance
      (Equiv.optionEquivSumPUnit α))
    (f : α → β) (b : β) (hf : Measurable f) :
    @Measurable (Option α) β LaterAssignmentStartMeasurability.optionMeasurableSpace
      inferInstance (fun o => o.elim b f) := by
  let e := Equiv.optionEquivSumPUnit α
  have hs : Measurable (Sum.elim f (fun _ : PUnit => b)) := hf.sumElim measurable_const
  have hfun : (fun o : Option α => o.elim b f) = Sum.elim f (fun _ : PUnit => b) ∘ e := by
    funext o
    cases o <;> rfl
  rw [hfun]
  exact hs.comp he

private theorem measurable_firstFlagCode :
    Measurable (fun code : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate =>
      match code with | .inl _ => true | .inr _ => false) := by
  let f : Unit → Bool := fun _ => true
  let g : ((ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ⊕
      ((ReferenceActivePhysicalStep.Payload rate ×
        (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit)) → Bool :=
    fun _ => false
  change Measurable (Sum.elim f g)
  exact measurable_const.sumElim measurable_const

private theorem incomingFirstFlag_measurable :
    Measurable (fun code : Option
      (ReferenceActivePhysicalStepMeasurability.StateCode p rate) =>
        code.elim false fun c => match c.1 with
          | .inl _ => true
          | .inr _ => false) := by
  exact measurable_optionElim (comap_measurable _)
    (fun c : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
      match c.1 with | .inl _ => true | .inr _ => false) false
    (measurable_firstFlagCode (p := p) (rate := rate) |>.comp measurable_fst)

private theorem initialMarker_iff_incomingFirstFlag
    (ell : Fin p.T) (z : SourceInput p) :
    ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
        rate rewards C_star C_h ell z ↔
      (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h ell z).elim
        false (fun code => match code.1 with | .inl _ => true | .inr _ => false) = true := by
  rw [ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_iff_record_first]
  constructor
  · rintro ⟨record, hr, hfirst⟩
    change ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h ell z = some record at hr
    simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr,
      ReferenceActivePhysicalStepMeasurability.encodeState,
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hfirst]
  · intro hflag
    cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h ell z with
    | none =>
        simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr] at hflag
    | some record =>
        cases hcoord : record.input.state.coordinator with
        | first => exact ⟨record, hr, hcoord⟩
        | live registers owned base =>
            simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr,
              ReferenceActivePhysicalStepMeasurability.encodeState,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hcoord] at hflag
        | collection payload ledger saved =>
            simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr,
              ReferenceActivePhysicalStepMeasurability.encodeState,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hcoord] at hflag
        | dagger =>
            simp [ReferenceSourcePrefixHistoryFiltration.incoming, hr,
              ReferenceActivePhysicalStepMeasurability.encodeState,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hcoord] at hflag

private theorem initialMarker_prefix_factor
    (control0 : ContinuousLearningRows.TimeControl p) (ell : Fin p.T)
    (z : SourceInput p) :
    ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
        rate rewards C_star C_h ell z ↔
      ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
        rate rewards C_star C_h ell
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 ell.val z) := by
  rw [initialMarker_iff_incomingFirstFlag, initialMarker_iff_incomingFirstFlag,
    ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 ell z]

private theorem stoppedStartCountThrough_preRound_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (ell : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (ell.val + 1)]
      {z : SourceInput p |
        ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
          rate rewards C_star C_h (ell.val + 1) z = k.val + 1} := by
  let n := ell.val + 1
  by_cases hk : k.val < p.T
  · let kNext : Fin (p.T + 1) := ⟨k.val + 1, by omega⟩
    have hn : n ≤ p.T := by dsimp [n]; omega
    have hcount (z : SourceInput p) :
        ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
            rate rewards C_star C_h n z = k.val + 1 ↔
          ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
              rate rewards C_star C_h k z ≤ n ∧
            ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
              rate rewards C_star C_h kNext z ≤ n := by
      have hdate := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
        rate rewards C_star C_h k n hn z
      have hnext := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
        rate rewards C_star C_h kNext n hn z
      constructor
      · intro hc
        have hlt : k.val <
            ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
              rate rewards C_star C_h n z := by omega
        have hnlt : ¬ k.val + 1 <
            ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
              rate rewards C_star C_h n z := by omega
        exact ⟨hdate.mpr hlt, fun h => by
          have hle := hnext.mp h
          dsimp [kNext] at hle
          omega⟩
      · rintro ⟨hdate', hnext'⟩
        have hlt := hdate.mp hdate'
        have hnlt : ¬ k.val + 1 <
            ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
              rate rewards C_star C_h n z := by
          intro h
          have hle := hnext.mpr h
          dsimp [kNext] at hle
          exact hnext' hle
        omega
    have hset :
        {z : SourceInput p |
          ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
            rate rewards C_star C_h n z = k.val + 1} =
        {z | ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
            rate rewards C_star C_h k z ≤ n} ∩
          {z | ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
            rate rewards C_star C_h kNext z ≤ n} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      exact hcount z
    rw [hset]
    have hτ := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
      rate rewards C_star C_h control0 k
    have hτNext := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
      rate rewards C_star C_h control0 kNext
    exact (hτ n).inter (hτNext n).compl
  · have hkval : k.val = p.T := by omega
    have hbound (z : SourceInput p) :
        ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
          rate rewards C_star C_h n z ≤ p.T := by
      calc
        _ = ((ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDates
            rate rewards C_star C_h z).filter (fun d => d ≤ n)).card :=
          (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDates_filter_card_eq_count
            rate rewards C_star C_h n z).symm
        _ ≤ (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDates
            rate rewards C_star C_h z).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ ≤ p.T :=
          ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDates_card_le_horizon
            rate rewards C_star C_h z
    have hset :
        {z : SourceInput p |
          ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
            rate rewards C_star C_h n z = k.val + 1} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      constructor
      · intro h
        have := hbound z
        omega
      · intro h
        cases h
    rw [hset]
    exact @MeasurableSet.empty (SourceInput p)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (ell.val + 1))

/-- The mark is unchanged when the source is replaced by its strict prefix
before the marked original date. -/
public theorem mark_prefix_factor
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (ell : Fin p.T) (z : SourceInput p) :
    z ∈ kthBirthMark rate rewards C_star C_h k ell ↔
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 ell.val z ∈
        kthBirthMark rate rewards C_star C_h k ell := by
  simp only [kthBirthMark, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨htag, hbad, hcount⟩
    refine ⟨?_, ?_, ?_⟩
    · rcases htag with hfirst | hhandover
      · exact Or.inl ((initialMarker_prefix_factor rate rewards C_star C_h control0 ell z).mp hfirst)
      · rw [ReferencePostReplacementCollectionHandoverSourcePrefix.handoverIncomingData_factor
          rate rewards C_star C_h control0 ell z] at hhandover
        exact Or.inr hhandover
    · exact (ReferenceOriginalFirstBadStrictPrefix.firstBadDate_inclusive_prefix_factor
        rate rewards C_star C_h control0 ell z).mp hbad
    · have h := stoppedStartCountThrough_prefix_factor rate rewards C_star C_h
        control0 (ell.val + 1) z
      rw [h] at hcount
      simpa using hcount
  · rintro ⟨htag, hbad, hcount⟩
    refine ⟨?_, ?_, ?_⟩
    · rcases htag with hfirst | hhandover
      · exact Or.inl ((initialMarker_prefix_factor rate rewards C_star C_h control0 ell z).mpr hfirst)
      · rw [ReferencePostReplacementCollectionHandoverSourcePrefix.handoverIncomingData_factor
          rate rewards C_star C_h control0 ell z]
        exact Or.inr hhandover
    · exact (ReferenceOriginalFirstBadStrictPrefix.firstBadDate_inclusive_prefix_factor
        rate rewards C_star C_h control0 ell z).mpr hbad
    · have h := stoppedStartCountThrough_prefix_factor rate rewards C_star C_h
        control0 (ell.val + 1) z
      rw [h]
      simpa using hcount

/-- The mark is measurable at the exact pre-round source field following its
tag date. -/
public theorem mark_preRound_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (ell : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (ell.val + 1)] (kthBirthMark rate rewards C_star C_h k ell) := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
    (ell.val + 1)
  have hfirst : MeasurableSet[F]
      {z : SourceInput p |
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h ell z).elim
          false (fun code => match code.1 with | .inl _ => true | .inr _ => false) = true} := by
    exact (measurableSet_singleton true).preimage
      ((incomingFirstFlag_measurable (p := p) (rate := rate)).comp
        (ReferenceSourcePrefixHistoryFiltration.incoming_measurable
          rate rewards C_star C_h control0 ell))
  have hmarker : MeasurableSet[F]
      {z : SourceInput p |
        ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
          rate rewards C_star C_h ell z} := by
    have heq :
        {z : SourceInput p |
          ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
            rate rewards C_star C_h ell z} =
        {z : SourceInput p |
          (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h ell z).elim
            false (fun code => match code.1 with | .inl _ => true | .inr _ => false) = true} := by
      ext z
      exact initialMarker_iff_incomingFirstFlag rate rewards C_star C_h ell z
    rw [heq]
    exact hfirst
  have hhandover : MeasurableSet[F]
      {z : SourceInput p |
        ReferencePostReplacementCollectionHandoverSourcePrefix.handoverIncomingData
          rate rewards C_star C_h ell z = some (true, none)} := by
    have hsingle : MeasurableSet[
        ReferenceInitializationMeasurability.optionCountableMeasurableSpace
          (Bool × Option (Finset (Fin (p.m - 1))))]
        {some (true, none)} := MeasurableSpace.measurableSet_top
    exact hsingle.preimage
      (ReferencePostReplacementCollectionHandoverSourcePrefix.handoverIncomingData_measurable
        rate rewards C_star C_h control0 ell)
  have hbad : MeasurableSet[F]
      {z : SourceInput p |
        ell.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z} := by
    have heq :
        {z : SourceInput p |
          ell.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
            rate rewards C_star C_h z} =
        {z | ReferenceOriginalFirstBadStrictPrefix.noBadEventStrictlyBefore
          rate rewards C_star C_h z ell} := by
      ext z
      exact (ReferenceOriginalFirstBadStrictPrefix.firstBadDate_prefix_iff
        rate rewards C_star C_h z ell)
    rw [heq]
    exact ReferenceOriginalFirstBadStrictPrefix.noBadEventStrictlyBefore_strictPrefix_measurable
      rate rewards C_star C_h control0 ell
  have hcount := stoppedStartCountThrough_preRound_measurable
    rate rewards C_star C_h control0 k ell
  rw [kthBirthMark]
  change MeasurableSet[F]
    (({z : SourceInput p |
        ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
            rate rewards C_star C_h ell z} ∪
      {z : SourceInput p |
        ReferencePostReplacementCollectionHandoverSourcePrefix.handoverIncomingData
          rate rewards C_star C_h ell z = some (true, none)}) ∩
      ({z : SourceInput p |
        ell.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate
          rate rewards C_star C_h z} ∩
       {z : SourceInput p |
        ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
          rate rewards C_star C_h (ell.val + 1) z = k.val + 1}))
  exact (hmarker.union hhandover).inter (hbad.inter hcount)

/-- Every finite masked fixed-label signed prefix is integrable under the
original private source law. -/
public theorem fixedPrefix_integrable (ell : Fin p.T) (v : ℕ) :
    Integrable (fixedSignedPrefix rate rewards C_star C_h ell v)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  classical
  unfold fixedSignedPrefix
  let control0 : ContinuousLearningRows.TimeControl p :=
    (fun _ => ⟨0, by norm_num⟩, fun _ => (fun _ => 0, 0))
  apply integrable_finsetSum (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
    (s := Finset.univ.filter (fun t : Fin p.T => t.val < v))
  intro t ht
  let supportSet : Set (SourceInput p) :=
    {z | ReferenceOriginalInstallationStoppedReleasePhase.supportAt
      rate rewards C_star C_h ell.val t.val z}
  have hsupportAt := ReferenceOriginalInstallationStoppedReleasePhase.supportAt_preRound_measurable
    rate rewards C_star C_h control0 ell.val t
  have hsupport : MeasurableSet supportSet := by
    exact ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)) supportSet hsupportAt
  have hdeficit := ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit_integrable
    rate rewards C_star C_h ell.val t
  have hterm :
      (fun z : SourceInput p =>
        if ReferenceOriginalInstallationStoppedReleasePhase.supportAt
            rate rewards C_star C_h ell.val t.val z then
          ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
            rate rewards C_star C_h ell.val t z
        else 0) =
      supportSet.indicator
        (ReferenceOriginalInstallationReleaseSignedCharge.actualFixedReleaseSignedDeficit
          rate rewards C_star C_h ell.val t) := by
    funext z
    simp [supportSet, Set.indicator]
  rw [hterm]
  exact hdeficit.indicator hsupport

/-- On its literal mark, the ranked stopped start has occurred by the
inclusive marked date. -/
public theorem markedStart_le_markedDate (k : Fin (p.T + 1)) (ell : Fin p.T)
    (z : SourceInput p) (hmark : z ∈ kthBirthMark rate rewards C_star C_h k ell) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h k z ≤ ell.val + 1 := by
  have hcount := hmark.2.2
  have hn : ell.val + 1 ≤ p.T := Nat.succ_le_of_lt ell.isLt
  apply (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
    rate rewards C_star C_h k (ell.val + 1) hn z).2
  rw [hcount]
  omega

/-- Each literal mark constructs a birth in the same complete actual suffix.
The FIRST branch is the zero-ranked launch; a later birth is strictly after
its existing ranked transfer start. No release-success premise is used. -/
public theorem mark_actual_installation (k : Fin (p.T + 1)) (ell : Fin p.T)
    (z : SourceInput p) (hmark : z ∈ kthBirthMark rate rewards C_star C_h k ell) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let a := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (b : Fin R.length) (M : ReferenceActivePhysicalStep.Payload rate),
      a + b.val = ell.val ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] M ∧
      ((b.val = 0 ∧ R[b.val].input.state.coordinator = .first ∧
          ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
            rate rewards C_star C_h k z = ell.val + 1 ∧ k.val = 0) ∨
        (ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true ∧
          ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
            rate rewards C_star C_h k z < ell.val + 1)) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let a := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hle := markedStart_le_markedDate rate rewards C_star C_h k ell z hmark
  have hmem := (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_mem_iff
    rate rewards C_star C_h k z).mp (hle.trans (Nat.succ_le_of_lt ell.isLt))
  obtain ⟨q, hq, hqdate⟩ :=
    (ReferenceOriginalStoppedPhysicalTransferStarts.mem_stoppedPhysicalTransferStartDates_iff
      rate rewards C_star C_h _ z).mp hmem
  rcases hmark.1 with hfirst | hlater
  · obtain ⟨record, hr, hf, selected, hd⟩ :=
      ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_installation
        rate rewards C_star C_h ell z hfirst
    have ha : ell.val = a := hfirst.2.1
    obtain ⟨b, hbdate, hb⟩ :=
      ReferenceOriginalTransferPhysicalIntervals.actualRecordAt_suffix_index
        rate rewards C_star C_h ell z (by omega) record hr
    change a + b.val = ell.val at hbdate
    have hbzero : b.val = 0 := by omega
    have hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth record
        (CoordinatorAssignmentRegisterInstall.installFirst
          (CoordinatorRoundDispatch.firstLaunchInput
            (ReferenceActivePhysicalStep.firstInput record.input))).registers.payload := by
      unfold ReferenceAssignmentPayloadPersistence.InstallationBirth
      rw [show record.output.preparation.coordinator =
        ReferenceActivePhysicalStep.dispatch record.input by rw [record.output_eq]; rfl, hd]
      exact ⟨rfl, by
        have htime := ReferenceAssignmentPayloadPersistence.firstChosen_payload_time
          record.input _ selected (by
            have hdispatch := ReferenceActivePhysicalStep.dispatch_first record.input hf
            rw [hdispatch] at hd
            exact ReferenceActivePhysicalStep.DispatchCut.first.inj hd)
        exact htime⟩
    have hstart_ge : ell.val + 1 ≤
        ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h k z := by
      rcases hq.1 with hi | hl
      · have hqa : q.val = a := hi.2.1
        omega
      · have hqa :=
          ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt_after_physicalStart
            rate rewards C_star C_h q z hl
        change a ≤ q.val at hqa
        omega
    have hcount_one :
        ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
          rate rewards C_star C_h (ell.val + 1) z = 1 := by
      unfold ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
      have hset : (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartRounds
          rate rewards C_star C_h z).filter (fun t => t.val + 1 ≤ ell.val + 1) = {ell} := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨ht, htle⟩
          have htstart := (Finset.mem_filter.mp ht).2.1
          have hat : a ≤ t.val := by
            rcases htstart with hi | hl
            · exact Nat.le_of_eq hi.2.1.symm
            · exact ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferLiveStartAt_after_physicalStart
                rate rewards C_star C_h t z hl
          apply Fin.ext
          omega
        · rintro rfl
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hfirst, hmark.2.1⟩,
            le_rfl⟩
      rw [hset, Finset.card_singleton]
    have hkzero : k.val = 0 := by
      have hc := hmark.2.2
      rw [hcount_one] at hc
      omega
    refine ⟨b, (CoordinatorAssignmentRegisterInstall.installFirst
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput record.input))).registers.payload,
      hbdate, ?_, Or.inl ⟨hbzero, ?_, le_antisymm hle hstart_ge, hkzero⟩⟩
    · change ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] _
      rw [hb]
      exact hbirth
    · change R[b.val].input.state.coordinator = .first
      rw [hb]
      exact hf
  · obtain ⟨record, hr⟩ : ∃ record,
        ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h ell z = some record := by
      cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h ell z with
      | none =>
          simp [ReferencePostReplacementCollectionHandoverSourcePrefix.handoverIncomingData,
            ReferenceSourcePrefixHistoryFiltration.incoming, hr] at hlater
      | some record => exact ⟨record, rfl⟩
    have ha : a ≤ ell.val := by
      by_contra hn
      simp [ReferenceSourcePrefixHistoryFiltration.actualRecord,
        show ¬ ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
          ell.val from hn] at hr
    obtain ⟨b, hbdate, hb⟩ :=
      ReferenceOriginalTransferPhysicalIntervals.actualRecordAt_suffix_index
        rate rewards C_star C_h ell z ha record hr
    have hstate : ∃ payload ledger saved,
        record.input.state.coordinator = .collection payload ledger saved := by
      cases hc : record.input.state.coordinator with
      | collection payload ledger saved => exact ⟨payload, ledger, saved, rfl⟩
      | first =>
          simp [ReferencePostReplacementCollectionHandoverSourcePrefix.handoverIncomingData,
            ReferenceSourcePrefixHistoryFiltration.incoming, hr,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc,
            ReferencePostReplacementCollectionHandoverSourcePrefix.incomingHandoverData] at hlater
      | live registers owned base =>
          simp [ReferencePostReplacementCollectionHandoverSourcePrefix.handoverIncomingData,
            ReferenceSourcePrefixHistoryFiltration.incoming, hr,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc,
            ReferencePostReplacementCollectionHandoverSourcePrefix.incomingHandoverData] at hlater
      | dagger =>
          simp [ReferencePostReplacementCollectionHandoverSourcePrefix.handoverIncomingData,
            ReferenceSourcePrefixHistoryFiltration.incoming, hr,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc,
            ReferencePostReplacementCollectionHandoverSourcePrefix.incomingHandoverData] at hlater
    obtain ⟨payload, ledger, saved, hc⟩ := hstate
    have hbstate : R[b.val].input.state.coordinator = .collection payload ledger saved := by
      rw [hb]
      exact hc
    have hlaterB :=
      (ReferencePostReplacementCollectionHandoverSourcePrefix.handoverIncomingData_collection_birth
        rate rewards C_star C_h z ell b payload ledger saved (by rw [hb]; exact hr)
        hbstate).mp hlater
    obtain ⟨M, hbirth, _⟩ :=
      ReferenceOriginalTransferPhysicalIntervals.actual_later_installation_missing_date_iff
        rate rewards C_star C_h z b hlaterB
    have hnot :=
      ReferenceOriginalTransferPhysicalIntervals.actual_laterChosen_installation_is_not_transfer_start
        rate rewards C_star C_h ell z record hr (by rw [← hb]; exact hlaterB)
    have hstrict :
        ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h k z < ell.val + 1 := by
      have hne : q ≠ ell := by
        intro heq
        subst q
        exact hnot hq.1
      have hqne : q.val ≠ ell.val := fun h => hne (Fin.ext h)
      omega
    exact ⟨b, M, hbdate, hbirth, Or.inr ⟨hlaterB, hstrict⟩⟩

private theorem supported_label_lt_date (label : ℕ) (t : Fin p.T)
    (z : SourceInput p)
    (hsupport : ReferenceOriginalInstallationStoppedReleasePhase.supportAt
      rate rewards C_star C_h label t.val z) : label < t.val := by
  have hlaunch := ReferenceOriginalInstallationStoppedReleasePhase.supportAt_actualLaunchBy
    rate rewards C_star C_h label t z hsupport
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome =
      true := hlaunch.1
  let a := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let seed := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  have hseed := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z rewards C_star C_h hcross
  have haT := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have helapsed : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = a := rfl
  have hrun : (ReferenceLocalReleaseGateChronology.sourceRun rate z rewards C_star C_h
      hcross a (p.T - a) helapsed (by dsimp [a]; omega)).records =
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h := by
    simpa only [ReferenceLocalReleaseGateChronology.sourceRun, a, seed] using
      (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate z rewards C_star C_h seed hseed).symm
  have hgate := ((ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff_stopped_originalGate
    rate rewards C_star C_h label t.val z t.isLt).mp hsupport).1
  obtain ⟨record, hrecord, hg, htime⟩ :=
    (ReferenceLocalReleaseGateChronology.mem_gateSupport label (t.val + 1)
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).mp hgate
  have hrecordRun : record ∈ (ReferenceLocalReleaseGateChronology.sourceRun
      rate z rewards C_star C_h hcross a (p.T - a) helapsed (by dsimp [a]; omega)).records := by
    rw [hrun]
    exact hrecord
  obtain ⟨_payload, _birth, _hs1, _hs2, _hb1, _hb2, _hb3, hlt, _⟩ :=
    ReferenceLocalReleaseGateChronology.source_gate_birth_and_payload_chronology
      rate z rewards C_star C_h hcross a (p.T - a) helapsed (by dsimp [a]; omega)
      label record hrecordRun record hrecordRun hg hg
  omega

/-- The original fixed-label release start is after its label, including
its honest `T+1` sentinel when no supported round exists. -/
public theorem markedDate_le_releaseStart (ell : Fin p.T) (z : SourceInput p) :
    ell.val + 1 ≤ ReferenceOriginalInstallationStoppedReleasePhase.sigmaR
      rate rewards C_star C_h ell.val z := by
  by_contra hn
  have hle : ReferenceOriginalInstallationStoppedReleasePhase.sigmaR
      rate rewards C_star C_h ell.val z ≤ ell.val := by omega
  obtain ⟨t, ht, hs⟩ :=
    (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR_le_iff_exists_supported_date
      rate rewards C_star C_h ell.val z ell.val (Nat.le_of_lt ell.isLt)).mp hle
  have hlt := supported_label_lt_date rate rewards C_star C_h ell.val t z hs
  omega

/-- Transport any event in the existing ranked-start stopped field on its
literal mark to the existing fixed-label release-start stopped field. Only
this intersection is transported; no global field inclusion is asserted. -/
public theorem marked_event_at_release_start
    (control0 : ContinuousLearningRows.TimeControl p) (k : Fin (p.T + 1))
    (ell : Fin p.T) (B0 : Set (SourceInput p))
    (hB0 : MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k)
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_isPreRoundStoppingTime
        rate rewards C_star C_h control0 k)] B0) :
    MeasurableSet[PhaseStartConditionalWaiting.phaseStartSigmaAlgebra
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR rate rewards C_star C_h ell.val)
      (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR_stopping
        rate rewards C_star C_h control0 ell.val)]
      (B0 ∩ kthBirthMark rate rewards C_star C_h k ell) := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let E := kthBirthMark rate rewards C_star C_h k ell
  let start := ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
    rate rewards C_star C_h k
  let sigma := ReferenceOriginalInstallationStoppedReleasePhase.sigmaR
    rate rewards C_star C_h ell.val
  have hE : MeasurableSet[F (ell.val + 1)] E :=
    mark_preRound_measurable rate rewards C_star C_h control0 k ell
  have hBcut : MeasurableSet[F (ell.val + 1)]
      (B0 ∩ {z | start z ≤ ell.val + 1}) := by
    have hset : {z | (start z : WithTop ℕ) ≤ ((ell.val + 1 : ℕ) : WithTop ℕ)} =
        {z | start z ≤ ell.val + 1} := by
      ext z
      norm_cast
    have h := hB0.2 (ell.val + 1)
    change MeasurableSet[F (ell.val + 1)]
      (B0 ∩ {z | (start z : WithTop ℕ) ≤ ((ell.val + 1 : ℕ) : WithTop ℕ)}) at h
    rw [hset] at h
    exact h
  have hrestrict : (B0 ∩ {z | start z ≤ ell.val + 1}) ∩ E = B0 ∩ E := by
    ext z
    constructor
    · rintro ⟨⟨hz, _⟩, he⟩
      exact ⟨hz, he⟩
    · rintro ⟨hz, he⟩
      exact ⟨⟨hz, markedStart_le_markedDate rate rewards C_star C_h k ell z he⟩, he⟩
  have hBE : MeasurableSet[F (ell.val + 1)] (B0 ∩ E) := by
    rw [← hrestrict]
    exact hBcut.inter hE
  change MeasurableSet[(PhaseStartConditionalWaiting.isStoppingTime_of_preRound F sigma
    (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR_stopping
      rate rewards C_star C_h control0 ell.val)).measurableSpace] (B0 ∩ E)
  refine ⟨le_iSup F (ell.val + 1) _ hBE, ?_⟩
  intro n
  change MeasurableSet[F n]
    ((B0 ∩ E) ∩ {z | (sigma z : WithTop ℕ) ≤ (n : WithTop ℕ)})
  have hset : {z | (sigma z : WithTop ℕ) ≤ (n : WithTop ℕ)} =
      {z | sigma z ≤ n} := by
    ext z
    norm_cast
  rw [hset]
  by_cases hn : ell.val + 1 ≤ n
  · exact (F.mono hn _ hBE).inter
      (ReferenceOriginalInstallationStoppedReleasePhase.sigmaR_stopping
        rate rewards C_star C_h control0 ell.val n)
  · have hempty : (B0 ∩ E) ∩ {z | sigma z ≤ n} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨_, hz⟩
      have horder := markedDate_le_releaseStart rate rewards C_star C_h ell z
      change sigma z ≤ n at hz
      change ell.val + 1 ≤ sigma z at horder
      omega
    rw [hempty]
    exact @MeasurableSet.empty (SourceInput p) (F n)

private theorem count_survival_mem_window (k : Fin (p.T + 1)) (ell : Fin p.T)
    (z : SourceInput p)
    (hbad : ell.val + 1 ≤ ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z)
    (hcount : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
      rate rewards C_star C_h (ell.val + 1) z = k.val + 1) :
    ell ∈ ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates
      rate rewards C_star C_h z k := by
  classical
  have hbound : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
      rate rewards C_star C_h (ell.val + 1) z ≤ p.T := by
    unfold ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin _)
  have hk : k.val + 1 < p.T + 1 := by omega
  let next : Fin (p.T + 1) := ⟨k.val + 1, hk⟩
  have hnext : ¬ ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
      rate rewards C_star C_h next z ≤ ell.val + 1 := by
    intro hn
    have hgt :=
      (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
        rate rewards C_star C_h next (ell.val + 1) (Nat.succ_le_of_lt ell.isLt) z).mp hn
    change k.val + 1 < _ at hgt
    omega
  have hnext' : ell.val + 1 < ReferenceOriginalTransferPhysicalIntervals.nextStoppedTransferStartDate
      rate rewards C_star C_h k z := by
    change ell.val + 1 <
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h next z
    omega
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · apply (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
      rate rewards C_star C_h k (ell.val + 1) (Nat.succ_le_of_lt ell.isLt) z).mpr
    rw [hcount]
    omega
  · unfold ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
    exact lt_min hnext' (by have ht := ell.isLt; omega)

/-- The literal count and inclusive stop put the marked birth inside the
existing half-open ranked transfer window. -/
public theorem mark_mem_ranked_window (k : Fin (p.T + 1)) (ell : Fin p.T)
    (z : SourceInput p) (hmark : z ∈ kthBirthMark rate rewards C_star C_h k ell) :
    ell ∈ ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates
      rate rewards C_star C_h z k :=
  count_survival_mem_window rate rewards C_star C_h k ell z hmark.2.1 hmark.2.2

/-- Two marks of the same ranked transfer cannot name different birth dates.
This uses the actual collection and installed LIVE intervals on the same run. -/
public theorem marks_disjoint (k : Fin (p.T + 1)) (ell ell' : Fin p.T)
    (hne : ell ≠ ell') :
    Disjoint (kthBirthMark rate rewards C_star C_h k ell)
      (kthBirthMark rate rewards C_star C_h k ell') := by
  classical
  apply Set.disjoint_left.mpr
  intro z hz hz'
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let a := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let E := ReferenceOriginalTransferPhysicalIntervals.stoppedTransferWindowEndDate
    rate rewards C_star C_h k z
  have hk := (markedStart_le_markedDate rate rewards C_star C_h k ell z hz).trans
    (Nat.succ_le_of_lt ell.isLt)
  have hwindow (l : Fin p.T) (hl : z ∈ kthBirthMark rate rewards C_star C_h k l) :
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
          rate rewards C_star C_h k z ≤ l.val + 1 ∧ l.val + 1 < E :=
    (Finset.mem_filter.mp (mark_mem_ranked_window rate rewards C_star C_h k l z hl)).2
  have hequal : ell.val = ell'.val := by
    by_cases hinitial : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z = a + 1
    · let W := ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
        rate rewards C_star C_h z
      obtain ⟨hW, _hE, _hclip, hglobal, _M, _hM, hfieldsInit, _⟩ :=
        ReferenceOriginalStoppedTransferPhaseIntervals.initial_rank_stopped_transfer_phase_intervals
          rate rewards C_star C_h k z hk hinitial
      obtain hempty | ⟨hpos, installed, selected, _hs, _hi, _hp, _hempty, _hp0, hfields⟩ :=
        ReferenceOriginalInitialTransferWindowGeometry.raw_initial_transfer_window_provenance
          rate rewards C_star C_h z
      · change W.length = 0 at hempty
        change 0 < W.length at hW
        omega
      have hlabel (l : Fin p.T) (hl : z ∈ kthBirthMark rate rewards C_star C_h k l) :
          l.val = a := by
        obtain ⟨b, M, hdate, _hbirth, hbranch⟩ :=
          mark_actual_installation rate rewards C_star C_h k l z hl
        rcases hbranch with ⟨hb, _⟩ | ⟨hlater, _⟩
        · change a + b.val = l.val at hdate
          omega
        · have htime := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
            rate rewards C_star C_h z b
          have hbefore : R[b.val].input.time.val + 1 < E := by
            have := (hwindow l hl).2
            change R[b.val].input.time.val + 1 = a + b.val + 1 at htime
            change a + b.val = l.val at hdate
            omega
          have hbW : b.val < W.length := ((hglobal b).mp hbefore).1
          let j : Fin W.length := ⟨b.val, hbW⟩
          have hget : R[b.val] = W[j.val] := by
            have hslot := (hfieldsInit j).1
            change R[b.val]? = some W[j.val] at hslot
            rw [List.getElem?_eq_getElem b.isLt] at hslot
            exact Option.some.inj hslot
          obtain ⟨payload, ledger, saved, hstate, _⟩ :=
            ReferenceCollectionPhaseHistory.laterChosen_pending_empty _ hlater
          obtain ⟨selectedJ, _hsJ, _hpJ, hphase, _⟩ := hfields j
          change (match W[j.val].input.state.coordinator with
            | .first => _ | .live _ _ _ => _ | _ => False) at hphase
          rw [← hget, hstate] at hphase
          exact hphase.elim
      exact (hlabel ell hz).trans (hlabel ell' hz').symm
    · obtain ⟨i, hi, hbranch⟩ :=
        ReferenceOriginalStoppedTransferPhaseIntervals.present_stopped_transfer_collection_intervals
          rate rewards C_star C_h k z hk
      rcases hbranch with ⟨hzero, _⟩ | hcollection
      · exact (hinitial (by simpa only [hzero, Nat.add_zero] using hi)).elim
      obtain ⟨registers, owned, base, seg, _hstate, _hat, _hentry, _hpayload, _hne,
        hCfields, _hCactual, _hCiff, hend⟩ := hcollection
      have hloc (l : Fin p.T) (hl : z ∈ kthBirthMark rate rewards C_star C_h k l) :
          ∃ b : Fin R.length, a + b.val = l.val ∧
            ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true ∧ i.val ≤ b.val ∧
              R[b.val].input.time.val + 1 < E := by
        obtain ⟨b, M, hdate, _hbirth, hbranch⟩ :=
          mark_actual_installation rate rewards C_star C_h k l z hl
        rcases hbranch with ⟨hbzero, _hf, hstart, _⟩ | ⟨hlater, _⟩
        · exact (hinitial (by change a + b.val = l.val at hdate; omega)).elim
        · have htime := ReferenceOriginalTransferPhysicalIntervals.completeSuffixRecord_source_date
            rate rewards C_star C_h z b
          change R[b.val].input.time.val + 1 = a + b.val + 1 at htime
          change a + b.val = l.val at hdate
          have hbds := hwindow l hl
          change _ = a + i.val + 1 at hi
          exact ⟨b, hdate, hlater, by omega, by omega⟩
      rcases hend with ⟨_hterminal, _hE, hchoices, _⟩ | hlater
      · obtain ⟨b, _hdate, hb, hbi, _⟩ := hloc ell hz
        have hc := hchoices b hbi
        rw [ReferenceOriginalTransferPhysicalIntervals.actual_laterChosen_not_collection_choice
          R[b.val] hb] at hc
        cases hc
      obtain ⟨b, hbi, hb, _hexit, _hstateb, _hempty, _hlen, _hE, _hclip, hglobal,
        _M, _hbirth, _hfields, _⟩ := hlater
      let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (b.val + 1)
      have hlabel (l : Fin p.T) (hl : z ∈ kthBirthMark rate rewards C_star C_h k l) :
          l.val = a + b.val := by
        obtain ⟨c, hdate, hc, hic, hbefore⟩ := hloc l hl
        have hcend : c.val < b.val + V.length := ((hglobal c).mp ⟨hic, hbefore⟩).2.1
        have hbc : b.val ≤ c.val := by
          by_contra hn
          let j : Fin seg.records.length := ⟨c.val - i.val, by omega⟩
          have hslot := (hCfields j).1
          have hindex : i.val + j.val = c.val := by dsimp only [j]; omega
          rw [hindex, List.getElem?_eq_getElem c.isLt] at hslot
          have hget : R[c.val] = seg.records[j.val] := Option.some.inj hslot
          obtain ⟨chosen, hchoice, _⟩ := (hCfields j).2.2
          rw [← hget, ReferenceOriginalTransferPhysicalIntervals.actual_laterChosen_not_collection_choice
            R[c.val] hc] at hchoice
          cases hchoice
        have heq : c.val = b.val := by
          by_contra hn
          let j : Fin V.length := ⟨c.val - b.val, by omega⟩
          have hfields := (ReferenceOriginalInstalledLiveStartExclusion.actual_later_installation_live_start_exclusion
            rate rewards C_star C_h z b hb).1 j
          have hslot := hfields.1
          have hindex : b.val + j.val = c.val := by dsimp only [j]; omega
          rw [hindex, List.getElem?_eq_getElem c.isLt] at hslot
          have hget : R[c.val] = V[j.val] := Option.some.inj hslot
          rcases hfields.2.2.2.2.2.2.2.2.2.1 with ⟨hjzero, _⟩ | ⟨_hjpos, _htest, r, o, bs, hs, _⟩
          · dsimp only [j] at hjzero
            omega
          · obtain ⟨payload, ledger, saved, hcstate, _⟩ :=
              ReferenceCollectionPhaseHistory.laterChosen_pending_empty _ hc
            rw [← hget, hcstate] at hs
            cases hs
        omega
      exact (hlabel ell hz).trans (hlabel ell' hz').symm
  exact hne (Fin.ext hequal)

private theorem birth_support_startCount
    (z : SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hbranch : (b.val = 0 ∧ (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input.state.coordinator = .first) ∨
      ReferenceCollectionPhaseHistory.laterChosen (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (t : Fin p.T)
    (hsupport : ReferenceOriginalInstallationStoppedReleasePhase.supportAt rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) t.val z) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
        rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val + 1) z =
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
        rate rewards C_star C_h (t.val + 1) z := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let a := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let label := a + b.val
  have hlt : label < t.val := supported_label_lt_date
    rate rewards C_star C_h label t z hsupport
  have hno : ∀ q : Fin p.T, label < q.val → q.val ≤ t.val →
      ¬ ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferStartAt
        rate rewards C_star C_h q z := by
    rcases hbranch with ⟨hbzero, _hfirst⟩ | hb
    · let W := ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
        rate rewards C_star C_h z
      have hgate := (ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff_stopped_originalGate
        rate rewards C_star C_h label t.val z t.isLt).mp hsupport |>.1
      have hcal := ReferenceFirstLiveInitialTransferChronology.raw_release_calendar
        rate rewards C_star C_h z
      change ReferenceLocalReleaseGateChronology.gateSupport a R = _ at hcal
      have hlabel : label = a := by dsimp [label]; rw [hbzero, Nat.add_zero]
      change t.val + 1 ∈ ReferenceLocalReleaseGateChronology.gateSupport label R at hgate
      rw [hlabel, hcal] at hgate
      obtain ⟨r, hr, htime⟩ := Finset.mem_image.mp hgate
      obtain ⟨hrW, _⟩ := Finset.mem_filter.mp hr
      have hrW' : r ∈ W := List.mem_toFinset.mp hrW
      obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hrW'
      have hdate := (ReferenceOriginalInitialTransferWindowGeometry.raw_window_record_calendar
        rate rewards C_star C_h z ⟨j, hj⟩).1
      change W[j].input.time.val = a + j at hdate
      change r.input.time.val + 1 = t.val + 1 at htime
      rw [heq] at hdate
      intro q hq hqt
      let u : Fin W.length := ⟨q.val - a, by omega⟩
      have hudate := (ReferenceOriginalInitialTransferWindowGeometry.raw_window_record_calendar
        rate rewards C_star C_h z u).1
      have hu : W[u.val].input.time = q := by
        apply Fin.ext
        change W[u.val].input.time.val = a + u.val at hudate
        have harith : a + u.val = q.val := by dsimp only [u]; omega
        exact hudate.trans harith
      rw [← hu]
      exact ReferenceOriginalInitialTransferWindowGeometry.raw_window_no_positive_transfer_start
        rate rewards C_star C_h z u (by dsimp [u]; omega)
    · let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (b.val + 1)
      obtain ⟨⟨r, hr, hrt⟩, _⟩ :=
        (ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff_later_release_member
          rate rewards C_star C_h z b hb t).mp hsupport
      have hrV : r ∈ V := by
        have hsuffix : (V.dropWhile
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).IsSuffix V :=
          List.dropWhile_suffix _
        exact hsuffix.subset hr
      obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hrV
      have hfields :=
        ReferenceOriginalInstalledLiveStartExclusion.actual_later_installation_live_start_exclusion
          rate rewards C_star C_h z b hb
      have hdate := (hfields.1 ⟨j, hj⟩).2.1
      change V[j].input.time.val + 1 = a + b.val + j + 1 at hdate
      rw [heq, hrt] at hdate
      intro q hq hqt
      let u : Fin V.length := ⟨q.val - label, by omega⟩
      have huFields := hfields.1 u
      have hudate := huFields.2.1
      have hu : V[u.val].input.time = q := by
        apply Fin.ext
        change V[u.val].input.time.val + 1 = label + u.val + 1 at hudate
        have harith : label + u.val = q.val := by dsimp only [u]; omega
        exact (Nat.add_right_cancel hudate).trans harith
      rw [← hu]
      exact huFields.2.2.2.2.2.2.2.2.2.2
  unfold ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
  congr 1
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hq, hdate⟩
    exact ⟨hq, by change q.val + 1 ≤ label + 1 at hdate; omega⟩
  · rintro ⟨hq, hdate⟩
    refine ⟨hq, ?_⟩
    change q.val + 1 ≤ label + 1
    by_contra hn
    have hstart := (Finset.mem_filter.mp hq).2.1
    exact hno q (by omega) (by omega) hstart

private theorem ranked_window_startCount (k : Fin (p.T + 1)) (t : Fin p.T)
    (z : SourceInput p)
    (ht : t ∈ ReferenceOriginalStoppedTransferSignedReindex.kthStoppedTransferWindowDates
      rate rewards C_star C_h z k) :
    ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
      rate rewards C_star C_h (t.val + 1) z = k.val + 1 := by
  classical
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

/-- Every nonempty original kth release has its literal predictable mark,
and its complete natural-prefix signed identity at that mark. The witness
is constructed from the accepted actual installation, rather than supplied. -/
public theorem nonempty_release_mark_and_prefix (k : Fin (p.T + 1)) (z : SourceInput p)
    (hne : ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
      rate rewards C_star C_h z k ≠ ∅) :
    ∃ ell : Fin p.T, z ∈ kthBirthMark rate rewards C_star C_h k ell ∧
      ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates rate rewards C_star C_h z k =
        ReferenceOriginalKthReleaseGateAlignment.fixedLabelReleaseDates
          rate rewards C_star C_h z ell.val ∧
      ∀ v : ℕ,
        (∑ t ∈ (ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
          rate rewards C_star C_h z k).filter (fun t => t.val < v),
          ReferenceOriginalCalendarTransferPhaseCover.actualDateSignedDelta rate rewards C_star C_h z t) =
        fixedSignedPrefix rate rewards C_star C_h ell v z := by
  classical
  obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain hempty | ⟨b, M, hbranch, hbirth, htime, _hstamp, hdates, _hpoint, hprefix⟩ :=
    ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge_empty_or_actual_installation
      rate rewards C_star C_h z k
  · exact (hne hempty.1).elim
  let ell := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[b.val].input.time
  have hell : ell.val = ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h + b.val := htime
  have hs : ReferenceOriginalInstallationStoppedReleasePhase.supportAt
      rate rewards C_star C_h ell.val t.val z := by
    rw [hdates] at ht
    rw [ReferenceOriginalKthReleaseGateAlignment.mem_fixedLabelReleaseDates_iff] at ht
    apply (ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff
      rate rewards C_star C_h ell.val t.val z t.isLt).mpr
    simpa only [hell] using ht
  have hlt := supported_label_lt_date rate rewards C_star C_h ell.val t z hs
  have hbad := ((ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff
    rate rewards C_star C_h ell.val t.val z t.isLt).mp hs).2
  have hcount := birth_support_startCount rate rewards C_star C_h z b hbranch t
    (by simpa only [hell] using hs)
  have hrank := ranked_window_startCount rate rewards C_star C_h k t z
    ((ReferenceOriginalKthReleaseGateAlignment.mem_kthReleaseDates_iff
      rate rewards C_star C_h z k t).mp ht).1
  have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h ell z = some
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val] := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
    rw [hell, ite_eq_left (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact List.getElem?_eq_getElem b.isLt
  have htag :
      ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt
        rate rewards C_star C_h ell z ∨
      ReferencePostReplacementCollectionHandoverSourcePrefix.handoverIncomingData
        rate rewards C_star C_h ell z = some (true, none) := by
    rcases hbranch with ⟨_hbzero, hf⟩ | hlater
    · exact Or.inl ((ReferenceOriginalCalendarPhysicalTransferCount.actualPhysicalTransferInitialMarkerAt_iff_record_first
        rate rewards C_star C_h ell z).mpr ⟨_, hrecord, hf⟩)
    · obtain ⟨payload, ledger, saved, hstate, _⟩ :=
        ReferenceCollectionPhaseHistory.laterChosen_pending_empty _ hlater
      exact Or.inr ((ReferencePostReplacementCollectionHandoverSourcePrefix.handoverIncomingData_collection_birth
        rate rewards C_star C_h z ell b payload ledger saved hrecord hstate).mpr hlater)
  have he : z ∈ kthBirthMark rate rewards C_star C_h k ell :=
    ⟨htag, by omega, by rw [hell, hcount, hrank]⟩
  obtain ⟨b0, M0, hdate0, hbirth0, _⟩ :=
    mark_actual_installation rate rewards C_star C_h k ell z he
  have hb0 : b0 = b := Fin.ext (by omega)
  rw [hb0] at hbirth0
  have hwhole : M0 = M := ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
    _ M0 M hbirth0 hbirth
  cases hwhole
  refine ⟨ell, he, ?_, ?_⟩
  · simpa only [hell] using hdates
  · intro v
    simpa only [fixedSignedPrefix, hell] using hprefix v

/-- Absence of every finite mark forces the actual kth release date set to
be empty, for every rank including the sentinel rank. -/
public theorem no_mark_dates_empty (k : Fin (p.T + 1)) (z : SourceInput p)
    (hz : ∀ ell : Fin p.T, z ∉ kthBirthMark rate rewards C_star C_h k ell) :
    ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
      rate rewards C_star C_h z k = ∅ := by
  by_contra hn
  obtain ⟨ell, he, _⟩ := nonempty_release_mark_and_prefix rate rewards C_star C_h k z hn
  exact hz ell he

open ReferenceActivePhysicalStep ReferenceActivePhysicalStepMeasurability
  ReferenceRetainedReleasePhaseObservation in
private theorem actual_gate_no_cutoff (x : RoundInput p rate) (label : ℕ)
    (hg : localReleaseGate rate label x.time (encodeState x.state) = true) :
    ReferenceCollectionPhaseHistory.cutoffChosen x = false := by
  obtain ⟨r, q, base, hc, _hb, _he, _hsigma, hu⟩ :=
    ReferenceLocalReleaseGateChronology.gate_live label x.time x.state hg
  have hgate := hg
  simp only [localReleaseGate, encodeState, encodeCoordinator, hc,
    Bool.and_eq_true, decide_eq_true_eq] at hgate
  have hlast := hgate.2
  cases hs : localReleaseStartResult rate x.time (encodeLive r q base) with
  | error failure => simp only [hs, Bool.false_eq_true] at hlast
  | ok started =>
    have hf : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
        (liveRegistersAt r x.time) started := by
      have hf' : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          (decodeLiveRegisters r.payload (encodeLive r q base)) started := by
        simpa only [hs, decide_eq_true_eq] using hlast
      simpa only [CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame,
        decodeLiveRegisters, encodeLive, liveRegistersAt,
        CoordinatorLiveChoiceRecorderStep.Registers.clockPending] using hf'
    have hd : (prepare x).coordinator = .live r q base
        (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
      simp only [prepare, dispatch, hc, CoordinatorRoundDispatch.dispatch]
      rfl
    unfold ReferenceCollectionPhaseHistory.cutoffChosen
    rw [hd]
    cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) with
    | cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected =>
      have heq : dispatched.startResult = started := Except.ok.inj (hstart.symm.trans hs)
      have huframe : started.clock.u = r.priorClock.u := congrArg
        CoordinatorPhaseClock.ClockRegisters.u hf.1
      have hucut : dispatched.startResult.clock.u = some x.time := congrArg
        CoordinatorPhaseClock.ClockRegisters.u hclock
      rw [heq, huframe, hu] at hucut
      cases hucut
    | _ => rfl

private theorem supported_date_is_release (label : ℕ) (t : Fin p.T) (z : SourceInput p)
    (hs : ReferenceOriginalInstallationStoppedReleasePhase.supportAt
      rate rewards C_star C_h label t.val z) :
    t ∈ ReferenceOriginalCalendarTransferPhaseCover.releasePhaseDates rate rewards C_star C_h z := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hgate := (ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff_stopped_originalGate
    rate rewards C_star C_h label t.val z t.isLt).mp hs
  obtain ⟨r, hr, hg, htime⟩ :=
    (ReferenceLocalReleaseGateChronology.mem_gateSupport label (t.val + 1) R).mp hgate.1
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
  let index : Fin R.length := ⟨j, hj⟩
  have ht : R[j].input.time = t := Fin.ext (by omega)
  obtain ⟨registers, owned, base, hc, _hstamp, hempty, _⟩ :=
    ReferenceLocalReleaseGateChronology.gate_live label R[j].input.time R[j].input.state hg
  obtain ⟨htest, selected, hselected, _hp, hpending⟩ :=
    ReferencePostReplacementCollectionHandoverSourcePrefix.actual_live_continuing_pending
      rate rewards C_star C_h z index registers owned base hc
      (actual_gate_no_cutoff rate R[j].input label hg)
  change ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest R[j] = true at htest
  have hchoice : ReferenceCollectionSegmentExtraction.choice R[j].input = none := by
    have hprepare : R[j].output.preparation = ReferenceActivePhysicalStep.prepare R[j].input := by
      rw [R[j].output_eq]; rfl
    unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at htest
    cases hd : R[j].output.preparation.coordinator with
    | live registers owned base outcome =>
      cases outcome <;> simp only [hd, Bool.false_eq_true] at htest
      unfold ReferenceCollectionSegmentExtraction.choice
      rw [← hprepare, hd]
      simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, ite_self]
    | first outcome => simp only [hd, Bool.false_eq_true] at htest
    | collection payload ledger clock cutoff outcome => simp only [hd, Bool.false_eq_true] at htest
    | invalidCollectionCutoff => simp only [hd, Bool.false_eq_true] at htest
    | dagger => simp only [hd, Bool.false_eq_true] at htest
  have hrelease : ReferenceOriginalCalendarTransferPhaseCover.actualReleaseSelection rate R[j] := by
    rcases ReferenceOriginalCalendarTransferPhaseCover.actual_suffix_phase_availability
        rate rewards C_star C_h z index with ⟨c, hc⟩ | ⟨other, ho, _hlive, hne⟩ | hrel
    · change ReferenceCollectionSegmentExtraction.choice R[j].input = some c at hc
      rw [hchoice] at hc
      cases hc
    · have heq : other = selected := Option.some.inj (ho.symm.trans hselected)
      subst other
      rw [hpending, hempty] at hne
      exact (Finset.not_nonempty_empty hne).elim
    · exact hrel
  have hlaunch := ReferenceOriginalInstallationStoppedReleasePhase.supportAt_actualLaunchBy
    rate rewards C_star C_h label t z hs
  have hlaunchDate : ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound
      rate rewards C_star C_h z =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1 := by
    change ReferenceInitializationRun.launchRound
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate) = _
    unfold ReferenceInitializationRun.launchRound
    have hc : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome =
        true := hlaunch.1
    rw [hc]
    rfl
  apply Finset.mem_image.mpr
  refine ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hrelease⟩, ht⟩
  change ReferenceOriginalCalendarTransferPhaseCover.actualLaunchRound rate rewards C_star C_h z ≤
      R[j].input.time.val + 1 ∧ R[j].input.time.val + 1 ≤
        min (ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z) p.T
  rw [ht, hlaunchDate]
  exact ⟨by have := hlaunch.2; omega, le_min hgate.2 (Nat.succ_le_of_lt t.isLt)⟩

private theorem marked_support_mem_release (k : Fin (p.T + 1)) (ell t : Fin p.T)
    (z : SourceInput p) (he : z ∈ kthBirthMark rate rewards C_star C_h k ell)
    (hs : ReferenceOriginalInstallationStoppedReleasePhase.supportAt
      rate rewards C_star C_h ell.val t.val z) :
    t ∈ ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates rate rewards C_star C_h z k := by
  obtain ⟨b, M, hdate, _hbirth, hbranch⟩ := mark_actual_installation rate rewards C_star C_h k ell z he
  have hb : (b.val = 0 ∧ (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val].input.state.coordinator = .first) ∨
      ReferenceCollectionPhaseHistory.laterChosen (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true :=
    hbranch.elim (fun h => Or.inl ⟨h.1, h.2.1⟩) (fun h => Or.inr h.1)
  have hcount := birth_support_startCount rate rewards C_star C_h z b hb t (by rw [hdate]; exact hs)
  rw [hdate, he.2.2] at hcount
  exact (ReferenceOriginalKthReleaseGateAlignment.mem_kthReleaseDates_iff
    rate rewards C_star C_h z k t).mpr
    ⟨count_survival_mem_window rate rewards C_star C_h k t z
      ((ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff
        rate rewards C_star C_h ell.val t.val z t.isLt).mp hs).2 hcount.symm,
      supported_date_is_release rate rewards C_star C_h ell.val t z hs⟩

/-- On every literal mark the entire original kth release date set is the
same fixed-label set, even when either set is empty. -/
public theorem mark_release_dates (k : Fin (p.T + 1)) (ell : Fin p.T)
    (z : SourceInput p) (he : z ∈ kthBirthMark rate rewards C_star C_h k ell) :
    ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates rate rewards C_star C_h z k =
      ReferenceOriginalKthReleaseGateAlignment.fixedLabelReleaseDates rate rewards C_star C_h z ell.val := by
  classical
  by_cases hn : ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates rate rewards C_star C_h z k = ∅
  · rw [hn]
    apply Eq.symm
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hs := (ReferenceOriginalKthReleaseGateAlignment.mem_fixedLabelReleaseDates_iff
      rate rewards C_star C_h z ell.val t).mp ht
    have hm := marked_support_mem_release rate rewards C_star C_h k ell t z he
      ((ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff
        rate rewards C_star C_h ell.val t.val z t.isLt).mpr hs)
    rw [hn] at hm
    exact Finset.notMem_empty t hm
  · obtain ⟨l, hl, hdates, _⟩ := nonempty_release_mark_and_prefix rate rewards C_star C_h k z hn
    have heq : l = ell := by
      by_contra hne
      exact (Set.disjoint_left.mp (marks_disjoint rate rewards C_star C_h k l ell hne)) hl he
    simpa only [heq] using hdates

/-- The common actual birth, whole payload, original phase dates and both
start orders on a literal mark. -/
public theorem mark_actual_birth_and_dates (k : Fin (p.T + 1)) (ell : Fin p.T)
    (z : SourceInput p) (he : z ∈ kthBirthMark rate rewards C_star C_h k ell) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let a := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (b : Fin R.length) (M : ReferenceActivePhysicalStep.Payload rate),
      a + b.val = ell.val ∧ ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] M ∧
      ((b.val = 0 ∧ R[b.val].input.state.coordinator = .first ∧
          ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
            rate rewards C_star C_h k z = ell.val + 1 ∧ k.val = 0) ∨
        (ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true ∧
          ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
            rate rewards C_star C_h k z < ell.val + 1)) ∧
      ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates rate rewards C_star C_h z k =
        ReferenceOriginalKthReleaseGateAlignment.fixedLabelReleaseDates rate rewards C_star C_h z ell.val ∧
      ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate
        rate rewards C_star C_h k z ≤ ell.val + 1 ∧
      ell.val + 1 ≤ ReferenceOriginalInstallationStoppedReleasePhase.sigmaR rate rewards C_star C_h ell.val z := by
  obtain ⟨b, M, hdate, hbirth, hbranch⟩ := mark_actual_installation rate rewards C_star C_h k ell z he
  exact ⟨b, M, hdate, hbirth, hbranch, mark_release_dates rate rewards C_star C_h k ell z he,
    markedStart_le_markedDate rate rewards C_star C_h k ell z he,
    markedDate_le_releaseStart rate rewards C_star C_h ell z⟩

private theorem fixedPrefix_zero_of_dates_empty (ell : Fin p.T) (v : ℕ) (z : SourceInput p)
    (hempty : ReferenceOriginalKthReleaseGateAlignment.fixedLabelReleaseDates
      rate rewards C_star C_h z ell.val = ∅) :
    fixedSignedPrefix rate rewards C_star C_h ell v z = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t _ht
  apply ite_eq_right
  intro hs
  have hm := (ReferenceOriginalKthReleaseGateAlignment.mem_fixedLabelReleaseDates_iff
    rate rewards C_star C_h z ell.val t).mpr
    ((ReferenceOriginalInstallationStoppedReleasePhase.supportAt_iff
      rate rewards C_star C_h ell.val t.val z t.isLt).mp hs)
  rw [hempty] at hm
  exact Finset.notMem_empty t hm

/-- Exact signed reindexing for every natural prefix. Empty pending sets
remain supported; the only mask is the original fixed-label R support. -/
public theorem signed_prefix_mark_reindex (k : Fin (p.T + 1)) (v : ℕ) (z : SourceInput p) :
    (∑ t ∈ (ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
        rate rewards C_star C_h z k).filter (fun t => t.val < v),
      ReferenceOriginalCalendarTransferPhaseCover.actualDateSignedDelta rate rewards C_star C_h z t) =
    ∑ ell : Fin p.T, (kthBirthMark rate rewards C_star C_h k ell).indicator
      (fixedSignedPrefix rate rewards C_star C_h ell v) z := by
  classical
  by_cases hempty : ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
      rate rewards C_star C_h z k = ∅
  · rw [hempty, Finset.filter_empty, Finset.sum_empty]
    symm
    apply Finset.sum_eq_zero
    intro ell _hell
    by_cases he : z ∈ kthBirthMark rate rewards C_star C_h k ell
    · rw [Set.indicator_of_mem he]
      apply fixedPrefix_zero_of_dates_empty rate rewards C_star C_h ell v z
      rw [← mark_release_dates rate rewards C_star C_h k ell z he, hempty]
    · exact Set.indicator_of_notMem he _
  · obtain ⟨ell, he, _hdates, hprefix⟩ :=
      nonempty_release_mark_and_prefix rate rewards C_star C_h k z hempty
    rw [hprefix v]
    symm
    calc
      _ = (kthBirthMark rate rewards C_star C_h k ell).indicator
          (fixedSignedPrefix rate rewards C_star C_h ell v) z := by
        apply Finset.sum_eq_single ell
        · intro l _hl hne
          apply Set.indicator_of_notMem
          intro hl
          exact (Set.disjoint_left.mp (marks_disjoint rate rewards C_star C_h k l ell hne)) hl he
        · intro hn
          exact (hn (Finset.mem_univ ell)).elim
      _ = _ := Set.indicator_of_mem he _

/-- The signed prefix masked by one predictable birth mark is integrable. -/
public theorem markedPrefix_integrable (k : Fin (p.T + 1)) (ell : Fin p.T)
    (v : ℕ) :
    Integrable (fun z : SourceInput p =>
      if z ∈ kthBirthMark rate rewards C_star C_h k ell then
        fixedSignedPrefix rate rewards C_star C_h ell v z else 0)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  classical
  let control0 : ContinuousLearningRows.TimeControl p :=
    (fun _ => ⟨0, by norm_num⟩, fun _ => (fun _ => 0, 0))
  let E : Set (SourceInput p) := {z | z ∈ kthBirthMark rate rewards C_star C_h k ell}
  have hEpre := mark_preRound_measurable rate rewards C_star C_h control0 k ell
  have hE : MeasurableSet E := by
    exact ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (ell.val + 1)) E hEpre
  have hfixed := fixedPrefix_integrable rate rewards C_star C_h ell v
  have hterm :
      (fun z : SourceInput p =>
        if z ∈ kthBirthMark rate rewards C_star C_h k ell then
          fixedSignedPrefix rate rewards C_star C_h ell v z else 0) =
      E.indicator (fixedSignedPrefix rate rewards C_star C_h ell v) := by
    funext z
    simp [E, Set.indicator]
  rw [hterm]
  exact hfixed.indicator hE

/-- The finite sum of marked fixed-label signed prefixes is integrable. -/
public theorem finiteMarkedPrefix_integrable (k : Fin (p.T + 1)) (v : ℕ) :
    Integrable (fun z : SourceInput p =>
      ∑ ell ∈ Finset.univ,
        if z ∈ kthBirthMark rate rewards C_star C_h k ell then
          fixedSignedPrefix rate rewards C_star C_h ell v z else 0)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  classical
  apply integrable_finsetSum (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
    (s := Finset.univ)
  intro ell hell
  exact markedPrefix_integrable rate rewards C_star C_h k ell v

/-- The actual original kth signed release charge is integrable, by the
finite marked signed-prefix identity under the original private source law. -/
public theorem kthCharge_integrable (k : Fin (p.T + 1)) :
    Integrable (fun z : SourceInput p =>
      ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge
        rate rewards C_star C_h z k) (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply (finiteMarkedPrefix_integrable rate rewards C_star C_h k p.T).congr
  apply Filter.Eventually.of_forall
  intro z
  have hfilter : (ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
      rate rewards C_star C_h z k).filter (fun t => t.val < p.T) =
      ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates rate rewards C_star C_h z k :=
    Finset.filter_eq_self.mpr (fun t _ht => t.isLt)
  simpa only [ReferenceOriginalKthReleaseSignedChargeLocalization.kthReleaseSignedCharge,
    hfilter, Set.indicator_apply] using
    (signed_prefix_mark_reindex rate rewards C_star C_h k p.T z).symm

/-- The terminal rank has no birth mark, and its original actual release
date set is empty. -/
public theorem sentinelRank_no_mark_or_release (z : SourceInput p) :
    (∀ ell : Fin p.T,
      kthBirthMark rate rewards C_star C_h ⟨p.T, by omega⟩ ell = ∅) ∧
      ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates
        rate rewards C_star C_h z ⟨p.T, by omega⟩ = ∅ := by
  constructor
  · intro ell
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hcount := hx.2.2
    have hkval : (⟨p.T, by omega⟩ : Fin (p.T + 1)).val = p.T := rfl
    have hle : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
        rate rewards C_star C_h (ell.val + 1) x ≤ p.T := by
      unfold ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
      calc
        _ ≤ (Finset.univ : Finset (Fin p.T)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = p.T := Finset.card_fin _
    rw [hcount] at hle
    rw [hkval] at hle
    omega
  · apply ReferenceOriginalKthReleaseGateAlignment.kthReleaseDates_eq_empty_of_absent_rank
    intro hdate
    have hcount : ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
        rate rewards C_star C_h p.T z ≤ p.T := by
      unfold ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartCountThrough
      calc
        _ ≤ (Finset.univ : Finset (Fin p.T)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = p.T := Finset.card_fin _
    have hgt := (ReferenceOriginalStoppedPhysicalTransferStarts.stoppedPhysicalTransferStartDate_le_iff_count_gt
      rate rewards C_star C_h ⟨p.T, by omega⟩ p.T le_rfl z).mp hdate
    have hkval : (⟨p.T, by omega⟩ : Fin (p.T + 1)).val = p.T := rfl
    rw [hkval] at hgt
    exact (Nat.not_lt_of_ge hcount) hgt

end Bandits.Support.ReferenceOriginalKthBirthMarkLocalization

end
