/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarRoundInnovation

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic

/-!
# Actual generated noncall dates

Sources: ZIP4 `06_interruptions.tex:391-408,423-426`,
`04_slow_fast_learner.tex:142-215,329-363`, and `08_main_theorem.tex:85-100`.

The optional cell below is read from the existing generated calendar, with its
original auxiliary array and entire incoming native archive. The first branch
measure remains unnormalized. Native coefficients evaluate the joint raw input,
numerical UPDATE and effective output, including disabled and stopped cases.
Whole raw-source/vector tests retain their correlated refill representation.
These internal results concern one noncall date, not an episode law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstNextInstallationTransitionLaw
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferencePostInvocationSupportedDisintegration
open ReferencePostInvocationKilledJointLaw
open ReferenceGeneratedInvocationCallSplice
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarEndpointMixture
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarJointRebase
open ReferenceGeneratedCalendarRoundInnovation
open ReferenceGeneratedNativeInvocationGeometry
open ReferenceActualCollectionHiddenRefreshPath
  (actualOriginalWord actualOriginalWord_length actualOriginalWord_numericalPrefix)
open ReferenceCompletePhysicalHistory (physicalStart completeSuffixRecords)
open RecordedQueueRun (run scoreWeight)
open ReferenceFirstCorrectedNextCalendarWordJoin (calendarReplay)

namespace Bandits.Support.ReferenceGeneratedCalendarNoncallRoundLaw

variable {p : ConstructorDimensions.Parameters}

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Vector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "Control" => ContinuousLearningRows.TimeControl p
local notation "Scalar" => ContinuousControlSlice.Scalar
local notation "Auxiliary" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "Outcome" => ReferencePostInvocationCollectionNativeLaw.Outcome p
local notation "replace" => ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p

local instance sourceMeasurableSpace : MeasurableSpace Source := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance
local instance controlMeasurableSpace : MeasurableSpace Control :=
  ReferencePostInvocationSupportedDisintegration.controlMeasurableSpace
local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] : MeasurableSpace (Option X) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p) (b0 : Bool) (u0 t0 : Fin p.T)

include control0

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "observe" => calendarObservation rate rewards C_star C_h control0 b0 u0 t0
local notation "original" => calendarOriginalLift rate rewards C_star C_h b0 u0 t0
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
local notation "stored" => calendarStoredState rate rewards C_star C_h control0 b0 u0 t0
local notation "past" => calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0
local notation "callFlag" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0
local notation "extension" => calendarExtensionKernel rate rewards C_star C_h control0 b0 u0 t0

/-- Literal optional native cell on the actual incoming generated tape. -/
def calendarNoncallCell (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k) :
    Option (LogicalCell p rate) :=
  noncallDateCell rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
    (current k hk.le w) (original k w).1.2 (stored k hk.le w).1

local notation "cell" => calendarNoncallCell rate rewards C_star C_h control0 b0 u0 t0

/-- Effective optional output. An absent cell and a present bottom recorder
have different tags. The raw input remains in `calendarNoncallCell`. -/
def calendarNoncallOutcome (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k) : Outcome :=
  ReferencePostInvocationCollectionNativeLaw.optionalOutcome rate (cell k hk w)

local notation "outcome" => calendarNoncallOutcome rate rewards C_star C_h control0 b0 u0 t0

theorem measurable_calendarStoredSeed (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) :
    Measurable (fun w : Sample k => (stored k hk w).1) :=
  (measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk).snd.fst

theorem measurable_calendarNoncallArguments (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) :
    Measurable (fun w : Sample k =>
      ((stored k hk w).1, (current k hk w, (original k w).1.2))) :=
  (measurable_calendarStoredSeed rate rewards C_star C_h control0 b0 u0 t0 k hk).prodMk
    ((measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk).prodMk
      (measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.snd)

theorem measurable_calendarNoncallCell (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    Measurable (α := Sample k) (β := Option (LogicalCell p rate)) (cell k hk) := by
  have he : cell k hk = (fun v : SlowSet p × (Source × Auxiliary) =>
      noncallDateCell rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩ v.2.1 v.2.2 v.1) ∘
      (fun w : Sample k => ((stored k hk.le w).1, (current k hk.le w, (original k w).1.2))) := rfl
  rw [he]
  exact (measurable_noncallDateCell rate rewards C_star C_h control0 ⟨t0.val + 1 + k, hk⟩).comp
    (measurable_calendarNoncallArguments rate rewards C_star C_h control0 b0 u0 t0 k hk.le)

theorem measurable_calendarNoncallOutcome (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    Measurable (outcome k hk) :=
  (ReferencePostInvocationCollectionNativeLaw.measurable_optionalOutcome rate).comp
    (measurable_calendarNoncallCell rate rewards C_star C_h control0 b0 u0 t0 k hk)

/-- Every actual noncall is a continuing LIVE or COLLECTION date. This is
derived from the generated native source, without a domain premise. -/
theorem calendarNoncall_phase (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hc : callFlag k (by omega) w = false) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    current k hk.le w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q ∨
    current k hk.le w ∈ collectionDateDomain rate rewards C_star C_h q := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o := observe k hk.le w
  let z := calendarNativeSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
  have hstart := (ReferencePostInvocationGeneratedAlignment.actualRecord_index rate rewards C_star C_h
    o.1 z.val _ (nativeSourceCell_spec rate rewards C_star C_h o.1 z).1).choose_spec.2.2
  have hdate := (calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1
  apply noncall_phase_coverage rate rewards C_star C_h q z.val (hstart.trans_lt hdate)
  rw [ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none]
  apply Option.not_isSome_iff_eq_none.mp
  change ¬ callFlag k (by omega) w = true
  rw [hc]
  exact Bool.false_ne_true

section Refill

variable (k : ℕ) (hk : t0.val + 1 + k < p.T)

omit control0 in
theorem noncallDate_after : t0.val < t0.val + 1 + k := by omega

local notation "q" => (Fin.mk (t0.val + 1 + k) hk)
local notation "htq" => (noncallDate_after t0 k)
local notation "fill" => calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k

theorem calendarCurrentSource_fillInnovation (w : Sample k) (x : Innovation p) :
    current k hk.le (fill (w, x)) = replace q (current k hk.le w) x.1 := by
  change current k hk.le (calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k
    (calendarFillPair rate rewards C_star C_h b0 u0 t0 q k (w, x.2), x.1)) = _
  rw [calendarCurrentSource_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk.le le_rfl,
    calendarFillPair_eq_withAuxiliary]
  rw [(calendarObservation_withAuxiliary_source_tag rate rewards C_star C_h control0 b0 u0 t0 k hk.le w _).2]

theorem calendarOriginalAuxiliary_fillInnovation (w : Sample k) (x : Innovation p) :
    (original k (fill (w, x))).1.2 =
      ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q (original k w).1.2 x.2 := by
  change (original k (calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k
    (calendarFillPair rate rewards C_star C_h b0 u0 t0 q k (w, x.2), x.1))).1.2 = _
  rw [calendarOriginalLift_replaceControl, calendarFillPair_eq_withAuxiliary,
    calendarOriginalLift_withAuxiliary]

theorem calendarCallFlag_fillInnovation (w : Sample k) (x : Innovation p) :
    callFlag k (by omega) (fill (w, x)) = callFlag k (by omega) w := by
  change callFlag k (by omega) (calendarReplaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k
    (calendarFillPair rate rewards C_star C_h b0 u0 t0 q k (w, x.2), x.1)) = _
  rw [calendarCallFlag_replaceControl rate rewards C_star C_h control0 b0 u0 t0 q htq k hk le_rfl,
    calendarFillPair_eq_withAuxiliary, calendarCallFlag_withAuxiliary]

theorem calendarNoncallCell_fillInnovation (w : Sample k) (x : Innovation p) :
    cell k hk (fill (w, x)) = noncallDateCell rate rewards C_star C_h q
      (replace q (current k hk.le w) x.1)
      (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q (original k w).1.2 x.2)
      (stored k hk.le w).1 := by
  have hs := congrArg (fun h : Source × (SlowSet p × List (LogicalCell p rate)) => h.2.1)
    (calendarRoundPast_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 q htq k hk.le le_rfl (w, x))
  change (stored k hk.le (fill (w, x))).1 = (stored k hk.le w).1 at hs
  unfold calendarNoncallCell
  rw [calendarCurrentSource_fillInnovation, calendarOriginalAuxiliary_fillInnovation, hs]

/-- All-controls identification with the accepted LIVE native producer. -/
theorem calendarNoncallOutcome_fill_live (w : Sample k)
    (hl : current k hk.le w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q) (x : Innovation p) :
    outcome k hk (fill (w, x)) =
      ReferencePostInvocationLiveNativeLaw.sourceOutcome rate rewards C_star C_h control0 q
        ⟨current k hk.le w, hl⟩ (original k w).1.2 x := by
  have hl' := (ReferencePostInvocationLiveNativeLaw.continuingDomain_replace rate rewards C_star C_h
    control0 q (current k hk.le w) x.1).mpr hl
  unfold calendarNoncallOutcome
  rw [calendarNoncallCell_fillInnovation, noncallDateCell, dite_eq_left hl']
  rfl

/-- All-controls identification with the COLLECTION native producer, for the
actual incoming hidden set, without identifying it with the old assignment. -/
theorem calendarNoncallOutcome_fill_collection (w : Sample k)
    (hl : current k hk.le w ∉ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q)
    (hcol : current k hk.le w ∈ collectionDateDomain rate rewards C_star C_h q) (x : Innovation p) :
    outcome k hk (fill (w, x)) =
      ReferencePostInvocationCollectionNativeLaw.sourceOutcome rate rewards C_star C_h control0 q
        ⟨current k hk.le w, hcol⟩ (stored k hk.le w).1 (original k w).1.2 x := by
  have hl' : replace q (current k hk.le w) x.1 ∉
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q :=
    fun h => hl ((ReferencePostInvocationLiveNativeLaw.continuingDomain_replace rate rewards C_star C_h
      control0 q (current k hk.le w) x.1).mp h)
  have hc' := ReferencePostInvocationCollectionNativeLaw.collectionDateDomain_replace_control rate rewards C_star C_h
    control0 q ⟨current k hk.le w, hcol⟩ x.1
  unfold calendarNoncallOutcome
  rw [calendarNoncallCell_fillInnovation, noncallDateCell, dite_eq_right hl', dite_eq_left hc']
  rfl

end Refill

omit control0 b0 u0 t0 in
/-- Explicit LIVE coefficients. The recorder/FAST factor is the accepted
correlated native pair, and the fixed-anchor residual is marker-specific. -/
def liveMass (q : Fin p.T) (z : ContinuingLiveSource rate rewards C_star C_h q)
    (o : Outcome) : ℝ≥0∞ :=
  if (continuingBefore rate rewards C_star C_h q z).overflow then
    if o = Sum.inr (none, frozenFastArm p, false, frozenSlowSet p) then 1 else 0
  else match o with
    | .inl _ => 0
    | .inr (i, j, B, V) =>
      ReferencePostInvocationLiveNativeLaw.nativePairLaw rate rewards C_star C_h q z {(i, j)} *
        (if B then ENNReal.ofReal (4 * (p.m : ℝ) * rate.eta.val) *
          ReferencePostInvocationLiveNativeLaw.residualLaw rate rewards C_star C_h q z i {V}
        else ENNReal.ofReal (1 - 4 * (p.m : ℝ) * rate.eta.val) *
          if V = (continuingSourceCell rate rewards C_star C_h q z).selected.view.payload.slowSet
          then 1 else 0)

omit control0 b0 u0 t0 in
theorem nativeLiveLaw_singleton (q : Fin p.T)
    (z : ContinuingLiveSource rate rewards C_star C_h q) (o : Outcome) :
    ReferencePostInvocationLiveNativeLaw.nativeLaw rate rewards C_star C_h q z {o} =
      liveMass rate rewards C_star C_h q z o := by
  cases hp : (continuingBefore rate rewards C_star C_h q z).overflow with
  | true =>
    rw [ReferencePostInvocationLiveNativeLaw.nativeLaw_overflow rate rewards C_star C_h q z hp]
    simp only [liveMass, hp, ite_true, Measure.dirac_apply, Set.mem_singleton_iff,
      Set.indicator_apply, Pi.one_apply]
    by_cases ho : o = Sum.inr (none, frozenFastArm p, false, frozenSlowSet p) <;>
      simp only [ho, eq_comm, ite_true, ite_false]
  | false =>
    cases o with
    | inl u =>
      cases u
      simpa only [liveMass, hp, Bool.false_eq_true, ite_false] using
        ReferencePostInvocationLiveNativeLaw.nativeLaw_absent rate rewards C_star C_h q z
    | inr v =>
      rcases v with ⟨i, j, B, V⟩
      simpa only [liveMass, hp, Bool.false_eq_true, ite_false] using
        ReferencePostInvocationLiveNativeLaw.nativeLaw_atom_clear rate rewards C_star C_h q z hp i j B V

/-- Evaluated coefficients on the actual generated incoming source. The
outside-domain branch is the literal absent optional cell; actual noncalls
are proved below to lie in one of the two native domains. -/
def calendarNoncallMass (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (o : Outcome) : ℝ≥0∞ :=
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  if hl : current k hk.le w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q then
    liveMass rate rewards C_star C_h q ⟨current k hk.le w, hl⟩ o
  else if hc : current k hk.le w ∈ collectionDateDomain rate rewards C_star C_h q then
    ReferencePostInvocationCollectionNativeLaw.nativeMass rate rewards C_star C_h q
      ⟨current k hk.le w, hc⟩ (stored k hk.le w).1 o
  else if o = Sum.inl () then 1 else 0

local notation "mass" => calendarNoncallMass rate rewards C_star C_h control0 b0 u0 t0

/-- The whole physical-control/two-label integral is evaluated, at this
actual generated source and incoming archive, into finite native coefficients.
No survival, presence, phase or desired-law premise is supplied. -/
theorem calendarNoncallOutcome_refill_test (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (hc : callFlag k (by omega) w = false) (f : Outcome → ℝ≥0∞) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    (∫⁻ x, f (outcome k hk (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
      (noncallDate_after t0 k) k (w, x))) ∂innovationLaw (p := p)) =
      ∑ o, f o * mass k hk w o := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  by_cases hl : current k hk.le w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q
  · simp_rw [calendarNoncallOutcome_fill_live rate rewards C_star C_h control0 b0 u0 t0 k hk w hl]
    let z : ContinuingLiveSource rate rewards C_star C_h q := ⟨current k hk.le w, hl⟩
    have hn := ReferencePostInvocationLiveNativeLaw.sourceOutcome_law rate rewards C_star C_h control0 q z
      (original k w).1.2
    have hnmap : (innovationLaw (p := p)).map
        (ReferencePostInvocationLiveNativeLaw.sourceOutcome rate rewards C_star C_h control0 q z (original k w).1.2) =
        ReferencePostInvocationLiveNativeLaw.nativeLaw rate rewards C_star C_h q z := hn.2
    rw [← lintegral_map (measurable_of_finite f) hn.1, hnmap, lintegral_fintype]
    apply Finset.sum_congr rfl
    intro o _ho
    rw [nativeLiveLaw_singleton]
    simp only [calendarNoncallMass, dite_eq_left hl, q, z]
  · have hcol := (calendarNoncall_phase rate rewards C_star C_h control0 b0 u0 t0 k hk w hc).resolve_left hl
    simp_rw [calendarNoncallOutcome_fill_collection rate rewards C_star C_h control0 b0 u0 t0 k hk w hl hcol]
    let z : CollectionDateSource rate rewards C_star C_h q := ⟨current k hk.le w, hcol⟩
    have hn := ReferencePostInvocationCollectionNativeLaw.measurable_sourceOutcome rate rewards C_star C_h
      control0 q z (stored k hk.le w).1 (original k w).1.2
    rw [← lintegral_map (measurable_of_finite f) hn, lintegral_fintype]
    apply Finset.sum_congr rfl
    intro o _ho
    rw [show innovationLaw (p := p) = ReferencePostInvocationCollectionNativeLaw.innovationLaw (p := p) from rfl,
      ReferencePostInvocationCollectionNativeLaw.sourceOutcome_mass]
    simp only [calendarNoncallMass, dite_eq_right hl, dite_eq_left hcol, q, z]

/-- Joint strict-past/hidden-seed/whole-archive noncall law. The actual
noncall gate is inside the unnormalized integral. All current-control and
auxiliary coordinates have been integrated into explicit finite coefficients. -/
theorem calendarLaw_noncall_round_test (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (F : (Source × (SlowSet p × List (LogicalCell p rate))) × Outcome → ℝ≥0∞)
    (hF : Measurable F) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    (∫⁻ wv : Sample k × Vector, if callFlag k (by omega) wv.1 = false then
      F (past k hk.le wv.1, outcome k hk wv.1) else 0 ∂law (k + 1) (by omega)) =
      ∫⁻ w, if callFlag k (by omega) w = false then
        ∑ o, F (past k hk.le w, o) * mass k hk w o else 0
        ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q
          (noncallDate_after t0 k) k) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k
  let test : Sample k × Vector → ℝ≥0∞ := fun wv =>
    if callFlag k (by omega) wv.1 = false then F (past k hk.le wv.1, outcome k hk wv.1) else 0
  have hp := measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le
  have ho := measurable_calendarNoncallOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk
  have hgate := measurableSet_eq_fun
    (measurable_calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega))
    (measurable_const (a := false))
  have ht : Measurable test := ((hF.comp (hp.prodMk ho)).comp measurable_fst).ite
    (hgate.preimage measurable_fst) measurable_const
  refine (calendarLaw_round_innovation_test rate rewards C_star C_h control0 b0 u0 t0 q
    (noncallDate_after t0 k) k hk le_rfl test ht).trans ?_
  apply lintegral_congr
  intro w
  change (∫⁻ x, ∫⁻ v, test (fill (w, x), v) ∂extension k (by omega) (fill (w, x))
    ∂innovationLaw (p := p)) = _
  have hflags := calendarCallFlag_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w
  by_cases hc : callFlag k (by omega) w = false
  · rw [ite_eq_left hc]
    have he (x : Innovation p) :
        (∫⁻ v, test (fill (w, x), v) ∂extension k (by omega) (fill (w, x))) =
        F (past k hk.le w, outcome k hk (fill (w, x))) := by
      have hc' : callFlag k (by omega) (fill (w, x)) = false := (hflags x).trans hc
      have hn : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q
          (current k hk.le (fill (w, x))) = none := by
        apply Option.not_isSome_iff_eq_none.mp
        change ¬ callFlag k (by omega) (fill (w, x)) = true
        rw [hc']
        exact Bool.false_ne_true
      rw [calendarExtensionKernel_noCall rate rewards C_star C_h control0 b0 u0 t0 k hk _ hn,
        lintegral_dirac]
      dsimp only [test]
      rw [ite_eq_left hc', calendarRoundPast_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
        (noncallDate_after t0 k) k hk.le le_rfl]
    simp_rw [he]
    exact calendarNoncallOutcome_refill_test rate rewards C_star C_h control0 b0 u0 t0 k hk w hc
      (fun o => F (past k hk.le w, o))
  · rw [ite_eq_right hc]
    have he (x : Innovation p) (v : Vector) : test (fill (w, x), v) = 0 := by
      dsimp only [test]
      rw [hflags, ite_eq_right hc]
    simp_rw [he, lintegral_zero]

/-- Full raw joint test on the same noncall extension. The existing complete
vector is retained by Dirac and stays inside the correlated innovation
integral, together with both actual native observers. -/
theorem calendarLaw_noncall_raw_test (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (F : (Source × (SlowSet p × List (LogicalCell p rate))) ×
      CalendarJointOutput rate rewards C_star C_h b0 u0 t0 k hk → ℝ≥0∞) (hF : Measurable F) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k
    (∫⁻ wv : Sample k × Vector, if callFlag k (by omega) wv.1 = false then
      F (calendarRoundJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv) else 0
      ∂law (k + 1) (by omega)) =
      ∫⁻ w, if callFlag k (by omega) w = false then
        ∫⁻ x, F (past k hk.le w,
          calendarJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk
            (fill (w, x), ReferenceFirstCollectionRenewalVectorInsertion.av q
              (replace q (current k hk.le w) x.1))) ∂innovationLaw (p := p)
        else 0 ∂(law k hk.le).map
          (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k
  let test : Sample k × Vector → ℝ≥0∞ := fun wv =>
    if callFlag k (by omega) wv.1 = false then
      F (calendarRoundJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv) else 0
  have hgate := measurableSet_eq_fun
    (measurable_calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega))
    (measurable_const (a := false))
  have ht : Measurable test := (hF.comp
    (measurable_calendarRoundJointReadout rate rewards C_star C_h control0 b0 u0 t0 k hk)).ite
      (hgate.preimage measurable_fst) measurable_const
  refine (calendarLaw_round_innovation_test rate rewards C_star C_h control0 b0 u0 t0 q
    (noncallDate_after t0 k) k hk le_rfl test ht).trans ?_
  apply lintegral_congr
  intro w
  change (∫⁻ x, ∫⁻ v, test (fill (w, x), v) ∂extension k (by omega) (fill (w, x))
    ∂innovationLaw (p := p)) = _
  by_cases hc : callFlag k (by omega) w = false
  · rw [ite_eq_left hc]
    apply lintegral_congr
    intro x
    have hc' : callFlag k (by omega) (fill (w, x)) = false :=
      (calendarCallFlag_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w x).trans hc
    have hn : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q
        (current k hk.le (fill (w, x))) = none := by
      apply Option.not_isSome_iff_eq_none.mp
      change ¬ callFlag k (by omega) (fill (w, x)) = true
      rw [hc']
      exact Bool.false_ne_true
    rw [calendarExtensionKernel_noCall rate rewards C_star C_h control0 b0 u0 t0 k hk _ hn, lintegral_dirac]
    dsimp only [test, calendarRoundJointReadout]
    rw [ite_eq_left hc', calendarRoundPast_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
      (noncallDate_after t0 k) k hk.le le_rfl, calendarCurrentSource_fillInnovation]
  · rw [ite_eq_right hc]
    have he (x : Innovation p) (v : Vector) : test (fill (w, x), v) = 0 := by
      dsimp only [test]
      rw [calendarCallFlag_fillInnovation, ite_eq_right hc]
    simp_rw [he, lintegral_zero]

/-- The actual optional PRE is always present, even across disabled dates
and at the terminal boundary. No presence premise is used by the round law. -/
theorem calendarNoncall_numerical_present (k : ℕ) (hk : t0.val + 1 + k ≤ p.T) (w : Sample k) :
    ∃ S, (observe k hk w).2.val.2.2.1 = some S :=
  ⟨_, (calendarObservation_word rate rewards C_star C_h control0 b0 u0 t0 k hk w).1⟩

/-- The append/absence partition is the actual stored successor. In
particular an enabled bottom recorder follows the present-cell branch. -/
theorem calendarNoncall_successor (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (v : Vector) (hc : callFlag k (by omega) w = false) :
    stored (k + 1) (by omega) (w, v) =
      match cell k hk w with
      | none => stored k hk.le w
      | some e => (e.nextSlowSet, (stored k hk.le w).2 ++ [e]) := by
  rw [calendarObservation_noncall_step rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc]
  rfl

/-- Native physical record, nominal numerical input, all-arm accepted
arrivals/service and the actual numerical POST, jointly on the same cell.
There is no POST-clear condition, so the first overflow UPDATE is retained. -/
theorem calendarNoncallCell_actualInput (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (v : Vector) (hc : callFlag k (by omega) w = false) (e : LogicalCell p rate)
    (he : cell k hk w = some e) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    ∃ (r : Record rate) (input : RecordedQueueRun.RoundInput p.K),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q (current k hk.le w) = some r ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some input ∧
      input.enabled = true ∧ e.time = q ∧
      e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r ∧
      e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates input ∧
      some e.before = (observe k hk.le w).2.val.2.2.1 ∧
      e.after = RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate) e.before input ∧
      e.arrivals = RecordedQueueRun.acceptedRecord
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) e.before input ∧
      e.service = (fun j => RecordedQueueRun.recordService
        (4 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).n) (e.before.registers j) (e.arrivals j)) ∧
      stored (k + 1) (by omega) (w, v) = (e.nextSlowSet, (stored k hk.le w).2 ++ [e]) ∧
      (observe (k + 1) (by omega) (w, v)).2.val.2.2.1 = some e.after := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o := observe k hk.le w
  let z := calendarNativeSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
  have hword := noncallDateCell_actualWord rate rewards C_star C_h q z.val
    (ReferenceGeneratedNativeInvocationGeometry.nativeInvocation_launch rate rewards C_star C_h o.1 z)
    (original k w).1.2 (stored k hk.le w).1 e he
  obtain ⟨ht, hb, _ha, r, input, hr, hi, hen, hphysical, hn, harr, hservice⟩ := hword
  have hpost := calendarObservation_noncall_cell_post rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc e he
  have hbefore : some e.before = o.2.val.2.2.1 := by
    rw [(calendarObservation_word rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).1]
    exact congrArg some hb
  have hstep : e.after = RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      e.before input := by
    have he0 := he
    unfold calendarNoncallCell noncallDateCell at he0
    split at he0
    next hlive =>
      let zz : ContinuingLiveSource rate rewards C_star C_h q := ⟨current k hk.le w, hlive⟩
      have hs := continuingSourceCell_spec rate rewards C_star C_h q zz
      have hr' : r = continuingRecord rate rewards C_star C_h q zz := Option.some.inj (hr.symm.trans hs.1)
      have hi' : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r =
          some (continuingSourceCell rate rewards C_star C_h q zz).input := by
        rw [hr', ReferenceFirstCollectionCurrentRetainedGate.cell0, hs.2.1, Option.some_or, hs.2.2]
      have hin : input = (continuingSourceCell rate rewards C_star C_h q zz).input :=
        Option.some.inj (hi.symm.trans hi')
      rw [← Option.some.inj he0, hin]
      rfl
    next _ =>
      split at he0
      next hcol =>
        let zz : CollectionDateSource rate rewards C_star C_h q := ⟨current k hk.le w, hcol⟩
        unfold laterCollectionCell? at he0
        split at he0
        next _hen =>
          have hr' : r = collectionRecord rate rewards C_star C_h q zz :=
            Option.some.inj (hr.symm.trans (collectionRecord_spec rate rewards C_star C_h q zz).1)
          have hin : input = collectionInput rate rewards C_star C_h q zz := by
            apply Option.some.inj
            exact hi.symm.trans (hr' ▸ (Option.some_get _).symm)
          rw [← Option.some.inj he0, hin]
          rfl
        next _ => cases he0
      next _ => cases he0
  exact ⟨r, input, hr, hi, hen, ht, hphysical, hn, hbefore, hstep, harr, hservice, hpost.1, hpost.2⟩

omit control0 b0 u0 t0 in
private theorem completeRecord_time (z : Source)
    (b : Fin (completeSuffixRecords rate z rewards C_star C_h).length) :
    (completeSuffixRecords rate z rewards C_star C_h)[b.val].input.time.val =
      physicalStart rate z rewards C_star C_h + b.val := by
  have ht := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values rate z rewards C_star C_h
  have hl := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hb : b.val < p.T - physicalStart rate z rewards C_star C_h := by omega
  have hg := congrArg (fun xs : List ℕ => xs[b.val]?) ht
  simpa only [List.getElem?_map, List.getElem?_eq_getElem b.isLt,
    Option.map_some, ReferenceActivePhysicalHorizon.calendar, List.getElem?_range', hb,
    ite_true, one_mul, Option.some.injEq] using hg

/-- The OLD payload and episode anchor are produced from the actual last
native invocation, at arbitrary rank. Enabled clear collection supplies the
all-arm numerical envelope and the prescribed FAST law for every hidden set. -/
theorem calendarCollection_fastLaw (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hc : current k hk.le w ∈ collectionDateDomain rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩)
    (hen : (collectionInput rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩ ⟨current k hk.le w, hc⟩).enabled = true)
    (hclear : (collectionBefore rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩ ⟨current k hk.le w, hc⟩).overflow = false) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let z : CollectionDateSource rate rewards C_star C_h q := ⟨current k hk.le w, hc⟩
    let P := (collectionArguments rate rewards C_star C_h q z).1
    let weight := scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (collectionBefore rate rewards C_star C_h q z)
    P = (nativeSourceCell rate rewards C_star C_h (observe k hk.le w).1
      (calendarNativeSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le w)).selected.view.payload ∧
    ∃ (hlo : ∀ j, P.anchor j ≤ weight j) (hhi : ∀ j, weight j ≤ 2 * P.anchor j),
      ∀ (U : SlowSet p) (j : CanonicalFastSampling.FastArm U),
        collectionFastMass rate P.anchor weight P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos _ _) U j =
          CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property rate.sourceCap P.anchor weight
            P.anchor_pos (RecordedSlowRefresh.scoreWeight_pos _ _) hlo hhi U j := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let o := observe k hk.le w
  let z := calendarNativeSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
  let zz : CollectionDateSource rate rewards C_star C_h q := ⟨z.val, hc⟩
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let W := collectionNumericalWord rate rewards C_star C_h q zz
  let R := completeSuffixRecords rate z.val rewards C_star C_h
  let s := physicalStart rate z.val rewards C_star C_h
  let h := q.val - s
  have horigin := calendarObservation_origin rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
  have htq : o.1.val < q.val := horigin.1
  have hpay := nativeInvocation_collectionPayload rate rewards C_star C_h o.1 q z htq horigin.2.2 hc
  refine ⟨hpay, ?_⟩
  obtain ⟨b, rho, P, hb, _hbirth, hrhob, _hroot, _hepisode, ha, hpow,
      htime, _horder, hg⟩ := nativeInvocation_episode_anchor rate rewards C_star C_h o.1 z
  have hbt := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h
    o.1 z.val (R[b.val]) hb).2.2.1
  have hbt' := completeRecord_time rate rewards C_star C_h z.val b
  have hbtval : s + b.val = o.1.val := hbt'.symm.trans (congrArg Fin.val hbt)
  have hsq : s ≤ q.val := by omega
  have hbh : rho.val ≤ h := by dsimp only [h]; omega
  have hWlen : W.length = R.length := actualOriginalWord_length rate rewards C_star C_h z.val _
  have hlenR := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z.val rewards C_star C_h
  change R.length = p.T - s at hlenR
  have hq := q.isLt
  have hhW : h ≤ W.length := by dsimp only [h]; omega
  have hrhoW : rho.val ≤ W.length := hbh.trans hhW
  have hclearR : (run Q (W.take rho.val)).overflow = false := by
    cases hflag : (run Q (W.take rho.val)).overflow with
    | false => rfl
    | true =>
      have hfirst := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        Q W rho.val hrhoW).mp hflag
      have hlate := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
        Q W h hhW).mpr (hfirst.trans hbh)
      change (run Q (W.take h)).overflow = false at hclear
      rw [hclear] at hlate
      cases hlate
  have hpre : rho.val ≤ UnstoppedRecordedQueueComparison.firstOverflowPrefix Q W := by
    by_contra hnot
    have hf := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
      Q W rho.val hrhoW).mpr (by omega)
    rw [hclearR] at hf
    cases hf
  have hweights := (actualOriginalWord_numericalPrefix rate rewards C_star C_h z.val
    (collection_launch rate rewards C_star C_h q zz) rho.val hrhoW).2.1
  change scoreWeight Q (run Q (W.take rho.val)) =
      (fun j => AssignmentScoreReconstruction.sourceWeightBase p ^
        (calendarReplay rate W j (min rho.val (UnstoppedRecordedQueueComparison.firstOverflowPrefix Q W))).1) at hweights
  rw [Nat.min_eq_left hpre] at hweights
  have hanchor : (collectionArguments rate rewards C_star C_h q zz).1.anchor =
      scoreWeight Q (run Q (W.take rho.val)) := by
    rw [hpay, ha, hweights]
    funext j
    exact hpow j
  have htimeR := completeRecord_time rate rewards C_star C_h z.val rho
  have hsig : P.sigma.val = s + rho.val := (congrArg Fin.val htime).symm.trans htimeR
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hgrid : FollowerCutoffScan.gridBoundary p rate.eta.val P.sigma ≤ P.sigma.val + 1 + H := by
    have hd := Nat.mod_add_div (P.sigma.val + 1) H
    have hm : H * ((P.sigma.val + 1) / H + 1) ≤ P.sigma.val + 1 + H := by
      rw [Nat.mul_succ]
      omega
    exact (Nat.min_le_right _ _).trans hm
  have hboundary : q.val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val
      (collectionArguments rate rewards C_star C_h q zz).1.sigma := by
    have he := (ReferencePostInvocationGeneratedAlignment.collectionInput_oldGrid rate rewards C_star C_h q zz).2
    have hen' : (collectionInput rate rewards C_star C_h q zz).enabled = true := hen
    rw [hen'] at he
    exact of_decide_eq_true he.symm
  have hshort : h - rho.val ≤ H := by
    rw [hpay, ← hg] at hboundary
    dsimp only [h]
    omega
  have henv (j : Fin p.K) : (collectionArguments rate rewards C_star C_h q zz).1.anchor j ≤
        scoreWeight Q (collectionBefore rate rewards C_star C_h q zz) j ∧
      scoreWeight Q (collectionBefore rate rewards C_star C_h q zz) j ≤
        2 * (collectionArguments rate rewards C_star C_h q zz).1.anchor j := by
    have he := RecordedEpisodeStability.execute_source_weight_envelope Q
      (run Q (W.take rho.val)) ((W.drop rho.val).take (h - rho.val)) j
      ((List.length_take_le _ _).trans hshort)
    rw [← RecordedEpisodeStability.run_take_eq_execute_drop Q W rho.val h hbh] at he
    rw [hanchor]
    exact ⟨he.1, he.2.1.le⟩
  exact ⟨fun j => (henv j).1, fun j => (henv j).2,
    collectionFastMass_eq_qGamma rate _ _ _ _ (fun j => (henv j).1) (fun j => (henv j).2)⟩

omit rate rewards C_star C_h control0 b0 u0 t0 in
/-- All canonical numerical UPDATE fields, including the complete per-arm
input histories, accepted enablement/arrivals, and all-arm service. -/
abbrev NumericalUpdate (p : ConstructorDimensions.Parameters) :=
  RecordedQueueRun.RunState p.K × (RecordedQueueRun.RunState p.K ×
    ((Fin p.K → Bool × ℕ) × (Fin p.K → ℕ)))

omit rewards C_star C_h control0 b0 u0 t0 in
def cellUpdate (e : LogicalCell p rate) : NumericalUpdate p :=
  (e.before, (e.after, (e.arrivals, e.service)))

omit rewards C_star C_h control0 b0 u0 t0 in
theorem measurable_cellUpdate : Measurable (cellUpdate rate) :=
  ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_before.prodMk
    (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_after.prodMk
      (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_arrivals.prodMk
        ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_service))

/-- Actual optional numerical UPDATE, on the same cell as the finite outcome. -/
def calendarNoncallUpdate (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k) :
    Option (NumericalUpdate p) := (cell k hk w).map (cellUpdate rate)

local notation "update" => calendarNoncallUpdate rate rewards C_star C_h control0 b0 u0 t0

theorem measurable_calendarNoncallUpdate (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    Measurable (update k hk) :=
  LaterAssignmentFullOutputMeasurability.measurable_optionMap _ (measurable_cellUpdate rate) _
    (measurable_calendarNoncallCell rate rewards C_star C_h control0 b0 u0 t0 k hk)

omit rewards C_star C_h control0 b0 u0 t0 in
/-- Literal numerical recurrence for an already specified PRE and input. -/
def numericalUpdate (S : RecordedQueueRun.RunState p.K) (input : RecordedQueueRun.RoundInput p.K) :
    NumericalUpdate p :=
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  (S, (RecordedQueueRun.step Q S input,
    (RecordedQueueRun.acceptedRecord Q S input,
      fun j => RecordedQueueRun.recordService (4 * Q.n) (S.registers j)
        (RecordedQueueRun.acceptedRecord Q S input j))))

omit rewards C_star C_h control0 b0 u0 t0 in
private theorem acceptedRecord_stopped (S : RecordedQueueRun.RunState p.K) (hS : S.overflow = true)
    (input : RecordedQueueRun.RoundInput p.K) :
    RecordedQueueRun.acceptedRecord (ReferenceFirstLaunchNumericalCell.queueParameters rate) S input =
      fun _ => (false, 0) := by
  funext j
  simp only [RecordedQueueRun.acceptedRecord, hS, ite_true]

/-- Numerical UPDATE associated with a finite native outcome on the actual
incoming source. The input keeps the same reward row and frozen rates. -/
def calendarNoncallUpdateForOutcome (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (o : Outcome) : Option (NumericalUpdate p) :=
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  match o with
  | .inl _ => none
  | .inr (i, _, _, _) =>
    if hl : current k hk.le w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
        rate rewards C_star C_h q then
      some (numericalUpdate rate (continuingBefore rate rewards C_star C_h q ⟨current k hk.le w, hl⟩)
        (ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q ⟨current k hk.le w, hl⟩ i))
    else if hc : current k hk.le w ∈ collectionDateDomain rate rewards C_star C_h q then
      some (numericalUpdate rate (collectionBefore rate rewards C_star C_h q ⟨current k hk.le w, hc⟩)
        (ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q ⟨current k hk.le w, hc⟩ i))
    else none

local notation "updateFor" => calendarNoncallUpdateForOutcome rate rewards C_star C_h control0 b0 u0 t0

section NumericalRefill

variable (k : ℕ) (hk : t0.val + 1 + k < p.T)

local notation "q" => (Fin.mk (t0.val + 1 + k) hk)
local notation "fill" => calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k

/-- Full LIVE cell identification, retaining the raw numerical and physical
coordinates which its effective finite projection suppresses after stopping. -/
theorem calendarNoncallCell_fill_live (w : Sample k)
    (hl : current k hk.le w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q) (x : Innovation p) :
    cell k hk (fill (w, x)) = some
      (ReferencePostInvocationLiveNativeLaw.controlledCell rate rewards C_star C_h q
        ⟨current k hk.le w, hl⟩ x.1 x.2.2) := by
  have hl' := (ReferencePostInvocationLiveNativeLaw.continuingDomain_replace rate rewards C_star C_h
    control0 q (current k hk.le w) x.1).mpr hl
  rw [calendarNoncallCell_fillInnovation, noncallDateCell, dite_eq_left hl']
  exact congrArg some (ReferencePostInvocationLiveNativeLaw.sourceAt_logicalCell rate rewards C_star C_h
    control0 q ⟨current k hk.le w, hl⟩ (original k w).1.2 x.1 x.2)

/-- Full optional COLLECTION cell identification for the actual hidden set. -/
theorem calendarNoncallCell_fill_collection (w : Sample k)
    (hl : current k hk.le w ∉ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q)
    (hc : current k hk.le w ∈ collectionDateDomain rate rewards C_star C_h q) (x : Innovation p) :
    cell k hk (fill (w, x)) = laterCollectionCell? rate rewards C_star C_h q
      (ReferencePostInvocationCollectionNativeLaw.replaceCollectionSource rate rewards C_star C_h control0 q
        ⟨current k hk.le w, hc⟩ x.1) (stored k hk.le w).1
      (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q (original k w).1.2 x.2) := by
  have hl' : replace q (current k hk.le w) x.1 ∉
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q :=
    fun h => hl ((ReferencePostInvocationLiveNativeLaw.continuingDomain_replace rate rewards C_star C_h
      control0 q (current k hk.le w) x.1).mp h)
  have hc' := ReferencePostInvocationCollectionNativeLaw.collectionDateDomain_replace_control rate rewards C_star C_h
    control0 q ⟨current k hk.le w, hc⟩ x.1
  rw [calendarNoncallCell_fillInnovation, noncallDateCell, dite_eq_right hl', dite_eq_left hc']
  rfl

/-- The SAME full numerical UPDATE is determined jointly with the effective
native outcome. On stopped PREs all accepted records are false, so replacing
the effective marker by bottom preserves the full numerical transition. -/
theorem calendarNoncallUpdate_fillInnovation (w : Sample k)
    (hc : callFlag k (by omega) w = false) (x : Innovation p) :
    update k hk (fill (w, x)) = updateFor k hk w (outcome k hk (fill (w, x))) := by
  by_cases hl : current k hk.le w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q
  · unfold calendarNoncallUpdate calendarNoncallOutcome
    rw [calendarNoncallCell_fill_live rate rewards C_star C_h control0 b0 u0 t0 k hk w hl x]
    cases hp : (continuingBefore rate rewards C_star C_h q ⟨current k hk.le w, hl⟩).overflow
    · simp only [Option.map_some, cellUpdate, ReferencePostInvocationCollectionNativeLaw.optionalOutcome,
        ReferencePostInvocationCollectionNativeLaw.cellOutcome,
        ReferencePostInvocationLiveNativeLaw.controlledCell,
        ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates,
        calendarNoncallUpdateForOutcome, dite_eq_left hl, numericalUpdate,
        ReferencePostInvocationLiveNativeLaw.inputForMarker, hp,
        Bool.false_eq_true, ite_false]
    ·
      simp only [Option.map_some, cellUpdate, ReferencePostInvocationCollectionNativeLaw.optionalOutcome,
        ReferencePostInvocationCollectionNativeLaw.cellOutcome,
        ReferencePostInvocationLiveNativeLaw.controlledCell,
        ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates,
        calendarNoncallUpdateForOutcome, dite_eq_left hl, numericalUpdate,
        ReferencePostInvocationLiveNativeLaw.inputForMarker, hp,
        ite_true,
        RecordedQueueRun.step, acceptedRecord_stopped rate _ hp]
  · have hcol := (calendarNoncall_phase rate rewards C_star C_h control0 b0 u0 t0 k hk w hc).resolve_left hl
    unfold calendarNoncallUpdate calendarNoncallOutcome
    rw [calendarNoncallCell_fill_collection rate rewards C_star C_h control0 b0 u0 t0 k hk w hl hcol x]
    let z : CollectionDateSource rate rewards C_star C_h q := ⟨current k hk.le w, hcol⟩
    rw [laterCollectionCell?, ReferencePostInvocationCollectionNativeLaw.collectionEnabled_replace_control]
    cases hen : (collectionInput rate rewards C_star C_h q z).enabled with
    | false =>
      dsimp only [z] at hen
      simp only [Bool.false_eq_true, ite_false, Option.map_none,
        ReferencePostInvocationCollectionNativeLaw.optionalOutcome, calendarNoncallUpdateForOutcome]
    | true =>
      dsimp only [z] at hen
      simp only [ite_true, Option.map_some, cellUpdate,
        ReferencePostInvocationCollectionNativeLaw.optionalOutcome,
        ReferencePostInvocationCollectionNativeLaw.cellOutcome, laterCollectionCell,
        ReferencePostInvocationCollectionNativeLaw.collectionBefore_replace_control,
        ReferencePostInvocationCollectionNativeLaw.collectionInput_replace_control,
        ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates]
      cases hp : (collectionBefore rate rewards C_star C_h q z).overflow
      · dsimp only [z] at hp
        simp only [Bool.false_eq_true, ite_false, calendarNoncallUpdateForOutcome,
          dite_eq_right hl, dite_eq_left hcol, numericalUpdate,
          ReferencePostInvocationCollectionNativeLaw.markerRound]
      · dsimp only [z] at hp
        simp only [hp, ite_true, calendarNoncallUpdateForOutcome,
          dite_eq_right hl, dite_eq_left hcol, numericalUpdate,
          ReferencePostInvocationCollectionNativeLaw.markerRound,
          RecordedQueueRun.step, acceptedRecord_stopped rate _ hp]

end NumericalRefill

/-- Evaluated joint law of the SAME proper past, optional full numerical
UPDATE and effective outcome. The coefficient sum includes every absent,
bottom, stopped, null and out-of-complement atom, without renormalization. -/
theorem calendarLaw_noncall_update_test (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (F : (Source × (SlowSet p × List (LogicalCell p rate))) ×
      (Option (NumericalUpdate p) × Outcome) → ℝ≥0∞) (hF : Measurable F) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    (∫⁻ wv : Sample k × Vector, if callFlag k (by omega) wv.1 = false then
      F (past k hk.le wv.1, (update k hk wv.1, outcome k hk wv.1)) else 0
      ∂law (k + 1) (by omega)) =
      ∫⁻ w, if callFlag k (by omega) w = false then
        ∑ o, F (past k hk.le w, (updateFor k hk w o, o)) * mass k hk w o else 0
        ∂(law k hk.le).map (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q
          (noncallDate_after t0 k) k) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k
  let test : Sample k × Vector → ℝ≥0∞ := fun wv =>
    if callFlag k (by omega) wv.1 = false then
      F (past k hk.le wv.1, (update k hk wv.1, outcome k hk wv.1)) else 0
  have hp := measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le
  have ho := measurable_calendarNoncallOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk
  have hu := measurable_calendarNoncallUpdate rate rewards C_star C_h control0 b0 u0 t0 k hk
  have hgate := measurableSet_eq_fun
    (measurable_calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega))
    (measurable_const (a := false))
  have ht : Measurable test := ((hF.comp (hp.prodMk (hu.prodMk ho))).comp measurable_fst).ite
    (hgate.preimage measurable_fst) measurable_const
  refine (calendarLaw_round_innovation_test rate rewards C_star C_h control0 b0 u0 t0 q
    (noncallDate_after t0 k) k hk le_rfl test ht).trans ?_
  apply lintegral_congr
  intro w
  change (∫⁻ x, ∫⁻ v, test (fill (w, x), v) ∂extension k (by omega) (fill (w, x))
    ∂innovationLaw (p := p)) = _
  by_cases hc : callFlag k (by omega) w = false
  · rw [ite_eq_left hc]
    have he (x : Innovation p) :
        (∫⁻ v, test (fill (w, x), v) ∂extension k (by omega) (fill (w, x))) =
        F (past k hk.le w, (updateFor k hk w (outcome k hk (fill (w, x))),
          outcome k hk (fill (w, x)))) := by
      have hc' : callFlag k (by omega) (fill (w, x)) = false :=
        (calendarCallFlag_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w x).trans hc
      have hn : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q
          (current k hk.le (fill (w, x))) = none := by
        apply Option.not_isSome_iff_eq_none.mp
        change ¬ callFlag k (by omega) (fill (w, x)) = true
        rw [hc']
        exact Bool.false_ne_true
      rw [calendarExtensionKernel_noCall rate rewards C_star C_h control0 b0 u0 t0 k hk _ hn, lintegral_dirac]
      dsimp only [test]
      rw [ite_eq_left hc', calendarRoundPast_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
        (noncallDate_after t0 k) k hk.le le_rfl,
        calendarNoncallUpdate_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w hc x]
    simp_rw [he]
    exact calendarNoncallOutcome_refill_test rate rewards C_star C_h control0 b0 u0 t0 k hk w hc
      (fun o => F (past k hk.le w, (updateFor k hk w o, o)))
  · rw [ite_eq_right hc]
    have he (x : Innovation p) (v : Vector) : test (fill (w, x), v) = 0 := by
      dsimp only [test]
      rw [calendarCallFlag_fillInnovation, ite_eq_right hc]
    simp_rw [he, lintegral_zero]

/-- Present bottom recording is an enabled all-queue service step. Its
stored cell and first-overflow POST remain available through `actualInput`. -/
theorem calendarNoncall_bottom_service (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (v : Vector) (hc : callFlag k (by omega) w = false) (e : LogicalCell p rate)
    (he : cell k hk w = some e) (hpre : e.before.overflow = false)
    (hbottom : e.numerical.2.1 = none) :
    ∀ j, e.arrivals j = (true, 0) ∧ e.service j =
      min (4 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).n) (e.before.registers j).2 := by
  obtain ⟨r, input, _hr, _hi, hen, _ht, _hp, hn, _hb, _hstep, harr, hservice, _hs, _ha⟩ :=
    calendarNoncallCell_actualInput rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc e he
  have hi : input.recordedArm = none :=
    (congrArg (fun c : ReferenceFirstLiveOverflowReadout.NumericalCellReadout p => c.2.1) hn).symm.trans hbottom
  intro j
  rw [hservice, harr]
  simp only [RecordedQueueRun.acceptedRecord, hpre, Bool.false_eq_true, ite_false, hen, ite_true,
    RecordedQueueRun.quantizedArrival, hi, reduceCtorEq, RecordedQueueRun.recordService,
    CappedService.service, Nat.add_zero, and_self]

/-- PRE overflow keeps the physical input but accepts no service. Full
numerical histories advance by their false no-op record. -/
theorem calendarNoncall_stopped_update (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (v : Vector) (hc : callFlag k (by omega) w = false) (e : LogicalCell p rate)
    (he : cell k hk w = some e) (hpre : e.before.overflow = true) :
    ∀ j, e.arrivals j = (false, 0) ∧ e.service j = 0 ∧
      e.after.registers j = e.before.registers j ∧ e.after.records j = e.before.records j ++ [(false, 0)] := by
  obtain ⟨r, input, _hr, _hi, _hen, _ht, _hp, _hn, _hb, hstep, harr, hservice, _hs, _ha⟩ :=
    calendarNoncallCell_actualInput rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc e he
  intro j
  rw [hservice, harr, hstep]
  simp only [RecordedQueueRun.acceptedRecord, hpre, ite_true, RecordedQueueRun.recordService,
    Bool.false_eq_true, ite_false, RecordedQueueRun.step, QueueReplay.transition, and_self]

omit rate rewards C_star C_h control0 b0 u0 t0 in
def outcomeMarker (o : Outcome) : Option (Fin p.K) :=
  match o with
  | .inl _ => none
  | .inr (i, _, _, _) => i

omit rewards C_star C_h control0 b0 u0 t0 in
/-- The raw recorder of a present cell, before effective stopping. The
separate outcome tag distinguishes an absent cell from present bottom. -/
def optionalRawMarker (e : Option (LogicalCell p rate)) : Option (Fin p.K) :=
  match e with
  | none => none
  | some e => e.numerical.2.1

omit rewards C_star C_h control0 b0 u0 t0 in
theorem measurable_optionalRawMarker : Measurable (optionalRawMarker rate) := by
  let f : LogicalCell p rate ⊕ PUnit → Option (Fin p.K) :=
    Sum.elim (fun e => e.numerical.2.1) (fun _ => none)
  have hf : Measurable f :=
    ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_numerical.snd.fst.sumElim measurable_const
  convert hf.comp (comap_measurable (Equiv.optionEquivSumPUnit.{0, 0} (LogicalCell p rate))) using 1
  funext e
  cases e <;> rfl

def calendarNoncallRawMarker (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k) :
    Option (Fin p.K) := optionalRawMarker rate (cell k hk w)

local notation "rawMarker" => calendarNoncallRawMarker rate rewards C_star C_h control0 b0 u0 t0

theorem measurable_calendarNoncallRawMarker (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    Measurable (rawMarker k hk) :=
  (measurable_optionalRawMarker rate).comp
    (measurable_calendarNoncallCell rate rewards C_star C_h control0 b0 u0 t0 k hk)

/-- Joint raw-recorder/effective coefficients. PRE overflow preserves the
raw recorder law while concentrating only the effective tuple at its frozen
value. This is not the law obtained by zeroing the physical recorder. -/
def calendarNoncallRawMass (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (i : Option (Fin p.K)) (o : Outcome) : ℝ≥0∞ :=
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  if hl : current k hk.le w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q then
    if (continuingBefore rate rewards C_star C_h q ⟨current k hk.le w, hl⟩).overflow then
      (∑ j : Fin p.K, ReferencePostInvocationLiveNativeLaw.nativePairLaw rate rewards C_star C_h q
        ⟨current k hk.le w, hl⟩ {(i, j)}) *
          (if o = Sum.inr (none, frozenFastArm p, false, frozenSlowSet p) then 1 else 0)
    else if outcomeMarker o = i then mass k hk w o else 0
  else if hc : current k hk.le w ∈ collectionDateDomain rate rewards C_star C_h q then
    if (collectionInput rate rewards C_star C_h q ⟨current k hk.le w, hc⟩).enabled then
      if (collectionBefore rate rewards C_star C_h q ⟨current k hk.le w, hc⟩).overflow then
        ReferencePostInvocationCollectionNativeLaw.recorderPMF rate rewards C_star C_h q
          ⟨current k hk.le w, hc⟩ i *
            (if o = Sum.inr (none, frozenFastArm p, false, frozenSlowSet p) then 1 else 0)
      else if outcomeMarker o = i then mass k hk w o else 0
    else if i = none ∧ o = Sum.inl () then 1 else 0
  else if i = none ∧ o = Sum.inl () then 1 else 0

local notation "rawMass" => calendarNoncallRawMass rate rewards C_star C_h control0 b0 u0 t0

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem sum_marker_join (f : Option (Fin p.K) × Outcome → ℝ≥0∞) (m : Outcome → ℝ≥0∞) :
    (∑ o, f (outcomeMarker o, o) * m o) =
      ∑ i, ∑ o, f (i, o) * (if outcomeMarker o = i then m o else 0) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _ho
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem sum_frozen_join (f : Option (Fin p.K) × Outcome → ℝ≥0∞)
    (m : Option (Fin p.K) → ℝ≥0∞) (a : Outcome) :
    (∑ i, f (i, a) * m i) = ∑ i, ∑ o, f (i, o) * (m i * (if o = a then 1 else 0)) := by
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_eq_single a]
  · simp only [ite_true, mul_one]
  · intro b _hb hba
    rw [ite_eq_right hba, mul_zero, mul_zero]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

omit rate rewards C_star C_h control0 b0 u0 t0 in
private theorem lintegral_innovation_fst (f : Control → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : Innovation p, f x.1 ∂innovationLaw (p := p)) =
      ∫⁻ c, f c ∂ContinuousLearningRows.timeControlLaw p :=
  (measurePreserving_fst (μ := ContinuousLearningRows.timeControlLaw p)
    (ν := ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)).lintegral_comp hf

/-- Raw recorder and stopped/unstopped effective output evaluated jointly
at the actual generated source. All raw physical recorder atoms survive
incoming overflow. -/
theorem calendarNoncallRaw_refill_test (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (hc : callFlag k (by omega) w = false)
    (f : Option (Fin p.K) × Outcome → ℝ≥0∞) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k
    (∫⁻ x, f (rawMarker k hk (fill (w, x)), outcome k hk (fill (w, x))) ∂innovationLaw (p := p)) =
      ∑ i, ∑ o, f (i, o) * rawMass k hk w i o := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k
  let frozen : Outcome := Sum.inr (none, frozenFastArm p, false, frozenSlowSet p)
  change (∫⁻ x, f (rawMarker k hk (fill (w, x)), outcome k hk (fill (w, x))) ∂innovationLaw (p := p)) = _
  by_cases hl : current k hk.le w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q
  · dsimp only [q] at hl
    let z : ContinuingLiveSource rate rewards C_star C_h q := ⟨current k hk.le w, hl⟩
    cases hp : (continuingBefore rate rewards C_star C_h q z).overflow with
    | false =>
      dsimp only [q, z] at hp
      have he (x : Innovation p) : rawMarker k hk (fill (w, x)) = outcomeMarker (outcome k hk (fill (w, x))) := by
        unfold calendarNoncallRawMarker calendarNoncallOutcome
        rw [calendarNoncallCell_fill_live rate rewards C_star C_h control0 b0 u0 t0 k hk w hl x]
        simp only [optionalRawMarker, ReferencePostInvocationCollectionNativeLaw.optionalOutcome,
          ReferencePostInvocationCollectionNativeLaw.cellOutcome, ReferencePostInvocationLiveNativeLaw.controlledCell,
          outcomeMarker, hp, Bool.false_eq_true, ite_false]
      simp_rw [he]
      refine (calendarNoncallOutcome_refill_test rate rewards C_star C_h control0 b0 u0 t0 k hk w hc
        (fun o => f (outcomeMarker o, o))).trans ?_
      rw [sum_marker_join]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro o _ho
      simp only [calendarNoncallRawMass, dite_eq_left hl, hp, Bool.false_eq_true, ite_false]
    | true =>
      dsimp only [q, z] at hp
      have he (x : Innovation p) :
          (rawMarker k hk (fill (w, x)), outcome k hk (fill (w, x))) =
          ((ReferencePostInvocationLiveNativeLaw.physicalPair rate rewards C_star C_h q z x.1).1, frozen) := by
        unfold calendarNoncallRawMarker calendarNoncallOutcome
        rw [calendarNoncallCell_fill_live rate rewards C_star C_h control0 b0 u0 t0 k hk w hl x]
        simp only [optionalRawMarker, ReferencePostInvocationCollectionNativeLaw.optionalOutcome,
          ReferencePostInvocationCollectionNativeLaw.cellOutcome, ReferencePostInvocationLiveNativeLaw.controlledCell,
          ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates,
          ReferencePostInvocationLiveNativeLaw.inputForMarker, hp, ite_true, Bool.not_true, Bool.false_and, frozen]
        rfl
      simp_rw [he]
      have hm := ReferencePostInvocationLiveNativeLaw.physicalPair_law rate rewards C_star C_h q z
      refine (lintegral_innovation_fst
        (fun c => f ((ReferencePostInvocationLiveNativeLaw.physicalPair rate rewards C_star C_h q z c).1, frozen))
        ((measurable_of_finite (fun y : Option (Fin p.K) × Fin p.K => f (y.1, frozen))).comp hm.1)).trans ?_
      change (∫⁻ c, (fun y : Option (Fin p.K) × Fin p.K => f (y.1, frozen))
        (ReferencePostInvocationLiveNativeLaw.physicalPair rate rewards C_star C_h q z c)
        ∂ContinuousLearningRows.timeControlLaw p) = _
      rw [← lintegral_map (measurable_of_finite (fun y : Option (Fin p.K) × Fin p.K => f (y.1, frozen))) hm.1,
        hm.2, lintegral_fintype, Fintype.sum_prod_type]
      simp only [calendarNoncallRawMass, dite_eq_left hl, hp, ite_true]
      rw [← sum_frozen_join f (fun i => ∑ j : Fin p.K,
        ReferencePostInvocationLiveNativeLaw.nativePairLaw rate rewards C_star C_h q z {(i, j)}) frozen]
      apply Finset.sum_congr rfl
      intro i _hi
      exact (Finset.mul_sum _ _ _).symm
  · dsimp only [q] at hl
    have hcol := (calendarNoncall_phase rate rewards C_star C_h control0 b0 u0 t0 k hk w hc).resolve_left hl
    let z : CollectionDateSource rate rewards C_star C_h q := ⟨current k hk.le w, hcol⟩
    cases hen : (collectionInput rate rewards C_star C_h q z).enabled with
    | false =>
      dsimp only [q, z] at hen
      have he (x : Innovation p) :
          (rawMarker k hk (fill (w, x)), outcome k hk (fill (w, x))) = (none, Sum.inl ()) := by
        unfold calendarNoncallRawMarker calendarNoncallOutcome
        rw [calendarNoncallCell_fill_collection rate rewards C_star C_h control0 b0 u0 t0 k hk w hl hcol x,
          laterCollectionCell?, ReferencePostInvocationCollectionNativeLaw.collectionEnabled_replace_control]
        simp only [hen, Bool.false_eq_true, ite_false, optionalRawMarker,
          ReferencePostInvocationCollectionNativeLaw.optionalOutcome]
      simp_rw [he]
      simp [calendarNoncallRawMass, hl, hcol, hen]
    | true =>
      dsimp only [q, z] at hen
      cases hp : (collectionBefore rate rewards C_star C_h q z).overflow with
      | false =>
        dsimp only [q, z] at hp
        have he (x : Innovation p) : rawMarker k hk (fill (w, x)) = outcomeMarker (outcome k hk (fill (w, x))) := by
          unfold calendarNoncallRawMarker calendarNoncallOutcome
          rw [calendarNoncallCell_fill_collection rate rewards C_star C_h control0 b0 u0 t0 k hk w hl hcol x,
            laterCollectionCell?, ReferencePostInvocationCollectionNativeLaw.collectionEnabled_replace_control]
          simp only [hen, ite_true, optionalRawMarker, ReferencePostInvocationCollectionNativeLaw.optionalOutcome,
            ReferencePostInvocationCollectionNativeLaw.cellOutcome, laterCollectionCell,
            ReferencePostInvocationCollectionNativeLaw.collectionBefore_replace_control, outcomeMarker,
            hp, Bool.false_eq_true, ite_false]
        simp_rw [he]
        refine (calendarNoncallOutcome_refill_test rate rewards C_star C_h control0 b0 u0 t0 k hk w hc
          (fun o => f (outcomeMarker o, o))).trans ?_
        rw [sum_marker_join]
        simp only [calendarNoncallRawMass, dite_eq_right hl, dite_eq_left hcol, hen, hp,
          ite_true, Bool.false_eq_true, ite_false]
      | true =>
        dsimp only [q, z] at hp
        have he (x : Innovation p) :
            (rawMarker k hk (fill (w, x)), outcome k hk (fill (w, x))) =
              (ReferencePostInvocationCollectionNativeLaw.nativeRecorder rate rewards C_star C_h q z x.1, frozen) := by
          unfold calendarNoncallRawMarker calendarNoncallOutcome
          rw [calendarNoncallCell_fill_collection rate rewards C_star C_h control0 b0 u0 t0 k hk w hl hcol x,
            laterCollectionCell?, ReferencePostInvocationCollectionNativeLaw.collectionEnabled_replace_control]
          simp only [hen, ite_true, optionalRawMarker, ReferencePostInvocationCollectionNativeLaw.optionalOutcome,
            ReferencePostInvocationCollectionNativeLaw.cellOutcome, laterCollectionCell,
            ReferencePostInvocationCollectionNativeLaw.collectionBefore_replace_control,
            ReferencePostInvocationCollectionNativeLaw.collectionInput_replace_control,
            ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates,
            ReferencePostInvocationCollectionNativeLaw.markerRound, hp, ite_true,
            Bool.not_true, Bool.and_false, Bool.false_and, frozen]
          rfl
        simp_rw [he]
        have hm := ReferencePostInvocationCollectionNativeLaw.measurable_nativeRecorder rate rewards C_star C_h q z
        refine (lintegral_innovation_fst
          (fun c => f (ReferencePostInvocationCollectionNativeLaw.nativeRecorder rate rewards C_star C_h q z c, frozen))
          ((measurable_of_finite (fun i => f (i, frozen))).comp hm)).trans ?_
        change (∫⁻ c, (fun i => f (i, frozen))
          (ReferencePostInvocationCollectionNativeLaw.nativeRecorder rate rewards C_star C_h q z c)
          ∂ContinuousLearningRows.timeControlLaw p) = _
        rw [← lintegral_map (measurable_of_finite (fun i => f (i, frozen))) hm,
          ReferencePostInvocationCollectionNativeLaw.nativeRecorder_map rate rewards C_star C_h q z hen,
          lintegral_fintype]
        simp only [calendarNoncallRawMass, dite_eq_right hl, dite_eq_left hcol, hen, hp, ite_true]
        rw [← sum_frozen_join f (ReferencePostInvocationCollectionNativeLaw.recorderPMF rate rewards C_star C_h q z) frozen]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [PMF.toMeasure_apply_singleton _ i (measurableSet_singleton i)]

/-- Raw numerical coordinates of the actual optional cell. In particular
its physical recorder is retained on a stopped, enabled date. -/
def calendarNoncallNumerical (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k) :
    Option (ReferenceFirstLiveOverflowReadout.NumericalCellReadout p) :=
  (cell k hk w).map (fun e => e.numerical)

local notation "numerical" => calendarNoncallNumerical rate rewards C_star C_h control0 b0 u0 t0

theorem measurable_calendarNoncallNumerical (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    Measurable (numerical k hk) :=
  LaterAssignmentFullOutputMeasurability.measurable_optionMap _
    ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_numerical _
    (measurable_calendarNoncallCell rate rewards C_star C_h control0 b0 u0 t0 k hk)

/-- Same-source frozen rates, reward row and nominal enablement, together
with a specified raw physical recorder. Absence is selected by the outcome. -/
def calendarNoncallNumericalForRaw (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (i : Option (Fin p.K)) (o : Outcome) : Option (ReferenceFirstLiveOverflowReadout.NumericalCellReadout p) :=
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  match o with
  | .inl _ => none
  | .inr _ =>
    if hl : current k hk.le w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
        rate rewards C_star C_h q then
      some (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
        (ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q ⟨current k hk.le w, hl⟩ i))
    else if hc : current k hk.le w ∈ collectionDateDomain rate rewards C_star C_h q then
      some (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
        (ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q ⟨current k hk.le w, hc⟩ i))
    else none

local notation "numericalFor" => calendarNoncallNumericalForRaw rate rewards C_star C_h control0 b0 u0 t0

theorem calendarNoncallNumerical_fillInnovation (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (w : Sample k) (hc : callFlag k (by omega) w = false) (x : Innovation p) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k
    numerical k hk (fill (w, x)) = numericalFor k hk w
      (rawMarker k hk (fill (w, x))) (outcome k hk (fill (w, x))) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  by_cases hl : current k hk.le w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q
  · dsimp only [q] at hl
    unfold calendarNoncallNumerical calendarNoncallRawMarker calendarNoncallOutcome
    rw [calendarNoncallCell_fill_live rate rewards C_star C_h control0 b0 u0 t0 k hk w hl x]
    simp only [Option.map_some, optionalRawMarker, ReferencePostInvocationCollectionNativeLaw.optionalOutcome,
      ReferencePostInvocationCollectionNativeLaw.cellOutcome, ReferencePostInvocationLiveNativeLaw.controlledCell,
      calendarNoncallNumericalForRaw, dite_eq_left hl,
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates,
      ReferencePostInvocationLiveNativeLaw.inputForMarker]
  · dsimp only [q] at hl
    have hcol := (calendarNoncall_phase rate rewards C_star C_h control0 b0 u0 t0 k hk w hc).resolve_left hl
    unfold calendarNoncallNumerical calendarNoncallRawMarker calendarNoncallOutcome
    rw [calendarNoncallCell_fill_collection rate rewards C_star C_h control0 b0 u0 t0 k hk w hl hcol x,
      laterCollectionCell?, ReferencePostInvocationCollectionNativeLaw.collectionEnabled_replace_control]
    cases hen : (collectionInput rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
      ⟨current k hk.le w, hcol⟩).enabled <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, Option.map_none, Option.map_some,
        optionalRawMarker, ReferencePostInvocationCollectionNativeLaw.optionalOutcome,
        ReferencePostInvocationCollectionNativeLaw.cellOutcome, laterCollectionCell,
        ReferencePostInvocationCollectionNativeLaw.collectionInput_replace_control,
        calendarNoncallNumericalForRaw, dite_eq_right hl, dite_eq_left hcol,
        ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates,
        ReferencePostInvocationCollectionNativeLaw.markerRound]

/-- Full evaluated noncall numerical round law, jointly with the canonical
proper past, hidden seed and WHOLE native archive. Raw enablement, recorder,
rates and rewards are tested beside PRE, accepted arrivals, service, POST and
the effective outcome. The first overflow UPDATE is never removed. -/
theorem calendarLaw_noncall_numerical_test (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (F : (Source × (SlowSet p × List (LogicalCell p rate))) ×
      (Option (ReferenceFirstLiveOverflowReadout.NumericalCellReadout p) ×
        (Option (NumericalUpdate p) × Outcome)) → ℝ≥0∞) (hF : Measurable F) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    (∫⁻ wv : Sample k × Vector, if callFlag k (by omega) wv.1 = false then
      F (past k hk.le wv.1, (numerical k hk wv.1, (update k hk wv.1, outcome k hk wv.1))) else 0
      ∂law (k + 1) (by omega)) =
      ∫⁻ w, if callFlag k (by omega) w = false then
        ∑ i, ∑ o, F (past k hk.le w, (numericalFor k hk w i o, (updateFor k hk w o, o))) *
          rawMass k hk w i o else 0 ∂(law k hk.le).map
            (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k) := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k
  let test : Sample k × Vector → ℝ≥0∞ := fun wv =>
    if callFlag k (by omega) wv.1 = false then
      F (past k hk.le wv.1, (numerical k hk wv.1, (update k hk wv.1, outcome k hk wv.1))) else 0
  have hp := measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le
  have ho := measurable_calendarNoncallOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk
  have hu := measurable_calendarNoncallUpdate rate rewards C_star C_h control0 b0 u0 t0 k hk
  have hn := measurable_calendarNoncallNumerical rate rewards C_star C_h control0 b0 u0 t0 k hk
  have hgate := measurableSet_eq_fun
    (measurable_calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega))
    (measurable_const (a := false))
  have ht : Measurable test := ((hF.comp (hp.prodMk (hn.prodMk (hu.prodMk ho)))).comp measurable_fst).ite
    (hgate.preimage measurable_fst) measurable_const
  refine (calendarLaw_round_innovation_test rate rewards C_star C_h control0 b0 u0 t0 q
    (noncallDate_after t0 k) k hk le_rfl test ht).trans ?_
  apply lintegral_congr
  intro w
  change (∫⁻ x, ∫⁻ v, test (fill (w, x), v) ∂extension k (by omega) (fill (w, x))
    ∂innovationLaw (p := p)) = _
  by_cases hc : callFlag k (by omega) w = false
  · rw [ite_eq_left hc]
    have he (x : Innovation p) :
        (∫⁻ v, test (fill (w, x), v) ∂extension k (by omega) (fill (w, x))) =
        F (past k hk.le w, (numericalFor k hk w (rawMarker k hk (fill (w, x))) (outcome k hk (fill (w, x))),
          (updateFor k hk w (outcome k hk (fill (w, x))), outcome k hk (fill (w, x))))) := by
      have hc' : callFlag k (by omega) (fill (w, x)) = false :=
        (calendarCallFlag_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w x).trans hc
      have hncall : ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h q
          (current k hk.le (fill (w, x))) = none := by
        apply Option.not_isSome_iff_eq_none.mp
        change ¬ callFlag k (by omega) (fill (w, x)) = true
        rw [hc']
        exact Bool.false_ne_true
      rw [calendarExtensionKernel_noCall rate rewards C_star C_h control0 b0 u0 t0 k hk _ hncall, lintegral_dirac]
      dsimp only [test]
      rw [ite_eq_left hc', calendarRoundPast_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
        (noncallDate_after t0 k) k hk.le le_rfl,
        calendarNoncallUpdate_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w hc x,
        calendarNoncallNumerical_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w hc x]
    simp_rw [he]
    exact calendarNoncallRaw_refill_test rate rewards C_star C_h control0 b0 u0 t0 k hk w hc
      (fun io => F (past k hk.le w, (numericalFor k hk w io.1 io.2, (updateFor k hk w io.2, io.2))))
  · rw [ite_eq_right hc]
    have he (x : Innovation p) (v : Vector) : test (fill (w, x), v) = 0 := by
      dsimp only [test]
      rw [calendarCallFlag_fillInnovation, ite_eq_right hc]
    simp_rw [he, lintegral_zero]

/-- Actual clear LIVE agreement is produced by the accepted generated
geometry, with the same hidden seed and original array. -/
theorem calendarNoncall_live_seed (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (hl : current k hk.le w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩)
    (hclear : (calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w).2 = true) :
    (stored k hk.le w).1 = (continuingSourceCell rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
      ⟨current k hk.le w, hl⟩).selected.view.payload.slowSet :=
  (calendarObservation_live_seed rate rewards C_star C_h control0 b0 u0 t0 k hk w hl hclear).1

/-- A disabled noncall has literal optional absence and preserves the
logical seed/list and score/backlog registers. Its numerical calendar
boundary still advances by one false record per arm, including at `T`. -/
theorem calendarNoncall_disabled (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (v : Vector) (hc : callFlag k (by omega) w = false)
    (hdisabled : ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      ⟨t0.val + 1 + k, hk⟩ (current k hk.le w)).bind
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).any RecordedQueueRun.RoundInput.enabled = false) :
    let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
    cell k hk w = none ∧ outcome k hk w = Sum.inl () ∧
      stored (k + 1) (by omega) (w, v) = stored k hk.le w ∧
      ∃ (input : RecordedQueueRun.RoundInput p.K) (S : RecordedQueueRun.RunState p.K),
        (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q (current k hk.le w)).bind
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some input ∧ input.enabled = false ∧
        (observe k hk.le w).2.val.2.2.1 = some S ∧
        (observe (k + 1) (by omega) (w, v)).2.val.2.2.1 = some (RecordedQueueRun.step Q S input) ∧
        ∀ j, (RecordedQueueRun.step Q S input).registers j = S.registers j ∧
          (RecordedQueueRun.step Q S input).records j = S.records j ++ [(false, 0)] := by
  dsimp only
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  have he : cell k hk w = none := by
    apply Option.not_isSome_iff_eq_none.mp
    have hp := calendarObservation_noncall_presence rate rewards C_star C_h control0 b0 u0 t0 k hk w hc
    change (cell k hk w).isSome = _ at hp
    rw [hp]
    intro ht
    exact Bool.false_ne_true (hdisabled.symm.trans ht)
  refine ⟨he, ?_, calendarObservation_noncall_absent rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc he, ?_⟩
  · simp only [calendarNoncallOutcome, he, ReferencePostInvocationCollectionNativeLaw.optionalOutcome]
  · have hl : current k hk.le w ∉ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
        rate rewards C_star C_h q := by
      intro hl
      have he' := he
      unfold calendarNoncallCell at he'
      rw [noncallDateCell, dite_eq_left hl] at he'
      cases he'
    have hcol := (calendarNoncall_phase rate rewards C_star C_h control0 b0 u0 t0 k hk w hc).resolve_left hl
    let z : CollectionDateSource rate rewards C_star C_h q := ⟨current k hk.le w, hcol⟩
    let input := collectionInput rate rewards C_star C_h q z
    let S := collectionBefore rate rewards C_star C_h q z
    have hr := (collectionRecord_spec rate rewards C_star C_h q z).1
    have hi : (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z.val).bind
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some input := by
      rw [hr, Option.bind_some]
      exact (Option.some_get _).symm
    have hen : input.enabled = false := by
      change ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z.val).bind
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).any RecordedQueueRun.RoundInput.enabled = false at hdisabled
      rwa [hi, Option.any_some] at hdisabled
    refine ⟨input, S, hi, hen, ?_, ?_, ?_⟩
    · exact (calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).trans
        (collectionBefore_spec rate rewards C_star C_h q z)
    · rw [calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega) (w, v)]
      change prefixNumerical rate rewards C_star C_h q.succ (current (k + 1) (by omega) (w, v)) = _
      rw [calendarCurrentSource_succ rate rewards C_star C_h control0 b0 u0 t0 k hk]
      simp only [hc, Bool.false_eq_true, ite_false]
      have hstart := (collectionInput_word rate rewards C_star C_h q z).choose_spec.1
      rw [prefixNumerical_actualWord rate rewards C_star C_h q.succ z.val
        (collection_launch rate rewards C_star C_h q z) (hstart.trans (Nat.le_succ _))]
      exact congrArg some (laterCollectionCell_after rate rewards C_star C_h q z
        (stored k hk.le w).1 (original k w).1.2).symm
    · intro j
      simp only [RecordedQueueRun.step, RecordedQueueRun.acceptedRecord, hen,
        Bool.false_eq_true, ite_false, ite_self, QueueReplay.transition, and_self]

/-- The effective logical tuple freezes on incoming overflow while the
same cell retains its original physical/numerical input. -/
theorem calendarNoncall_stopped_tuple (k : ℕ) (hk : t0.val + 1 + k < p.T) (w : Sample k)
    (e : LogicalCell p rate) (he : cell k hk w = some e) (hpre : e.before.overflow = true) :
    e.slowSet = frozenSlowSet p ∧ e.fastArm = frozenFastArm p ∧ e.proposal = false ∧
      e.nextSlowSet = frozenSlowSet p := by
  unfold calendarNoncallCell noncallDateCell at he
  split at he
  next hl =>
    rw [← Option.some.inj he] at hpre ⊢
    change (continuingBefore rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
      ⟨current k hk.le w, hl⟩).overflow = true at hpre
    simp only [continuingLogicalCell, appendLogicalCell, hpre, ite_true,
      Bool.not_true, Bool.false_and, and_self]
  next _ =>
    split at he
    next hcol =>
      unfold laterCollectionCell? at he
      split at he
      next _hen =>
        rw [← Option.some.inj he] at hpre ⊢
        change (collectionBefore rate rewards C_star C_h ⟨t0.val + 1 + k, hk⟩
          ⟨current k hk.le w, hcol⟩).overflow = true at hpre
        simp only [laterCollectionCell, hpre, ite_true,
          Bool.not_true, Bool.and_false, Bool.false_and, and_self]
      next _ => cases he
    next _ => cases he

/-- The evaluated numerical-test family is measurable in the incoming
generated sample. Its measurability is proved from the actual refill, rather
than supplied as a new kernel hypothesis. -/
theorem measurable_calendarNoncallNumerical_test (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (F : (Source × (SlowSet p × List (LogicalCell p rate))) ×
      (Option (ReferenceFirstLiveOverflowReadout.NumericalCellReadout p) ×
        (Option (NumericalUpdate p) × Outcome)) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun w : Sample k => if callFlag k (by omega) w = false then
      ∑ i, ∑ o, F (past k hk.le w, (numericalFor k hk w i o, (updateFor k hk w o, o))) *
        rawMass k hk w i o else 0) := by
  let q : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let fill := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k
  let g : Sample k × Innovation p → ℝ≥0∞ := fun wx =>
    if callFlag k (by omega) wx.1 = false then
      F (past k hk.le wx.1, (numerical k hk (fill wx), (update k hk (fill wx), outcome k hk (fill wx)))) else 0
  have hf := measurable_calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k
  have hp : Measurable (fun wx : Sample k × Innovation p => past k hk.le wx.1) :=
    (measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le).comp measurable_fst
  have hn := (measurable_calendarNoncallNumerical rate rewards C_star C_h control0 b0 u0 t0 k hk).comp hf
  have hu := (measurable_calendarNoncallUpdate rate rewards C_star C_h control0 b0 u0 t0 k hk).comp hf
  have ho := (measurable_calendarNoncallOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk).comp hf
  have hgate := measurableSet_eq_fun
    (measurable_calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega))
    (measurable_const (a := false))
  have hg : Measurable g := (hF.comp (hp.prodMk (hn.prodMk (hu.prodMk ho)))).ite
    (hgate.preimage measurable_fst) measurable_const
  have he (w : Sample k) : (∫⁻ x, g (w, x) ∂innovationLaw (p := p)) =
      if callFlag k (by omega) w = false then
        ∑ i, ∑ o, F (past k hk.le w, (numericalFor k hk w i o, (updateFor k hk w o, o))) *
          rawMass k hk w i o else 0 := by
    by_cases hc : callFlag k (by omega) w = false
    · rw [ite_eq_left hc]
      have he (x : Innovation p) : g (w, x) =
          F (past k hk.le w, (numericalFor k hk w (rawMarker k hk (fill (w, x))) (outcome k hk (fill (w, x))),
            (updateFor k hk w (outcome k hk (fill (w, x))), outcome k hk (fill (w, x))))) := by
        dsimp only [g]
        rw [ite_eq_left hc, calendarNoncallNumerical_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w hc x,
          calendarNoncallUpdate_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 k hk w hc x]
      simp_rw [he]
      exact calendarNoncallRaw_refill_test rate rewards C_star C_h control0 b0 u0 t0 k hk w hc
        (fun io => F (past k hk.le w, (numericalFor k hk w io.1 io.2, (updateFor k hk w io.2, io.2))))
    · simp only [g, ite_eq_right hc, lintegral_zero]
  have heq := funext he
  rw [← heq]
  exact hg.lintegral_prod_right'

end Bandits.Support.ReferenceGeneratedCalendarNoncallRoundLaw

end
