/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodePrefixRecombination
public import Bandits.Support.ReferenceGeneratedCalendarRoundLaw

import Mathlib.Tactic

/-!
# Initialization at actual collection renewals after the first invocation

The opportunity below reads the incoming collection ledger and numerical PRE,
and requires a strictly earlier actual invocation. It does not test installation
success. All terminal observations refer to the original exhaustive carrier.

Sources: ZIP4 `04_slow_fast_learner.tex:176-215,323-390`,
`06_interruptions.tex:391-426`, and `08_main_theorem.tex:78-109`.
These are internal initialization results, with no manuscript closure claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceGeneratedInvocationCallSplice
open ReferenceGeneratedNativeInvocationGeometry
open ReferenceGeneratedRankCalendarFoundation
open ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarNativePreservation
open ReferenceGeneratedCalendarEndpointMixture
open ReferenceGeneratedCalendarPathAgreement
open ReferenceGeneratedCalendarMarkedPath
open ReferenceGeneratedCalendarRoundInnovation
open ReferencePostInvocationNoncallGeometry
open ReferencePostInvocationPrefixLocality
open ReferenceFirstCollectionLogicalPrefixExtension (NoCallBefore noCallAt_iff_callAt_none)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)

namespace Bandits.Support.ReferenceGeneratedCalendarLaterRenewalSlowInitialization

variable {p : ConstructorDimensions.Parameters}

local notation "Source" => BootstrapPrivateRoundStreams.SourceInput p
local notation "Vector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "Scalar" => ContinuousControlSlice.Scalar

local instance sourceMeasurableSpace : MeasurableSpace Source := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance
local instance controlMeasurableSpace : MeasurableSpace (ContinuousLearningRows.TimeControl p) :=
  ReferencePostInvocationSupportedDisintegration.controlMeasurableSpace
local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] : MeasurableSpace (Option A) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance sumMeasurableSingleton {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] : MeasurableSingletonClass (A ⊕ B) where
  measurableSet_singleton a := by
    cases a with
    | inl x => simpa only [Set.image_singleton] using (measurableSet_singleton x).inl_image (β := B)
    | inr x => simpa only [Set.image_singleton] using (measurableSet_singleton x).inr_image (α := A)
local instance optionMeasurableSingleton {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] : MeasurableSingletonClass (Option A) where
  measurableSet_singleton a := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit A))
      (measurableSet_singleton ((Equiv.optionEquivSumPUnit A) a))
    convert h using 1
    ext b
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact (Equiv.optionEquivSumPUnit A).injective.eq_iff.symm
local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Omega" => ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h
local notation "Z" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0
local notation "L" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout rate rewards C_star C_h control0
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "call" => ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h
local notation "freeze" => ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h
local notation "pre" => prefixNumerical rate rewards C_star C_h

omit control0 in
/-- Literal pre-sampler renewal opportunity. The final conjunct is an actual
strict-past condition, excluding the first invocation itself. -/
def sourceLaterRenewal (s : Fin p.T) : Set Source :=
  {z | (call s z).isSome = true ∧
    (freeze s z).any (fun g => decide (g ≤ s.val + 1)) = true ∧
    (pre s.castSucc z).any (fun S => !S.overflow) = true ∧
    ¬ NoCallBefore rate rewards C_star C_h s.castSucc z}

/-- The same opportunity on the actual exhaustive terminal sample. -/
def laterRenewalEvent (s : Fin p.T) : Set Omega :=
  Z ⁻¹' sourceLaterRenewal rate rewards C_star C_h s

private theorem measurable_optionIsSome {A : Type*} [MeasurableSpace A] :
    Measurable (Option.isSome : Option A → Bool) := by
  have h : Measurable (Sum.elim (fun _ : A => true) (fun _ : PUnit => false)) :=
    measurable_fun_sum measurable_const measurable_const
  convert h.comp (comap_measurable (Equiv.optionEquivSumPUnit A)) using 1
  funext a
  cases a <;> rfl

include control0 in
theorem measurableSet_sourceLaterRenewal (s : Fin p.T) :
    MeasurableSet (sourceLaterRenewal rate rewards C_star C_h s) := by
  have hc : Measurable (call s) :=
    (ReferenceCalendarCollectionCallControlLaw.callAt_measurable rate rewards C_star C_h control0 s).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (s.val + 1)) le_rfl
  have hg : Measurable (fun z : Source =>
      (freeze s z).any (fun g => decide (g ≤ s.val + 1))) :=
    (measurable_of_countable (fun g : Option ℕ => g.any (fun n => decide (n ≤ s.val + 1)))).comp
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_oldFreezeAt? rate rewards C_star C_h s)
  have hp : Measurable (fun z : Source => (pre s.castSucc z).any (fun S => !S.overflow)) :=
    (measurable_of_countable (fun o : Option (RecordedQueueRun.RunState p.K) =>
      o.any (fun S : RecordedQueueRun.RunState p.K => !S.overflow))).comp
        (measurable_prefixNumerical rate rewards C_star C_h s.castSucc)
  exact (measurableSet_eq_fun (measurable_optionIsSome.comp hc) measurable_const).inter
    ((measurableSet_eq_fun hg measurable_const).inter
      ((measurableSet_eq_fun hp measurable_const).inter
        (ReferenceFirstCollectionLogicalPrefixExtension.measurableSet_noCallBefore
          rate rewards C_star C_h control0 s.castSucc).compl))

theorem measurableSet_laterRenewalEvent (s : Fin p.T) :
    MeasurableSet (laterRenewalEvent rate rewards C_star C_h control0 s) :=
  (measurableSet_sourceLaterRenewal rate rewards C_star C_h control0 s).preimage
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalSource rate rewards C_star C_h control0)

/-- Measurability of the literal strict history tested by initialization. -/
theorem measurable_literal_history (s : Fin p.T) :
    Measurable (fun w : Omega => (sourcePrefix control0 s.val (Z w),
      ReferenceGeneratedCalendarEpisodePrefixRecombination.archiveBefore
        rate rewards C_star C_h control0 s.castSucc w)) :=
  ((ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 s.val).comp
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalSource
      rate rewards C_star C_h control0)).prodMk
    (ReferenceGeneratedCalendarEpisodePrefixRecombination.measurable_archiveBefore
      rate rewards C_star C_h control0 s.castSucc)

private theorem oldFreezeAt_eq_of_prefix_eq (s : Fin p.T) (z z' : Source)
    (hp : sourcePrefix control0 s.val z = sourcePrefix control0 s.val z')
    (hc : (call s z).isSome = true) : freeze s z = freeze s z' := by
  have he : call s z = call s z' := by
    rw [ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 s z,
      hp, ← ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 s z']
  obtain ⟨⟨cutoff, theta⟩, hcall⟩ := Option.isSome_iff_exists.mp hc
  have hcall' := he.symm.trans hcall
  obtain ⟨R, hR, hRc⟩ := Option.bind_eq_some_iff.mp hcall
  obtain ⟨R', hR', _⟩ := Option.bind_eq_some_iff.mp hcall'
  obtain ⟨payload, ledger, saved, hcoord, _, _⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec R cutoff theta).mp hRc
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h s z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h s z' := by
    rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 s z,
      hp, ← ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 s z']
  have hstate := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecords_state_congr
    rate rewards C_star C_h s z z' R R' hR hR' hin
  obtain ⟨i, hi⟩ := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecord_suffix_index
    rate rewards C_star C_h s z R hR
  obtain ⟨i', hi'⟩ := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecord_suffix_index
    rate rewards C_star C_h s z' R' hR'
  have htime := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h s z R hR).2.2.1
  have htime' := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h s z' R' hR').2.2.1
  rw [ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record rate rewards C_star C_h
      s z R (hi ▸ List.getElem_mem i.isLt) htime payload ledger saved hcoord,
    ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record rate rewards C_star C_h
      s z' R' (hi' ▸ List.getElem_mem i'.isLt) htime' payload ledger saved
        ((congrArg ReferenceActivePhysicalStep.State.coordinator hstate).symm.trans hcoord)]

/-- Every conjunct of the opportunity is fixed before this date's draw. -/
theorem sourceLaterRenewal_sourcePrefix (s : Fin p.T) (z : Source) :
    z ∈ sourceLaterRenewal rate rewards C_star C_h s ↔
      sourcePrefix control0 s.val z ∈ sourceLaterRenewal rate rewards C_star C_h s := by
  have hc := ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 s z
  have hp := prefixNumerical_sourcePrefix rate rewards C_star C_h control0 s.castSucc s.val le_rfl z
  have hn := ReferenceFirstCollectionLogicalPrefixExtension.noCallBefore_sourcePrefix
    rate rewards C_star C_h control0 s.castSucc z
  simp only [Fin.val_castSucc] at hn
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
  rw [← hc, ← hp, ← hn]
  by_cases hcall : (call s z).isSome = true
  · rw [oldFreezeAt_eq_of_prefix_eq rate rewards C_star C_h control0 s z
      (sourcePrefix control0 s.val z) (by
        rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 s.val s.val le_rfl]) hcall]
  · exact iff_of_false (fun h => hcall h.1) (fun h => hcall h.1)

/-- In particular the event factors through the first coordinate of exactly
the displayed source-prefix/archive pair, with no component tag added. -/
theorem laterRenewalEvent_literal_history (s : Fin p.T) :
    laterRenewalEvent rate rewards C_star C_h control0 s =
      (fun w : Omega => (sourcePrefix control0 s.val (Z w),
        ReferenceGeneratedCalendarEpisodePrefixRecombination.archiveBefore
          rate rewards C_star C_h control0 s.castSucc w)) ⁻¹'
        (sourceLaterRenewal rate rewards C_star C_h s ×ˢ Set.univ) := by
  ext w
  exact (sourceLaterRenewal_sourcePrefix rate rewards C_star C_h control0 s (Z w)).trans
    (and_iff_left (Set.mem_univ _)).symm

omit control0 in
/-- On an actual first-call cell, having an earlier invocation is exactly a
strict inequality between physical dates. -/
theorem noCallBefore_on_firstCell (u t : Fin p.T) (z : Source)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell rate rewards C_star C_h u t)
    (n : Fin (p.T + 1)) : NoCallBefore rate rewards C_star C_h n z ↔ n.val ≤ t.val := by
  have hb := ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell
    rate rewards C_star C_h u t z hz
  constructor
  · intro hn
    by_contra h
    have ht : t.val < n.val := by omega
    have hbefore := (ReferenceFirstCollectionPrecallCalendarSupport.before_cut_iff_no_call_through
      rate rewards C_star C_h t z).mpr (fun v hv =>
        (noCallAt_iff_callAt_none rate rewards C_star C_h v z).mp (hn v (hv.trans_lt ht)))
    rw [hb] at hbefore
    exact Nat.lt_irrefl _ hbefore
  · intro hn v hv
    rw [noCallAt_iff_callAt_none]
    exact (ReferenceFirstCollectionPrecallCalendarSupport.before_cut_iff_no_call_through
      rate rewards C_star C_h v z).mp (by rw [hb]; omega) v le_rfl

/-- A real sampler invocation is nominally enabled, including stopped calls. -/
theorem call_nominalEnabled (s : Fin p.T) (z : Source) (hc : (call s z).isSome = true) :
    ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled rate rewards C_star C_h s z = true := by
  let v : InvocationSource rate rewards C_star C_h s := ⟨z, hc⟩
  have hs := nativeSourceCell_spec rate rewards C_star C_h s v
  have hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h s z =
      some (nativeRecord rate rewards C_star C_h s v) := hs.1
  have hcell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate (nativeRecord rate rewards C_star C_h s v) =
      some (nativeSourceCell rate rewards C_star C_h s v).input := by
    rw [ReferenceFirstCollectionCurrentRetainedGate.cell0, hs.2.2, Option.some_or]
  rw [ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled, hr, Option.bind_some,
    hcell, Option.any_some]
  exact (nativeSourceCell rate rewards C_star C_h s v).enabled

/-- The opportunity contains a unique PRESENT actual mark. No success or
chronology assumption is supplied by the caller. -/
theorem laterRenewalEvent_unique_present (s : Fin p.T) (w : Omega)
    (hw : w ∈ laterRenewalEvent rate rewards C_star C_h control0 s) :
    ∃! e : LogicalCell p rate, e ∈ (L w).2.2 ∧ e.time = s :=
  (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_unique_enabled
    rate rewards C_star C_h control0 w s).mpr
      (call_nominalEnabled rate rewards C_star C_h s (Z w) hw.1)

/-- The present mark has exactly the actual clear numerical PRE, under the
raw law and every original fixed-ID law. No numerical consistency is assumed. -/
theorem ae_laterRenewalEvent_unique_clear (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ s : Fin p.T, w ∈ laterRenewalEvent rate rewards C_star C_h control0 s →
        ∃! e : LogicalCell p rate, e ∈ (L w).2.2 ∧ e.time = s ∧
          pre s.castSucc (Z w) = some e.before ∧ e.before.overflow = false := by
  filter_upwards [ReferenceExhaustiveGeneratedCalendarSourceLaw.ae_terminal_marked_path
    rate rewards C_star C_h control0 ids] with w hw
  intro s hs
  obtain ⟨e, he, huniq⟩ := laterRenewalEvent_unique_present rate rewards C_star C_h control0 s w hs
  obtain hnil | ⟨hl, hfields⟩ := hw.2.2
  · rw [hnil.2] at he
    cases he.1
  · have hb := (hfields e he.1).2.1
    rw [he.2] at hb
    let v : InvocationSource rate rewards C_star C_h s := ⟨Z w, hs.1⟩
    have hd := (ReferencePostInvocationGeneratedAlignment.actualRecord_index rate rewards C_star C_h s
      (Z w) _ (nativeSourceCell_spec rate rewards C_star C_h s v).1).choose_spec.2.2
    have hp := prefixNumerical_actualWord rate rewards C_star C_h s.castSucc (Z w) hl hd
    simp only [Fin.val_castSucc] at hp
    rw [← hb] at hp
    have hc := hs.2.2.1
    rw [hp, Option.any_some, Bool.not_eq_true'] at hc
    refine ⟨e, ⟨he.1, he.2, hp, hc⟩, ?_⟩
    intro f hf
    exact huniq f ⟨hf.1, hf.2.1⟩

/-- On generated components the excluded first-call condition is genuinely
past exactly when `t < s`; neither the next call nor sampler success is read. -/
theorem generated_laterRenewal_first_date (b : Bool) (u t s : Fin p.T)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h (.generated b u t)) :
    ¬ NoCallBefore rate rewards C_star C_h s.castSucc (Z ⟨.generated b u t, w⟩) ↔ t.val < s.val := by
  change ¬ NoCallBefore rate rewards C_star C_h s.castSucc
    (calendarCurrentSource rate rewards C_star C_h control0 b u t _ _ w) ↔ _
  rw [noCallBefore_on_firstCell rate rewards C_star C_h u t _
    (ReferenceGeneratedCalendarLivePayoff.calendarCurrentSource_firstCell
      rate rewards C_star C_h control0 b u t _ _ w)]
  change ¬ s.val ≤ t.val ↔ t.val < s.val
  exact Nat.not_le

/-- At a later opportunity the original `beforeFirstCall` complement agrees
with the actual source's past condition on every generated component. -/
theorem generated_not_beforeFirstCall (b : Bool) (u t s : Fin p.T)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h (.generated b u t)) :
    (⟨.generated b u t, w⟩ : Omega) ∉
        ReferenceGeneratedCalendarEpisodePrefixRecombination.beforeFirstCall rate rewards C_star C_h s.castSucc ↔
      t.val < s.val := by
  let root := calendarOriginalLift rate rewards C_star C_h b u t _ w
  have hfirst : root.1.1.val ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t := by
    cases b with
    | false => exact (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_facts
        rate rewards C_star C_h u t root.1.1.val root.1.1.property).1
    | true => exact root.1.1.property.1
  change ¬ NoCallBefore rate rewards C_star C_h s.castSucc root.1.1.val ↔ _
  rw [noCallBefore_on_firstCell rate rewards C_star C_h u t _ hfirst]
  exact Nat.not_le

/-- No-first-call samples contribute no renewal opportunity. -/
theorem noCall_not_laterRenewal (s : Fin p.T)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h .noCall) :
    (⟨.noCall, w⟩ : Omega) ∉ laterRenewalEvent rate rewards C_star C_h control0 s := by
  intro hw
  apply hw.2.2.2
  have h := (ReferenceExhaustiveGeneratedCalendarSourceLaw.noCallBefore_terminal_iff
    rate rewards C_star C_h w.1.val).mpr w.1.property
  exact fun q _ => h q q.isLt

/-- A stopped component cannot become a clear-PRE renewal later. -/
theorem stopped_not_laterRenewal (u t s : Fin p.T)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h (.stopped u t)) :
    (⟨.stopped u t, w⟩ : Omega) ∉ laterRenewalEvent rate rewards C_star C_h control0 s := by
  intro hw
  have hts : t.val < s.val := by
    have h := hw.2.2.2
    change ¬ NoCallBefore rate rewards C_star C_h s.castSucc w.1.val at h
    rw [noCallBefore_on_firstCell rate rewards C_star C_h u t w.1.val w.1.property.1.1] at h
    exact Nat.lt_of_not_ge h
  have hd := ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_dates
    rate rewards C_star C_h u t w.1.val w.1.property.1.1
  have hp := prefixNumerical_actualWord rate rewards C_star C_h s.castSucc w.1.val
    (ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_launch
      rate rewards C_star C_h u t w.1.val w.1.property.1.1) (by
        change ReferenceCompletePhysicalHistory.physicalStart rate w.1.val rewards C_star C_h ≤ s.val
        omega)
  simp only [Fin.val_castSucc] at hp
  have hc := hw.2.2.1
  change (pre s.castSucc w.1.val).any (fun S => !S.overflow) = true at hc
  rw [hp, Option.any_some] at hc
  have hov := ReferenceInitialStoppedCalendar.suffixBefore_stopped rate rewards C_star C_h
    u t s hts.le w.1
  change (RecordedQueueRun.run Q
    ((ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h w.1.val _).take
      (s.val - ReferenceCompletePhysicalHistory.physicalStart rate w.1.val rewards C_star C_h))).overflow = true at hov
  rw [hov] at hc
  cases hc

private theorem selected_parameters_at_success {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hrec : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction = .success ledger instruction out) :
    LaterAssignmentStartMeasurability.selectedSamplerParameters? old ⟨ledger, instruction, consistent⟩ =
      some (LaterAssignmentStartMeasurability.selectedSamplerParameters old ledger instruction out hrec) := by
  rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match]
  have hpair : (⟨AssignmentScoreReconstruction.reconstructLaterStart ledger instruction, rfl⟩ :
      LaterAssignmentStartOperation.ReconstructionCall old ledger instruction) =
      ⟨.success ledger instruction out, hrec⟩ := by
    apply LaterAssignmentStartOperation.ReconstructionCall.ext
    exact hrec
  unfold LaterAssignmentStartOperation.decideReconstruction
  rw [hpair]
  rfl

/-- At a genuine reached-boundary call, restoration identifies the actual
sampler's current weights and new anchor with its numerical PRE. The
reconstructed law, queues, clock and installation are produced internally. -/
theorem nativeRenewal_parameter (s : Fin p.T) (z : InvocationSource rate rewards C_star C_h s)
    (u : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : call s z.val = some (u, theta))
    (hfreeze : (freeze s z.val).any (fun g => decide (g ≤ s.val + 1)) = true)
    (hclear : (nativeBefore rate rewards C_star C_h control0 s z).overflow = false) :
    theta.2 = RecordedQueueRun.scoreWeight Q (nativeBefore rate rewards C_star C_h control0 s z) ∧
    theta.1 = LaterAssignmentStartOperation.productQOnPrefixCarrier theta.2 ∧
    (nativeSourceCell rate rewards C_star C_h s z).selected.view.payload.anchor = theta.2 := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h
  let hl := nativeInvocation_launch rate rewards C_star C_h s z
  let W := ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord rate rewards C_star C_h z.val hl
  obtain ⟨b, rb, _qb, _beta, hr, heq, hchosen, _hnext, hbirth, hpay⟩ :=
    nativeInvocation_installation rate rewards C_star C_h s z
  let r := R[b.val]
  obtain ⟨old, ledger, saved, hcoord, hempty⟩ :=
    ReferenceCollectionPhaseHistory.laterChosen_pending_empty r.input hchosen
  have htimeR := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h s z.val r hr).2.2.1
  have hf := ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record
    rate rewards C_star C_h s z.val r (List.getElem_mem b.isLt) htimeR old ledger saved hcoord
  rw [hf, Option.any_some, decide_eq_true_eq] at hfreeze
  have hstep := ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
    rate rewards C_star C_h z.val b
  dsimp only at hstep
  rw [hcoord] at hstep
  obtain ⟨u', _hu, core, started, hstart, instruction, hassignment, htime, hkind,
    consistent, output, hlocal, _hresult, clockData, installed, selected,
    _hinstall, _hstarted, _hdispatch, hprepared, _htail⟩ := hstep hempty
  have hrenewal : instruction.kind = .renewal := by
    rw [ite_eq_right (by rw [htimeR]; omega)] at hkind
    exact hkind
  obtain ⟨r', hr', hcallR⟩ := Option.bind_eq_some_iff.mp hcall
  have hrr : r' = r := Option.some.inj (hr'.symm.trans hr)
  subst r'
  obtain ⟨_P, _ledger, _saved, _hcoord, _hcut, hparam⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcallR
  have hprep : r.output.preparation.coordinator = ReferenceActivePhysicalStep.dispatch r.input := by
    rw [r.output_eq]
    rfl
  change ReferenceLaterAssignmentFibreStep.parameters? r.input = some theta at hparam
  rw [ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch, ← hprep, hprepared] at hparam
  change LaterAssignmentStartMeasurability.selectedSamplerParameters? old
    ⟨_, instruction, consistent⟩ = some theta at hparam
  rw [selected_parameters_at_success old _ instruction consistent output.reconstruction output.reconstruction_eq] at hparam
  have htheta := Option.some.inj hparam
  have hpar := LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
    old _ instruction output.reconstruction output.reconstruction_eq hrenewal
  have hthetaWeight : theta.2 = AssignmentScoreReconstruction.currentWeight output.reconstruction := by
    rw [← htheta]
    exact hpar.1
  have hthetaMass : theta.1 = LaterAssignmentStartOperation.productQOnPrefixCarrier theta.2 := by
    rw [← htheta]
    exact funext fun S => by rw [hpar.2 S, hpar.1]; rfl
  have hrestore := ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration
    rate rewards C_star C_h z.val
  rw [Classical.choose_spec hl] at hrestore
  obtain ⟨whole, hlen, _hprefix, hfull, _hunique, hbirths, _hbranches, _hstates⟩ := hrestore
  have hwhole : whole = W := Option.some.inj (hfull.symm.trans
    (ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_spec rate rewards C_star C_h z.val hl))
  obtain ⟨_rho, _P, _hrho, _hroot, _hepisode, hscore, _⟩ := hbirths b rb.payload hbirth
  unfold ReferenceCompleteLiveComplementScoreSpan.installationScoreVector at hscore
  rw [hprepared] at hscore
  have hweights : AssignmentScoreReconstruction.currentWeight output.reconstruction =
      (fun i => AssignmentScoreReconstruction.sourceWeightBase p ^
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate W i b.val).1) := by
    rw [← hwhole]
    funext i
    exact congrArg (fun n : ℕ => AssignmentScoreReconstruction.sourceWeightBase p ^ n)
      (congrFun hscore.2.1 i).symm
  have hindex : s.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = b.val := by
    have ht := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
      rate z.val rewards C_star C_h b.val r (List.getElem?_eq_getElem b.isLt)
    rw [htimeR] at ht
    omega
  have hbefore : nativeBefore rate rewards C_star C_h control0 s z = RecordedQueueRun.run Q (W.take b.val) := by
    have h := nativeCell_before_word rate rewards C_star C_h control0 s z
      ReferenceFirstLiveActualRefreshTestLaw.scalarZero
    rw [hindex] at h
    exact h
  have hb : b.val ≤ W.length := by rw [← hwhole, hlen]; exact b.isLt.le
  have hpre : b.val ≤ UnstoppedRecordedQueueComparison.firstOverflowPrefix Q W := by
    by_contra h
    have hover := (UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
      Q W b.val hb).mpr (by omega)
    rw [← hbefore, hclear] at hover
    cases hover
  have hnum := (ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_numericalPrefix
    rate rewards C_star C_h z.val hl b.val hb).2.1
  change RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q (W.take b.val)) =
    (fun i => AssignmentScoreReconstruction.sourceWeightBase p ^
      (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate W i
        (min b.val (UnstoppedRecordedQueueComparison.firstOverflowPrefix Q W))).1) at hnum
  rw [Nat.min_eq_left hpre] at hnum
  refine ⟨?_, hthetaMass, ?_⟩
  · rw [hthetaWeight, hbefore, hnum]
    exact hweights
  · have hanchor := (LaterAssignmentStartOperation.successful_renewal_law_spec output hrenewal).2.1
    have hinstalled : installed.registers.payload = output.payload := _htail.1
    have hselection : r.output.preparation.coordinator.selection.map (fun v => v.view.payload) =
        some (nativeSourceCell rate rewards C_star C_h s z).selected.view.payload := by
      have heq' : r = nativeRecord rate rewards C_star C_h s z := heq
      rw [heq', (nativeSourceCell rate rewards C_star C_h s z).selection_actual, Option.map_some]
    rw [hprepared] at hselection
    have htime' : instruction.time = r.input.time := htime
    simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, dite_eq_left htime', Option.map_some] at hselection
    have hview : installed.registers.payload =
        (nativeSourceCell rate rewards C_star C_h s z).selected.view.payload := Option.some.inj hselection
    rw [← hview, hinstalled, hanchor, ← hthetaWeight]

/-- The initial law uses the same PRE score weights as its new fixed anchor. -/
def initialSlowPMF (S : RecordedQueueRun.RunState p.K) : PMF (SlowSet p) :=
  RecordedSlowRefresh.recordedSlowPMF p Q S (RecordedQueueRun.scoreWeight Q S)
    (RecordedSlowRefresh.scoreWeight_pos Q S)

/-- The actual renewal selector has the exact initial slow PMF, with no null
outcome. This joins restoration to the accepted full-vector sampler identity. -/
theorem nativeRenewal_fibreMass (s : Fin p.T) (z : InvocationSource rate rewards C_star C_h s)
    (u : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
    (hcall : call s z.val = some (u, theta))
    (hfreeze : (freeze s z.val).any (fun g => decide (g ≤ s.val + 1)) = true)
    (hclear : (nativeBefore rate rewards C_star C_h control0 s z).overflow = false)
    (U : SlowSet p) :
    AssignmentParameterFibreKernel.fibreMass p theta (some U) =
      initialSlowPMF rate (nativeBefore rate rewards C_star C_h control0 s z) U ∧
    AssignmentParameterFibreKernel.fibreMass p theta none = 0 := by
  obtain ⟨hw, hm, _ha⟩ := nativeRenewal_parameter rate rewards C_star C_h control0 s z u theta
    hcall hfreeze hclear
  let S := nativeBefore rate rewards C_star C_h control0 s z
  let weight := RecordedQueueRun.scoreWeight Q S
  have hpos := RecordedSlowRefresh.scoreWeight_pos Q S
  have htheta : theta = ((CanonicalAssignmentVector.productQNormalizedMass
      p.two_le_m p.m_lt_K weight hpos).weight, weight) := by
    refine Prod.ext ?_ hw
    rw [hm, hw]
    rfl
  have hsample (v : Vector) : AssignmentParameterFibreKernel.successfulSlowSet p theta v =
      some (CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K weight weight hpos hpos v) := by
    rw [htheta]
    unfold AssignmentParameterFibreKernel.successfulSlowSet
    rw [CheckedAssignmentSample.productQ_checkedAssignmentSample_eq_sampler p weight weight hpos hpos]
    rfl
  constructor
  · change ContinuousControlSlice.assignmentLaw p.K {v | _ = some U} = _
    simp_rw [hsample, Option.some.injEq]
    change FiniteFibreLift.fibreMass (ContinuousControlSlice.assignmentLaw p.K)
      (CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K weight weight hpos hpos) U = _
    rw [CanonicalAssignmentVector.canonicalSlowSampler_fibreMass]
    exact (CanonicalOrientedSetLaw.slowSetPMF_apply weight weight p.two_le_m p.m_lt_K hpos hpos U).symm
  · change ContinuousControlSlice.assignmentLaw p.K {v | _ = none} = 0
    simp_rw [hsample]
    simp only [reduceCtorEq, Set.ofPred_false, measure_empty]

private theorem measurable_option_cases {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (o : X → Option A) (ho : Measurable o) (f : X → B) (hf : Measurable f)
    (g : X × A → B) (hg : Measurable g) :
    Measurable (fun x => match o x with | none => f x | some a => g (x, a)) := by
  have hs := hg.sumElim (hf.comp (measurable_fst : Measurable (Prod.fst : X × PUnit → X)))
  have he := (MeasurableEquiv.prodSumDistrib X A PUnit).measurable.comp
    (measurable_id.prodMk ((comap_measurable (Equiv.optionEquivSumPUnit A)).comp ho))
  convert hs.comp he using 1
  funext x
  cases h : o x <;> simp only [Function.comp_apply, id_eq, h] <;> rfl

omit control0 in
/-- Evaluate the fresh categorical endpoint at an actual optional call
parameter. This is only used on renewal opportunities; a retained call's
carried endpoint is never replaced by this map. Absent calls remain absent. -/
def freshCallEndpoint (s : Fin p.T) (zx : Source × Scalar) : AssignmentParameterFibreKernel.Outcome p :=
  match call s zx.1 with
  | none => none
  | some a => ReferenceNextRetainedEndpointFibreLaw.freshEndpoint (p := p) a.2 zx.2

include control0 in
private theorem measurable_call_global (s : Fin p.T) : Measurable (call s) :=
  (ReferenceCalendarCollectionCallControlLaw.callAt_measurable rate rewards C_star C_h control0 s).mono
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (s.val + 1)) le_rfl

private theorem measurable_fresh : Measurable (fun v : AssignmentParameterFibreKernel.Theta p × Scalar =>
    ReferenceNextRetainedEndpointFibreLaw.freshEndpoint (p := p) v.1 v.2) :=
  (ReferenceNextRetainedEndpointFibreLaw.measurable_freshEndpoint (p := p)).mono le_rfl le_top

private theorem measurable_fresh_comp {X : Type*} [MeasurableSpace X]
    (a : X → AssignmentParameterFibreKernel.Theta p) (x : X → Scalar)
    (ha : Measurable a) (hx : Measurable x) :
    Measurable (fun z => ReferenceNextRetainedEndpointFibreLaw.freshEndpoint (p := p) (a z) (x z)) := by
  intro V hV
  change MeasurableSet ((fun z => (a z, x z)) ⁻¹'
    ((fun v : AssignmentParameterFibreKernel.Theta p × Scalar =>
      ReferenceNextRetainedEndpointFibreLaw.freshEndpoint (p := p) v.1 v.2) ⁻¹' V))
  exact (ha.prodMk hx) ((measurable_fresh (p := p)) hV)

include control0 in
private theorem measurable_initial_selector (s : Fin p.T) :
    Measurable (freshCallEndpoint rate rewards C_star C_h s) := by
  unfold freshCallEndpoint
  have hm := measurable_option_cases (fun zx : Source × Scalar => call s zx.1)
    ((measurable_call_global rate rewards C_star C_h control0 s).comp measurable_fst)
    (fun _ => (none : AssignmentParameterFibreKernel.Outcome p)) measurable_const
    (fun z => ReferenceNextRetainedEndpointFibreLaw.freshEndpoint (p := p) z.2.2 z.1.2)
    (measurable_fresh_comp (p := p)
      (X := (Source × Scalar) × (Fin p.T × AssignmentParameterFibreKernel.Theta p))
      (fun z => z.2.2) (fun z => z.1.2)
      measurable_snd.snd measurable_fst.snd)
  convert hm using 1
  funext zx
  cases call s zx.1 <;> rfl

private theorem fresh_scalar_cylinder (theta : AssignmentParameterFibreKernel.Theta p) (U : SlowSet p) :
    (∫⁻ x : Scalar, if ReferenceNextRetainedEndpointFibreLaw.freshEndpoint (p := p) theta x = some U
      then (1 : ℝ≥0∞) else 0 ∂ContinuousControlSlice.scalarLaw) =
      AssignmentParameterFibreKernel.fibreMass p theta (some U) := by
  have he : Measurable (ReferenceNextRetainedEndpointFibreLaw.freshEndpoint (p := p) theta) :=
    Measurable.of_uncurry_left (measurable_fresh (p := p))
  have hE : MeasurableSet {x : Scalar |
      ReferenceNextRetainedEndpointFibreLaw.freshEndpoint (p := p) theta x = some U} :=
    measurableSet_eq_fun he measurable_const
  rw [show (fun x : Scalar => if ReferenceNextRetainedEndpointFibreLaw.freshEndpoint (p := p) theta x = some U
      then (1 : ℝ≥0∞) else 0) =
      {x : Scalar | ReferenceNextRetainedEndpointFibreLaw.freshEndpoint (p := p) theta x = some U}.indicator (fun _ => 1) by
        funext x
        by_cases h : ReferenceNextRetainedEndpointFibreLaw.freshEndpoint (p := p) theta x = some U
        · simp only [Set.indicator, Set.mem_ofPred_eq, h, ite_true]
        · simp only [Set.indicator, Set.mem_ofPred_eq, h, ite_false],
    lintegral_indicator_const hE, one_mul,
    ReferenceNextInsertedSourceMarginal.freshEndpoint_fibre (p := p)]

include control0 in
/-- The genuine later-renewal opportunity produces the scalar initializer
law from its actual sampler parameter and actual PRE, without a supplied law. -/
theorem sourceLaterRenewal_initial_scalar (s : Fin p.T) (z : Source)
    (hz : z ∈ sourceLaterRenewal rate rewards C_star C_h s) (U : SlowSet p) :
    (∫⁻ x : Scalar, if freshCallEndpoint rate rewards C_star C_h s (z, x) = some U then 1 else 0
      ∂ContinuousControlSlice.scalarLaw) =
    (pre s.castSucc z).elim 0 (fun S => initialSlowPMF rate S U) := by
  let v : InvocationSource rate rewards C_star C_h s := ⟨z, hz.1⟩
  obtain ⟨⟨u, theta⟩, hc⟩ := Option.isSome_iff_exists.mp hz.1
  have hp : pre s.castSucc z = some (nativeBefore rate rewards C_star C_h control0 s v) :=
    nativeBefore_prefix rate rewards C_star C_h control0 s v
  have hclear := hz.2.2.1
  rw [hp, Option.any_some, Bool.not_eq_true'] at hclear
  rw [hp, Option.elim_some]
  simp only [freshCallEndpoint, hc]
  rw [fresh_scalar_cylinder (p := p)]
  exact (nativeRenewal_fibreMass rate rewards C_star C_h control0 s v u theta hc hz.2.1 hclear U).1

private theorem freshCallEndpoint_sourcePrefix (s : Fin p.T) (z : Source) (x : Scalar) :
    freshCallEndpoint rate rewards C_star C_h s (z, x) =
      freshCallEndpoint rate rewards C_star C_h s (sourcePrefix control0 s.val z, x) := by
  exact congrArg (fun a : ReferenceCalendarCollectionCallControlLaw.CallAt p => match a with
    | none => (none : AssignmentParameterFibreKernel.Outcome p)
    | some a => ReferenceNextRetainedEndpointFibreLaw.freshEndpoint (p := p) a.2 x)
      (ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 s z)

/-- Literal clear-PRE slow-set indicator on an archived cell. -/
def slowSetCoefficient (U : SlowSet p) (e : LogicalCell p rate) : ℝ≥0∞ :=
  if e.before.overflow then 0 else if e.slowSet = U then 1 else 0

/-- The corresponding initial PMF evaluated at the SAME archived PRE. -/
def initialMassCoefficient (U : SlowSet p) (e : LogicalCell p rate) : ℝ≥0∞ :=
  if e.before.overflow then 0 else initialSlowPMF rate e.before U

private theorem measurable_list_getElem? {A : Type*} [MeasurableSpace A] (k : ℕ) :
    Measurable (fun H : List A => H[k]?) := by
  have ht : Measurable (fun H : List A => ReferenceActiveHorizonMeasurability.listObservationAt H k) :=
    (measurable_pi_apply k).comp ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.snd
  have hd : Measurable (Sum.elim (fun _ : Unit => (none : Option A)) some) :=
    measurable_fun_sum measurable_const
      (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ measurable_id)
  convert hd.comp ht using 1
  funext H
  simp only [Function.comp_apply, ReferenceActiveHorizonMeasurability.listObservationAt]
  cases H[k]? <;> rfl

attribute [local instance] ReferenceRankInstallationPostUpdateProposalLaw.listMeasurableSingleton

private theorem measurable_find_time (s : Fin p.T) :
    Measurable (fun H : List (LogicalCell p rate) => H.find? (fun e => e.time == s)) := by
  have ht : Measurable (fun H : List (LogicalCell p rate) => H.map LogicalCell.time) :=
    ReferenceActiveHorizonMeasurability.measurable_list_map id measurable_id _
      ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_time
  have hn : Measurable (fun H : List (LogicalCell p rate) =>
      (H.map LogicalCell.time).findIdx (fun t => t == s)) :=
    (measurable_of_countable (fun H : List (Fin p.T) => H.findIdx (fun t => t == s))).comp ht
  have hg : Measurable (fun nH : ℕ × List (LogicalCell p rate) => nH.2[nH.1]?) :=
    measurable_from_prod_countable_right (fun n => measurable_list_getElem? n)
  convert hg.comp (hn.prodMk measurable_id) using 1
  funext H
  simp only [Function.comp_apply, List.find?_eq_getElem?_findIdx, List.findIdx_map, id_eq]
  rfl

private theorem measurable_elim_coefficient (f : LogicalCell p rate → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun o : Option (LogicalCell p rate) => o.elim 0 f) := by
  convert measurable_option_cases id measurable_id (fun _ => (0 : ℝ≥0∞)) measurable_const
    (fun v : Option (LogicalCell p rate) × LogicalCell p rate => f v.2) (hf.comp measurable_snd) using 1
  funext o
  cases o <;> rfl

theorem measurable_slowSetCoefficient (U : SlowSet p) : Measurable (slowSetCoefficient rate U) := by
  have hb : Measurable (fun e : LogicalCell p rate => e.before.overflow) :=
    (measurable_of_countable (fun S : RecordedQueueRun.RunState p.K => S.overflow)).comp
      (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_before (rate := rate))
  exact measurable_const.ite (measurableSet_eq_fun hb measurable_const)
    (measurable_const.ite (measurableSet_eq_fun
      ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_slowSet measurable_const) measurable_const)

theorem measurable_initialMassCoefficient (U : SlowSet p) : Measurable (initialMassCoefficient rate U) := by
  have hb : Measurable (fun e : LogicalCell p rate => e.before.overflow) :=
    (measurable_of_countable (fun S : RecordedQueueRun.RunState p.K => S.overflow)).comp
      (ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_before (rate := rate))
  exact measurable_const.ite (measurableSet_eq_fun hb measurable_const)
    ((measurable_of_countable (fun S : RecordedQueueRun.RunState p.K => initialSlowPMF rate S U)).comp
      ReferenceFirstLiveChronologicalPrefixMeasurability.measurable_logicalCell_before)

/-- A cylinder on the literal strict source prefix and actual strict archive,
with the actual optional date mark read directly from terminalReadout. -/
def renewalCylinder (s : Fin p.T) (Phi : Source × List (LogicalCell p rate) → ℝ≥0∞)
    (f : LogicalCell p rate → ℝ≥0∞) (w : Omega) : ℝ≥0∞ :=
  if w ∈ laterRenewalEvent rate rewards C_star C_h control0 s then
    Phi (sourcePrefix control0 s.val (Z w),
      ReferenceGeneratedCalendarEpisodePrefixRecombination.archiveBefore rate rewards C_star C_h control0 s.castSucc w) *
        ((L w).2.2.find? (fun e => e.time == s)).elim 0 f else 0

theorem measurable_renewalCylinder (s : Fin p.T) (Phi : Source × List (LogicalCell p rate) → ℝ≥0∞)
    (hPhi : Measurable Phi) (f : LogicalCell p rate → ℝ≥0∞) (hf : Measurable f) :
    Measurable (renewalCylinder rate rewards C_star C_h control0 s Phi f) :=
  ((hPhi.comp (measurable_literal_history rate rewards C_star C_h control0 s)).mul
    ((measurable_elim_coefficient rate f hf).comp ((measurable_find_time rate s).comp
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalReadout rate rewards C_star C_h control0).snd.snd))).ite
        (measurableSet_laterRenewalEvent rate rewards C_star C_h control0 s) measurable_const

/-- The terminal opportunity also satisfies the accepted original-source
strict-past first-call condition, across all exhaustive raw alternatives. -/
theorem laterRenewalEvent_not_beforeFirstCall (s : Fin p.T) (w : Omega)
    (hw : w ∈ laterRenewalEvent rate rewards C_star C_h control0 s) :
    w ∉ ReferenceGeneratedCalendarEpisodePrefixRecombination.beforeFirstCall rate rewards C_star C_h s.castSucc := by
  rcases w with ⟨i, w⟩
  cases i with
  | noCall => exact (noCall_not_laterRenewal rate rewards C_star C_h control0 s w hw).elim
  | stopped u t => exact (stopped_not_laterRenewal rate rewards C_star C_h control0 u t s w hw).elim
  | generated b u t =>
    exact (generated_not_beforeFirstCall rate rewards C_star C_h b u t s w).mpr
      ((generated_laterRenewal_first_date rate rewards C_star C_h control0 b u t s w).mp hw.2.2.2)

section Ancestors

variable (b0 : Bool) (u0 t0 : Fin p.T)

local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0
local notation "stored" => calendarStoredState rate rewards C_star C_h control0 b0 u0 t0
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0
local notation "ancestor" => calendarAncestor rate rewards C_star C_h b0 u0 t0
local notation "law" => calendarLaw rate rewards C_star C_h control0 b0 u0 t0
local notation "past" => calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0
local notation "original" => calendarOriginalLift rate rewards C_star C_h b0 u0 t0

/-- The initial endpoint is the present date's actual native slow set almost
surely on renewed clear calls. The full-vector fibre match is produced by
the accepted generated law, rather than required as an input. -/
theorem ae_calendarLaw_laterRenewal_step (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    ∀ᵐ wv ∂law (k + 1) (by omega),
      let s : Fin p.T := ⟨t0.val + 1 + k, hk⟩
      current k hk.le wv.1 ∈ sourceLaterRenewal rate rewards C_star C_h s →
      ∃ e : LogicalCell p rate,
        calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2 = some e ∧
        pre s.castSucc (current k hk.le wv.1) = some e.before ∧ e.before.overflow = false ∧
        freshCallEndpoint rate rewards C_star C_h s
          (current k hk.le wv.1, (original k wv.1).1.2 (s, 1)) = some e.slowSet := by
  filter_upwards [ae_calendarLaw_call_support rate rewards C_star C_h control0 b0 u0 t0 k hk]
    with wv hsupport
  change Sample k × Vector at wv
  dsimp only
  intro hw
  let s : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  have hc : calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega) wv.1 = true := hw.1
  have hr : (calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k (by omega) wv.1).1 = true := hw.2.1
  have hclear : (calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k (by omega) wv.1).2 = true := by
    change (calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk.le wv.1).2.val.2.2.1.any
      (fun S => !S.overflow) = true
    rw [calendarObservation_numerical]
    exact hw.2.2.1
  let e := calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2 hc
  have hp : pre s.castSucc (current k hk.le wv.1) = some e.before :=
    (calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 k hk.le wv.1).symm.trans
      (calendarInvocationCell_before rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2 hc).symm
  have hov := hw.2.2.1
  rw [hp, Option.any_some, Bool.not_eq_true'] at hov
  obtain ⟨u, theta, hcall, _hphysical, hendpoint⟩ :=
    calendarInvocationCell_join_of_fibreMatch rate rewards C_star C_h control0 b0 u0 t0
      k hk wv.1 wv.2 hc hclear (hsupport hc hclear).1
  rw [show ReferenceNextRetainedEndpointFibreLaw.renewalFlag rate rewards C_star C_h
      (t := (calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk.le wv.1).1)
      s (calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk.le wv.1).2.val = true from hr,
    ] at hendpoint
  simp only [↓reduceIte] at hendpoint
  refine ⟨e, ?_, hp, hov, ?_⟩
  · rw [calendarStepCell, dite_eq_left hc]
  · unfold freshCallEndpoint
    dsimp only [Prod.fst, Prod.snd]
    have hcall' : call s (current k hk.le wv.1) = some (u, theta) := hcall
    rw [hcall']
    exact hendpoint

/-- The label-one initializer is tested jointly with the full actual strict
physical prefix and earlier archive. The earlier first-branch information is
past here and is not added to the tested history. -/
theorem calendarLaw_laterRenewal_endpoint_cylinder (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (U : SlowSet p) (Phi : Source × List (LogicalCell p rate) → ℝ≥0∞) (hPhi : Measurable Phi) :
    let s : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    (∫⁻ w, if current k hk.le w ∈ sourceLaterRenewal rate rewards C_star C_h s then
      Phi (sourcePrefix control0 s.val (current k hk.le w), (stored k hk.le w).2) *
        (if freshCallEndpoint rate rewards C_star C_h s
          (current k hk.le w, (original k w).1.2 (s, 1)) = some U then 1 else 0) else 0
      ∂law k hk.le) =
    ∫⁻ w, if current k hk.le w ∈ sourceLaterRenewal rate rewards C_star C_h s then
      Phi (sourcePrefix control0 s.val (current k hk.le w), (stored k hk.le w).2) *
        (pre s.castSucc (current k hk.le w)).elim 0 (fun S => initialSlowPMF rate S U) else 0
      ∂law k hk.le := by
  dsimp only
  let s : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let A := Source × (SlowSet p × List (LogicalCell p rate))
  let I := ReferencePostInvocationSupportedDisintegration.Innovation p
  let E := sourceLaterRenewal rate rewards C_star C_h s
  let test : Source × Scalar → ℝ≥0∞ := fun zx =>
    if freshCallEndpoint rate rewards C_star C_h s zx = some U then 1 else 0
  have ht : Measurable test := measurable_const.ite
    (measurableSet_eq_fun (measurable_initial_selector rate rewards C_star C_h control0 s) measurable_const)
      measurable_const
  let F : A × I → ℝ≥0∞ := fun hx => if hx.1.1 ∈ E then
    Phi (hx.1.1, hx.1.2.2) * test (hx.1.1, hx.2.2.2) else 0
  have hF : Measurable F := ((hPhi.comp (measurable_fst.fst.prodMk measurable_fst.snd.snd)).mul
    (ht.comp (measurable_fst.fst.prodMk measurable_snd.snd.snd))).ite
      ((measurableSet_sourceLaterRenewal rate rewards C_star C_h control0 s).preimage measurable_fst.fst)
        measurable_const
  let G : A → ℝ≥0∞ := fun h => if h.1 ∈ E then
    Phi (h.1, h.2.2) * (pre s.castSucc h.1).elim 0 (fun S => initialSlowPMF rate S U) else 0
  have hG : Measurable G := ((hPhi.comp (measurable_fst.prodMk measurable_snd.snd)).mul
    ((measurable_of_countable (fun o : Option (RecordedQueueRun.RunState p.K) =>
      o.elim (0 : ℝ≥0∞) (fun S => initialSlowPMF rate S U))).comp
        ((measurable_prefixNumerical rate rewards C_star C_h s.castSucc).comp measurable_fst))).ite
      ((measurableSet_sourceLaterRenewal rate rewards C_star C_h control0 s).preimage measurable_fst)
        measurable_const
  have hpast := measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le
  have hx := measurable_calendarInnovation rate rewards C_star C_h b0 u0 t0 s k
  have hi := calendarLaw_roundPast_innovation_product rate rewards C_star C_h control0 b0 u0 t0
    s (by dsimp only [s]; omega) k hk.le le_rfl
  have hlast : MeasurePreserving (fun x : I => x.2.2)
      (ReferencePostInvocationSupportedDisintegration.innovationLaw (p := p)) ContinuousControlSlice.scalarLaw :=
    (measurePreserving_snd (μ := ContinuousControlSlice.scalarLaw) (ν := ContinuousControlSlice.scalarLaw)).comp
      (measurePreserving_snd (μ := ContinuousLearningRows.timeControlLaw p)
        (ν := ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw))
  have hintegral (h : A) :
      (∫⁻ x : I, F (h, x) ∂ReferencePostInvocationSupportedDisintegration.innovationLaw (p := p)) = G h := by
    by_cases he : h.1 ∈ E
    · simp only [F, he, ite_true]
      have hxTest : Measurable (fun x : I => test (h.1, x.2.2)) :=
        ht.comp (measurable_const.prodMk measurable_snd.snd)
      have hscalar : Measurable (fun x : Scalar => test (h.1, x)) :=
        ht.comp (measurable_const.prodMk measurable_id)
      rw [lintegral_const_mul _ hxTest,
        hlast.lintegral_comp hscalar]
      simp only [G, he, ite_true]
      exact congrArg (fun a : ℝ≥0∞ => Phi (h.1, h.2.2) * a)
        (sourceLaterRenewal_initial_scalar rate rewards C_star C_h control0 s h.1 he U)
    · simp only [F, G, he, ite_false]
      exact lintegral_zero
  calc
    _ = ∫⁻ w, F (past k hk.le w,
        calendarInnovation rate rewards C_star C_h b0 u0 t0 s k w) ∂law k hk.le := by
      apply lintegral_congr
      intro w
      dsimp only [F, test, calendarRoundPast, calendarInnovation]
      rw [← sourceLaterRenewal_sourcePrefix rate rewards C_star C_h control0 s,
        ← freshCallEndpoint_sourcePrefix rate rewards C_star C_h control0 s]
      rfl
    _ = ∫⁻ hx, F hx ∂(law k hk.le).map (fun w =>
        (past k hk.le w, calendarInnovation rate rewards C_star C_h b0 u0 t0 s k w)) :=
      (lintegral_map hF (hpast.prodMk hx)).symm
    _ = ∫⁻ h, ∫⁻ x, F (h, x) ∂ReferencePostInvocationSupportedDisintegration.innovationLaw (p := p)
        ∂(law k hk.le).map (past k hk.le) := by rw [hi]; exact lintegral_prod _ hF.aemeasurable
    _ = ∫⁻ h, G h ∂(law k hk.le).map (past k hk.le) := lintegral_congr hintegral
    _ = ∫⁻ w, G (past k hk.le w) ∂law k hk.le := lintegral_map hG hpast
    _ = _ := by
      apply lintegral_congr
      intro w
      dsimp only [G, calendarRoundPast]
      rw [← sourceLaterRenewal_sourcePrefix rate rewards C_star C_h control0 s,
        ← prefixNumerical_sourcePrefix rate rewards C_star C_h control0 s.castSucc s.val le_rfl]


/-- On the actual generated successor, the present native mark has the
renewal initializer law jointly with the literal strict history. No current
slow seed is supplied to the test, and only incoming PRE is gated. -/
theorem calendarLaw_laterRenewal_initial_cylinder (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (U : SlowSet p) (Phi : Source × List (LogicalCell p rate) → ℝ≥0∞) (hPhi : Measurable Phi) :
    let s : Fin p.T := ⟨t0.val + 1 + k, hk⟩
    (∫⁻ wv, if current k hk.le wv.1 ∈ sourceLaterRenewal rate rewards C_star C_h s then
      Phi (sourcePrefix control0 s.val (current k hk.le wv.1), (stored k hk.le wv.1).2) *
        (calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2).elim 0
          (slowSetCoefficient rate U) else 0 ∂law (k + 1) (by omega)) =
    ∫⁻ wv, if current k hk.le wv.1 ∈ sourceLaterRenewal rate rewards C_star C_h s then
      Phi (sourcePrefix control0 s.val (current k hk.le wv.1), (stored k hk.le wv.1).2) *
        (calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2).elim 0
          (initialMassCoefficient rate U) else 0 ∂law (k + 1) (by omega) := by
  dsimp only
  let s : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  let F : Sample k → ℝ≥0∞ := fun w => if current k hk.le w ∈ sourceLaterRenewal rate rewards C_star C_h s then
    Phi (sourcePrefix control0 s.val (current k hk.le w), (stored k hk.le w).2) *
      (if freshCallEndpoint rate rewards C_star C_h s
        (current k hk.le w, (original k w).1.2 (s, 1)) = some U then 1 else 0) else 0
  let G : Sample k → ℝ≥0∞ := fun w => if current k hk.le w ∈ sourceLaterRenewal rate rewards C_star C_h s then
    Phi (sourcePrefix control0 s.val (current k hk.le w), (stored k hk.le w).2) *
      (pre s.castSucc (current k hk.le w)).elim 0 (fun S => initialSlowPMF rate S U) else 0
  have hz := measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le
  have hpast := measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le
  have hphi := hPhi.comp (hpast.fst.prodMk hpast.snd.snd)
  have hE := (measurableSet_sourceLaterRenewal rate rewards C_star C_h control0 s).preimage hz
  have ha : Measurable (fun w : Sample k => (original k w).1.2 (s, 1)) :=
    (measurable_pi_apply (s, 1)).comp (measurable_calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k).fst.snd
  have hs := (measurable_initial_selector rate rewards C_star C_h control0 s).comp (hz.prodMk ha)
  have hF : Measurable F := (hphi.mul (measurable_const.ite (measurableSet_eq_fun hs measurable_const)
    measurable_const)).ite hE measurable_const
  have hG : Measurable G := (hphi.mul ((measurable_of_countable
    (fun o : Option (RecordedQueueRun.RunState p.K) => o.elim (0 : ℝ≥0∞) (fun S => initialSlowPMF rate S U))).comp
      ((measurable_prefixNumerical rate rewards C_star C_h s.castSucc).comp hz))).ite hE measurable_const
  have hproj : MeasurePreserving (Prod.fst : Sample k × Vector → Sample k)
      (law (k + 1) (by omega)) (law k hk.le) :=
    ⟨measurable_fst, calendarLaw_succ_map_fst rate rewards C_star C_h control0 b0 u0 t0 k (by omega)⟩
  have hstep := ae_calendarLaw_laterRenewal_step rate rewards C_star C_h control0 b0 u0 t0 k hk
  calc
    _ = ∫⁻ wv : Sample k × Vector, F wv.1 ∂law (k + 1) (by omega) := by
      apply lintegral_congr_ae
      filter_upwards [hstep] with wv hwv
      by_cases hw : current k hk.le wv.1 ∈ sourceLaterRenewal rate rewards C_star C_h s
      · obtain ⟨e, he, _hp, hov, hseed⟩ := hwv hw
        dsimp only [s] at hw
        simp only [F, s, hw, ite_true, he, Option.elim_some, slowSetCoefficient, hov,
          Bool.false_eq_true, ite_false, hseed, Option.some.injEq]
      · dsimp only [s] at hw
        simp only [F, s, hw, ite_false]
    _ = ∫⁻ w, F w ∂law k hk.le := hproj.lintegral_comp hF
    _ = ∫⁻ w, G w ∂law k hk.le :=
      calendarLaw_laterRenewal_endpoint_cylinder rate rewards C_star C_h control0 b0 u0 t0 k hk U Phi hPhi
    _ = ∫⁻ wv : Sample k × Vector, G wv.1 ∂law (k + 1) (by omega) := (hproj.lintegral_comp hG).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hstep] with wv hwv
      by_cases hw : current k hk.le wv.1 ∈ sourceLaterRenewal rate rewards C_star C_h s
      · obtain ⟨e, he, hp, hov, _hseed⟩ := hwv hw
        dsimp only [s] at hw
        simp only [G, s, hw, ite_true, he, hp, Option.elim_some, initialMassCoefficient, hov,
          Bool.false_eq_true, ite_false]
      · dsimp only [s] at hw
        simp only [G, s, hw, ite_false]

/-- Filtering the same terminal archive at an earlier PRE boundary recovers
the literal ancestor archive, including all enabled zero-arrival updates. -/
theorem calendar_archiveBefore_ancestor (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (w : Sample k) (j : ℕ) (hj : j ≤ k) :
    ((stored k hk w).2.filter (fun e => e.time.val < t0.val + 1 + j)) =
      (stored j (by omega) (ancestor k j hj w)).2 := by
  induction k with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    rw [calendarAncestor_self]
    exact List.filter_eq_self.mpr (fun e he => decide_eq_true
      ((calendarObservation_chronology rate rewards C_star C_h control0 b0 u0 t0 0 hk w).2 e he))
  | succ k ih =>
    by_cases hjk : j = k + 1
    · subst j
      rw [calendarAncestor_self]
      exact List.filter_eq_self.mpr (fun e he => decide_eq_true
        ((calendarObservation_chronology rate rewards C_star C_h control0 b0 u0 t0 (k + 1) hk w).2 e he))
    · have hjk' : j ≤ k := by omega
      rw [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k j hjk' w]
      change Sample k × Vector at w
      rw [calendarStoredState_succ rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w.1 w.2]
      cases hc : calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w.1 w.2 with
      | none => exact ih (by omega) w.1 hjk'
      | some e =>
        have ht := calendarStepCell_time rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w.1 w.2 e hc
        have hnot : ¬ e.time.val < t0.val + 1 + j := by rw [ht]; dsimp only; omega
        simp only [List.filter_append, List.filter_cons, decide_eq_false hnot,
          Bool.false_eq_true, ite_false, List.filter_nil, List.append_nil]
        exact ih (by omega) w.1 hjk'

/-- The two entries of the literal before-draw history survive every future
full-vector insertion jointly on the same raw sample. -/
theorem calendar_literal_history_ancestor (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (w : Sample k) (j : ℕ) (hj : j ≤ k) :
    (sourcePrefix control0 (t0.val + 1 + j) (current k hk w),
      (stored k hk w).2.filter (fun e => e.time.val < t0.val + 1 + j)) =
    (sourcePrefix control0 (t0.val + 1 + j) (current j (by omega) (ancestor k j hj w)),
      (stored j (by omega) (ancestor k j hj w)).2) :=
  Prod.ext (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj).2.1
    (calendar_archiveBefore_ancestor rate rewards C_star C_h control0 b0 u0 t0 k hk w j hj)

private theorem find_time_none_of_bound (H : List (LogicalCell p rate)) (s : Fin p.T)
    (hH : ∀ e ∈ H, e.time.val < s.val) : H.find? (fun e => e.time == s) = none := by
  apply List.find?_eq_none.mpr
  intro e he
  have hne : e.time ≠ s := fun h => by have := hH e he; rw [h] at this; exact Nat.lt_irrefl _ this
  simpa using hne

private theorem find_time_append_ne (H : List (LogicalCell p rate)) (s : Fin p.T)
    (e : LogicalCell p rate) (hne : e.time ≠ s) :
    (H ++ [e]).find? (fun e => e.time == s) = H.find? (fun e => e.time == s) := by
  simp [List.find?_append, hne]

/-- Every later date's terminal optional mark is literally its own native
step in the actual ancestor; future insertions cannot supply another mark. -/
theorem calendar_find_time_ancestor (k : ℕ) (hk : t0.val + 1 + k ≤ p.T)
    (w : Sample k) (j : ℕ) (hj : j < k) :
    let s : Fin p.T := ⟨t0.val + 1 + j, by omega⟩
    let x : Sample j × Vector := ancestor k (j + 1) (by omega) w
    (stored k hk w).2.find? (fun e => e.time == s) =
      calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 j (by omega) x.1 x.2 := by
  dsimp only
  induction k with
  | zero => omega
  | succ k ih =>
    change Sample k × Vector at w
    by_cases hjk : j = k
    · subst j
      rw [calendarAncestor_self rate rewards C_star C_h b0 u0 t0 (k + 1) w,
        calendarStoredState_succ rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w.1 w.2]
      have hn := find_time_none_of_bound rate (stored k (by omega) w.1).2
        ⟨t0.val + 1 + k, by omega⟩
        (calendarObservation_chronology rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w.1).2
      cases hc : calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w.1 w.2 with
      | none => exact hn
      | some e =>
        have ht := calendarStepCell_time rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w.1 w.2 e hc
        simp [List.find?_append, hn, ht]
    · have hjk' : j < k := by omega
      rw [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k (j + 1) (by omega) w,
        calendarStoredState_succ rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w.1 w.2]
      cases hc : calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w.1 w.2 with
      | none => exact ih (by omega) w.1 hjk'
      | some e =>
        have ht := calendarStepCell_time rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w.1 w.2 e hc
        have hne : e.time ≠ (⟨t0.val + 1 + j, by omega⟩ : Fin p.T) := by
          intro h
          have := congrArg Fin.val (ht.symm.trans h)
          dsimp only at this
          omega
        rw [find_time_append_ne rate _ _ e hne]
        exact ih (by omega) w.1 hjk'

theorem measurable_calendarStepCell (k : ℕ) (hk : t0.val + 1 + k < p.T) :
    Measurable (fun wv : Sample k × Vector =>
      calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2) := by
  have hm : Measurable (fun wv : Sample k × Vector => (stored (k + 1) (by omega) wv).2.find?
      (fun e => e.time == ⟨t0.val + 1 + k, hk⟩)) :=
    (measurable_find_time rate ⟨t0.val + 1 + k, hk⟩).comp
    (measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)).snd.snd
  have heq : (fun wv : Sample k × Vector =>
      calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2) =
      (fun wv : Sample k × Vector => (stored (k + 1) (by omega) wv).2.find?
        (fun e => e.time == ⟨t0.val + 1 + k, hk⟩)) := by
    funext wv
    have h := calendar_find_time_ancestor rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega) wv k (by omega)
    simpa only [calendarAncestor_self rate rewards C_star C_h b0 u0 t0 (k + 1) wv] using h.symm
  rw [heq]
  exact hm

private theorem calendarAncestor_fst (k : ℕ) (w : Sample k) (j : ℕ) (hj : j < k) :
    (ancestor k (j + 1) (by omega) w).1 = ancestor k j (by omega) w := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hjk : j = k
    · subst j
      rw [calendarAncestor_self, calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k k le_rfl w,
        calendarAncestor_self]
    · have hjk' : j < k := by omega
      rw [calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k (j + 1) (by omega) w,
        calendarAncestor_succ rate rewards C_star C_h b0 u0 t0 k j (by omega) w]
      exact ih w.1 hjk'

private def calendarCylinder (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (Phi : Source × List (LogicalCell p rate) → ℝ≥0∞) (f : LogicalCell p rate → ℝ≥0∞)
    (wv : Sample k × Vector) : ℝ≥0∞ :=
  let s : Fin p.T := ⟨t0.val + 1 + k, hk⟩
  if current k hk.le wv.1 ∈ sourceLaterRenewal rate rewards C_star C_h s then
    Phi (sourcePrefix control0 s.val (current k hk.le wv.1), (stored k hk.le wv.1).2) *
      (calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1 wv.2).elim 0 f else 0

private theorem measurable_calendarCylinder (k : ℕ) (hk : t0.val + 1 + k < p.T)
    (Phi : Source × List (LogicalCell p rate) → ℝ≥0∞) (hPhi : Measurable Phi)
    (f : LogicalCell p rate → ℝ≥0∞) (hf : Measurable f) :
    Measurable (calendarCylinder rate rewards C_star C_h control0 b0 u0 t0 k hk Phi f) :=
  ((hPhi.comp (((measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le).fst.prodMk
    (measurable_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le).snd.snd).comp measurable_fst)).mul
      ((measurable_elim_coefficient rate f hf).comp
        (measurable_calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk))).ite
    ((measurableSet_sourceLaterRenewal rate rewards C_star C_h control0 ⟨t0.val + 1 + k, hk⟩).preimage
      ((measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le).comp measurable_fst))
        measurable_const

/-- Terminal transport preserves the SAME full strict history and date mark,
and uses the actual ancestor marginal of the full-vector calendar. -/
private theorem generated_terminal_cylinder (s : Fin p.T) (hts : t0.val < s.val)
    (Phi : Source × List (LogicalCell p rate) → ℝ≥0∞) (hPhi : Measurable Phi)
    (f : LogicalCell p rate → ℝ≥0∞) (hf : Measurable f) :
    let j := s.val - (t0.val + 1)
    (∫⁻ w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h (.generated b0 u0 t0),
      renewalCylinder rate rewards C_star C_h control0 s Phi f ⟨.generated b0 u0 t0, w⟩
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b0 u0 t0)) =
    ∫⁻ wv, calendarCylinder rate rewards C_star C_h control0 b0 u0 t0 j (by dsimp only [j]; omega) Phi f wv
      ∂law (j + 1) (by dsimp only [j]; omega) := by
  dsimp only
  let j := s.val - (t0.val + 1)
  let N := p.T - (t0.val + 1)
  have hdate : t0.val + 1 + j = s.val := by dsimp only [j]; omega
  have hj : j < N := by dsimp only [N]; have := s.isLt; omega
  let x : Sample N → Sample j × Vector := ancestor N (j + 1) (by omega)
  have hfun (w : Sample N) : renewalCylinder rate rewards C_star C_h control0 s Phi f
      ⟨.generated b0 u0 t0, w⟩ = calendarCylinder rate rewards C_star C_h control0 b0 u0 t0 j
        (by omega) Phi f (x w) := by
    have hh := calendar_literal_history_ancestor rate rewards C_star C_h control0 b0 u0 t0 N (by dsimp only [N]; omega) w j hj.le
    rw [← calendarAncestor_fst rate rewards C_star C_h b0 u0 t0 N w j hj] at hh
    rw [hdate] at hh
    have hm := calendar_find_time_ancestor rate rewards C_star C_h control0 b0 u0 t0 N
      (by dsimp only [N]; omega) w j hj
    have hsq : (⟨t0.val + 1 + j, by omega⟩ : Fin p.T) = s := Fin.ext hdate
    dsimp only at hm
    rw [hsq] at hm
    have hE : current N (by dsimp only [N]; omega) w ∈ sourceLaterRenewal rate rewards C_star C_h s ↔
        current j (by omega) (x w).1 ∈ sourceLaterRenewal rate rewards C_star C_h s := by
      rw [sourceLaterRenewal_sourcePrefix rate rewards C_star C_h control0 s,
        sourceLaterRenewal_sourcePrefix rate rewards C_star C_h control0 s (current j (by omega) (x w).1)]
      exact congrArg (fun z : Source => z ∈ sourceLaterRenewal rate rewards C_star C_h s) (congrArg Prod.fst hh) |>.to_iff
    change (if current N (by dsimp only [N]; omega) w ∈ sourceLaterRenewal rate rewards C_star C_h s then
      Phi (sourcePrefix control0 s.val (current N (by dsimp only [N]; omega) w),
        (stored N (by dsimp only [N]; omega) w).2.filter (fun e => e.time.val < s.val)) *
        ((stored N (by dsimp only [N]; omega) w).2.find? (fun e => e.time == s)).elim 0 f else 0) = _
    unfold calendarCylinder
    rw [hsq]
    dsimp only
    rw [hE, hh, hm]
  have hx := measurable_calendarAncestor rate rewards C_star C_h b0 u0 t0 N (j + 1) (by omega)
  have hF := measurable_calendarCylinder rate rewards C_star C_h control0 b0 u0 t0 j (by omega) Phi hPhi f hf
  change (∫⁻ w : Sample N, renewalCylinder rate rewards C_star C_h control0 s Phi f
    ⟨.generated b0 u0 t0, w⟩ ∂law N (by dsimp only [N]; omega)) = _
  calc
    _ = ∫⁻ w, calendarCylinder rate rewards C_star C_h control0 b0 u0 t0 j (by omega) Phi f (x w)
        ∂law N (by dsimp only [N]; omega) := lintegral_congr hfun
    _ = ∫⁻ wv, calendarCylinder rate rewards C_star C_h control0 b0 u0 t0 j (by omega) Phi f wv
        ∂(law N (by dsimp only [N]; omega)).map x := (lintegral_map hF hx).symm
    _ = _ := by
      have hmap : (law N (by dsimp only [N]; omega)).map x = law (j + 1) (by omega) :=
        calendarLaw_map_ancestor rate rewards C_star C_h control0 b0 u0 t0 N
          (by dsimp only [N]; omega) (j + 1) (by omega)
      exact congrArg (fun nu : Measure (Sample j × Vector) => ∫⁻ wv,
        calendarCylinder rate rewards C_star C_h control0 b0 u0 t0 j (by omega) Phi f wv ∂nu) hmap

end Ancestors

private theorem measurable_sigma_mk {I : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] (i : I) : Measurable (Sigma.mk i : B i → Sigma B) :=
  measurable_iff_le_map.mpr (iInf_le _ i)

/-- Exhaustive later-renewal before-initial-draw cylinder under the raw
terminal law. All first-branch components are summed with their original
mass; earlier, same-date, no-call and stopped components are proved absent. -/
theorem terminalLaw_laterRenewal_initial_cylinder_raw (s : Fin p.T) (U : SlowSet p)
    (Phi : Source × List (LogicalCell p rate) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w : Omega, renewalCylinder rate rewards C_star C_h control0 s Phi (slowSetCoefficient rate U) w
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0) =
    ∫⁻ w : Omega, renewalCylinder rate rewards C_star C_h control0 s Phi (initialMassCoefficient rate U) w
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0 := by
  have hF := measurable_renewalCylinder rate rewards C_star C_h control0 s Phi hPhi _
    (measurable_slowSetCoefficient rate U)
  have hG := measurable_renewalCylinder rate rewards C_star C_h control0 s Phi hPhi _
    (measurable_initialMassCoefficient rate U)
  rw [ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw,
    lintegral_sum_measure, lintegral_sum_measure]
  apply tsum_congr
  intro i
  rw [lintegral_map hF (measurable_sigma_mk i), lintegral_map hG (measurable_sigma_mk i)]
  cases i with
  | noCall =>
    apply lintegral_congr
    intro w
    simp only [renewalCylinder, ite_eq_right (noCall_not_laterRenewal rate rewards C_star C_h control0 s w)]
  | stopped u t =>
    apply lintegral_congr
    intro w
    simp only [renewalCylinder, ite_eq_right (stopped_not_laterRenewal rate rewards C_star C_h control0 u t s w)]
  | generated b u t =>
    by_cases ht : t.val < s.val
    · rw [generated_terminal_cylinder rate rewards C_star C_h control0 b u t s ht Phi hPhi _
        (measurable_slowSetCoefficient rate U),
      generated_terminal_cylinder rate rewards C_star C_h control0 b u t s ht Phi hPhi _
        (measurable_initialMassCoefficient rate U)]
      exact calendarLaw_laterRenewal_initial_cylinder rate rewards C_star C_h control0 b u t
        (s.val - (t.val + 1)) (by omega) U Phi hPhi
    · apply lintegral_congr
      intro w
      have hn : (⟨.generated b u t, w⟩ : Omega) ∉ laterRenewalEvent rate rewards C_star C_h control0 s := by
        intro hw
        exact ht ((generated_laterRenewal_first_date rate rewards C_star C_h control0 b u t s w).mp hw.2.2.2)
      simp only [renewalCylinder, ite_eq_right hn]

/-- The same literal later-renewal initialization cylinder under BOTH the
raw law and EVERY original fixed-ID law. Localization normalizes only the
original positive ID atom, retaining the original private arrays and tape. -/
theorem terminalLaw_laterRenewal_initial_cylinder (ids : Option (CompletePublicTable.IDArray p))
    (s : Fin p.T) (U : SlowSet p) (Phi : Source × List (LogicalCell p rate) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ w : Omega, renewalCylinder rate rewards C_star C_h control0 s Phi (slowSetCoefficient rate U) w
      ∂ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)) =
    ∫⁻ w : Omega, renewalCylinder rate rewards C_star C_h control0 s Phi (initialMassCoefficient rate U) w
      ∂ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0) := by
  cases ids with
  | none => exact terminalLaw_laterRenewal_initial_cylinder_raw rate rewards C_star C_h control0 s U Phi hPhi
  | some ids =>
    let D : Set Omega := Z ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids
    have hD : MeasurableSet D := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalSource rate rewards C_star C_h control0)
    let PhiID : Source × List (LogicalCell p rate) → ℝ≥0∞ := fun h =>
      if h.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids then Phi h else 0
    have hPhiID : Measurable PhiID := hPhi.ite
      ((ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage measurable_fst) measurable_const
    have htest (f : LogicalCell p rate → ℝ≥0∞) (w : Omega) :
        D.indicator (renewalCylinder rate rewards C_star C_h control0 s Phi f) w =
          renewalCylinder rate rewards C_star C_h control0 s PhiID f w := by
      have hID : sourcePrefix control0 s.val (Z w) ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids ↔
          Z w ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids := by
        change (sourcePrefix control0 s.val (Z w)).1.1 = ids ↔ (Z w).1.1 = ids
        rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_ids]
      by_cases hw : Z w ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids <;>
        by_cases he : w ∈ laterRenewalEvent rate rewards C_star C_h control0 s <;>
        simp only [Set.indicator, D, Set.mem_preimage, hw, he, ite_true, ite_false,
          renewalCylinder, PhiID, hID, zero_mul]
    change (∫⁻ w, renewalCylinder rate rewards C_star C_h control0 s Phi (slowSetCoefficient rate U) w
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids) =
      ∫⁻ w, renewalCylinder rate rewards C_star C_h control0 s Phi (initialMassCoefficient rate U) w
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0 ids
    rw [ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw_eq_restrict,
      lintegral_smul_measure, lintegral_smul_measure, ← lintegral_indicator hD, ← lintegral_indicator hD]
    apply congrArg (fun a : ℝ≥0∞ => (CompletePublicTable.idArrayMeasure p {ids})⁻¹ * a)
    calc
      _ = ∫⁻ w, renewalCylinder rate rewards C_star C_h control0 s PhiID (slowSetCoefficient rate U) w
          ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0 :=
        lintegral_congr (htest _)
      _ = ∫⁻ w, renewalCylinder rate rewards C_star C_h control0 s PhiID (initialMassCoefficient rate U) w
          ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0 :=
        terminalLaw_laterRenewal_initial_cylinder_raw rate rewards C_star C_h control0 s U PhiID hPhiID
      _ = _ := (lintegral_congr (htest _)).symm

end Bandits.Support.ReferenceGeneratedCalendarLaterRenewalSlowInitialization
