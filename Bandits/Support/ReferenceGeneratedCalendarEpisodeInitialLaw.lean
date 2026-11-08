/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodeSlowLaw

/-!
# Actual episode starts and their initial slow-set law

Sources: ZIP4 `04_slow_fast_learner.tex:176-215,323-365`,
`06_interruptions.tex:391-426`, and `08_main_theorem.tex:78-109`.

The start history is the admitted strict source-prefix/archive observer before
the fresh draw. Original suffix indices are joined to calendar dates explicitly.
These internal results do not identify the finer estimate observer with the
manuscript's floored estimate field or assert a later conditional law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceGeneratedCalendarEpisodeSlowLaw
open ReferenceOriginalCalendarEpisodeChronology
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)

namespace Bandits.Support.ReferenceGeneratedCalendarEpisodeInitialLaw

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace : MeasurableSpace (Source p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Omega" => ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h
local notation "Z" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalSource rate rewards C_star C_h control0
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "records " z:max => ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "launch" => ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
  (rate := rate) rewards C_star C_h
local notation "call" => ReferenceCalendarCollectionCallControlLaw.callAt rate rewards C_star C_h
local notation "pre" => ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h

omit control0 in
/-- Looking up a record at its own physical date recovers that same original
record. The suffix index and physical calendar date are distinct. -/
theorem actualRecord_at_record (z : Source p) (rho : Fin (records z).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (records z)[rho.val].input.time z = some (records z)[rho.val] := by
  have ht := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z rho
  have hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
      (records z)[rho.val].input.time.val := by omega
  rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hs, ht,
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem rho.isLt]

private theorem selected_parameters_at_success {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hrec : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out) :
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

omit control0 in
/-- The actual empty-installation constructor produces a prechoice sampler
call. Empty pending is used through that constructor, never as a sampling law. -/
theorem complete_empty_collection_call (z : Source p) (rho : Fin (records z).length)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hc : (records z)[rho.val].input.state.coordinator = .collection P ledger saved)
    (hp : ledger.pending = ∅) :
    (call (records z)[rho.val].input.time z).isSome = true := by
  let r := (records z)[rho.val]
  have hstep := ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
    rate rewards C_star C_h z rho
  dsimp only at hstep
  rw [hc] at hstep
  obtain ⟨u, hu, core, started, hstart, instruction, hassignment, _htime, _hkind,
    consistent, output, hlocal, _hresult, clockData, installed, selected,
    _hinstall, _hstarted, _hdispatch, hprepared, _htail⟩ := hstep hp
  have hprep : r.output.preparation.coordinator = ReferenceActivePhysicalStep.dispatch r.input := by
    rw [r.output_eq]
    rfl
  have hparam : (ReferenceLaterSamplerParameterMeasurability.parameters? r.input).isSome = true := by
    change (ReferenceLaterAssignmentFibreStep.parameters? r.input).isSome = true
    rw [ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch, ← hprep, hprepared]
    change (LaterAssignmentStartMeasurability.selectedSamplerParameters? P
      ⟨_, instruction, consistent⟩).isSome = true
    rw [selected_parameters_at_success P _ instruction consistent output.reconstruction output.reconstruction_eq]
    rfl
  rw [ReferenceCalendarCollectionCallControlLaw.callAt,
    actualRecord_at_record rate rewards C_star C_h z rho, Option.bind_some,
    ReferenceFirstCollectionSamplerCall.collectionCallAt_isSome]
  exact hparam

omit control0 in
/-- Reverse original-birth join on clear PRE. Both launch and renewal are
derived from the actual original record, including its actual sampler call. -/
theorem episode_birth_sourceStartEvent (z : Source p) (rho : Fin (records z).length)
    (hb : ReferenceCompleteEpisodeAnchorOrigin.IsEpisodeAnchorBirth (records z)[rho.val])
    (hclear : (pre (records z)[rho.val].input.time.castSucc z).any (fun S => !S.overflow) = true) :
    z ∈ sourceStartEvent rate rewards C_star C_h (records z)[rho.val].input.time := by
  refine ⟨?_, hclear⟩
  rcases (complete_episode_birth_iff_launch_or_renewal rate rewards C_star C_h z rho).mp hb with
    hz | ⟨P, ledger, saved, hc, hp, hg⟩
  · left
    obtain ⟨active, ha⟩ := complete_record_launch rate rewards C_star C_h z rho
    have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h).isSome = true := by
      rw [ha]
      rfl
    refine ⟨(ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).mp hsome, ?_⟩
    have ht := ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z rho
    omega
  · right
    refine ⟨complete_empty_collection_call rate rewards C_star C_h z rho P ledger saved hc hp, ?_⟩
    rw [incomingFreezeAt_of_record rate rewards C_star C_h _ z _
      (actualRecord_at_record rate rewards C_star C_h z rho) P ledger saved hc,
      Option.any_some, decide_eq_true_eq]
    exact hg

/-- A retained mark produces its actual original birth, payload, and single
clear strict-prefix seed. The witnesses are shared by every later test and U. -/
theorem ae_retained_episode_origin (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (q : Fin p.T) (e : LogicalCell p rate),
        currentMark rate rewards C_star C_h control0 q w = some e → e.before.overflow = false →
        ∃ (rho : Fin (records (Z w)).length) (P : ReferenceActivePhysicalStep.Payload rate)
          (A : RecordedQueueRun.RunState p.K),
          let s := (records (Z w))[rho.val].input.time
          EpisodeCovers (records (Z w))[rho.val] q ∧
          ReferenceAssignmentPayloadPersistence.InstallationBirth (records (Z w))[rho.val] P ∧
          pre s.castSucc (startHistory rate rewards C_star C_h control0 s w).1 = some A ∧
          A.overflow = false ∧ P.anchor = RecordedQueueRun.scoreWeight Q A ∧
          w ∈ episodeStartEvent rate rewards C_star C_h control0 s ∧
          w ∈ retainedEvent rate rewards C_star C_h control0 s q := by
  filter_upwards [ae_estimate_numerical_update rate rewards C_star C_h control0 ids] with w hw
  intro q e he hec
  have hen := (currentMark_isSome_iff rate rewards C_star C_h control0 q w).mp
    (Option.isSome_iff_exists.mpr ⟨e, he⟩)
  obtain ⟨rho, P, _r, _c, _v, _hr, _hc, _hen, hcover, _huniq, hb, _hP, _hrest⟩ :=
    nominalEnabled_episode_data rate rewards C_star C_h (Z w) q hen
  have hclear : (pre q.castSucc (Z w)).any (fun S => !S.overflow) = true := by
    rw [(hw q e he).2.1, Option.any_some, Bool.not_eq_true']
    exact hec
  obtain ⟨A, hA, hAc, hanchor⟩ := episode_anchor_of_cover
    rate rewards C_star C_h control0 (Z w) q rho P hcover hb hclear
  have hseed : (pre (records (Z w))[rho.val].input.time.castSucc (Z w)).any
      (fun S => !S.overflow) = true := by
    rw [ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix rate rewards C_star C_h control0
      (records (Z w))[rho.val].input.time.castSucc (records (Z w))[rho.val].input.time.val le_rfl,
      hA, Option.any_some, Bool.not_eq_true']
    exact hAc
  exact ⟨rho, P, A, hcover, hb, hA, hAc, hanchor,
    episode_birth_sourceStartEvent rate rewards C_star C_h (Z w) rho hcover.1 hseed,
    hcover.2.1, hcover.2.2, hclear⟩

/-- Reverse retained-date coverage, with uniqueness supplied by the original
episode intervals. It holds simultaneously at every date and every mark. -/
theorem ae_retained_unique_episodeStart (ids : Option (CompletePublicTable.IDArray p)) :
    ∀ᵐ w ∂ids.elim
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0),
      ∀ (q : Fin p.T) (e : LogicalCell p rate),
        currentMark rate rewards C_star C_h control0 q w = some e → e.before.overflow = false →
        ∃! s : Fin p.T, w ∈ episodeStartEvent rate rewards C_star C_h control0 s ∧
          w ∈ retainedEvent rate rewards C_star C_h control0 s q := by
  filter_upwards [ae_retained_episode_origin rate rewards C_star C_h control0 ids] with w hw
  intro q e he hec
  obtain ⟨rho, P, A, hcover, _hb, _hA, _hAc, _hanchor, hs, hret⟩ := hw q e he hec
  refine ⟨(records (Z w))[rho.val].input.time, ⟨hs, hret⟩, ?_⟩
  intro s hs
  obtain ⟨rho', ht, hb⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s (Z w) hs.1
  have hcover' : EpisodeCovers (records (Z w))[rho'.val] q :=
    ⟨hb, ht ▸ hs.2.1, ht ▸ hs.2.2.1⟩
  have heq := complete_episode_interval_at_most_one rate rewards C_star C_h (Z w) q rho' rho hcover' hcover
  exact ht.symm.trans (congrArg (fun k : Fin (records (Z w)).length => (records (Z w))[k.val].input.time) heq)

section InitialPartition

open ReferenceGeneratedCalendarLaterRenewalSlowInitialization

/-- Finite physical launch, with every exhaustive future component retained. -/
def launchEvent (s : Fin p.T) : Set Omega := Z ⁻¹' launch s.val

/-- A renewed FIRST invocation, tested on its actual incoming source before
the draw. FIRST means there has been no earlier sampler invocation. -/
def firstRenewalEvent (s : Fin p.T) : Set Omega :=
  {w | (call s (Z w)).isSome = true ∧
    (incomingFreezeAt rate rewards C_star C_h s (Z w)).any (fun g => decide (g ≤ s.val + 1)) = true ∧
    (pre s.castSucc (Z w)).any (fun S => !S.overflow) = true ∧
    ReferenceFirstCollectionLogicalPrefixExtension.NoCallBefore rate rewards C_star C_h s.castSucc (Z w)}

theorem measurableSet_launchEvent (s : Fin p.T) :
    MeasurableSet (launchEvent rate rewards C_star C_h control0 s) :=
  (ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
    (rate := rate) rewards C_star C_h s.val).preimage
      (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalSource rate rewards C_star C_h control0)

theorem measurableSet_episodeStartEvent (s : Fin p.T) :
    MeasurableSet (episodeStartEvent rate rewards C_star C_h control0 s) :=
  (measurableSet_sourceStartEvent rate rewards C_star C_h control0 s).preimage
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.measurable_terminalSource rate rewards C_star C_h control0)

omit control0 in
private theorem call_none_at_launch (s : Fin p.T) (z : Source p) (hz : z ∈ launch s.val) :
    call s z = none := by
  rcases ReferenceFirstCollectionSamplerOutputLaw.firstCell_cover_or_noCall rate rewards C_star C_h z with
    hn | ⟨u, t, ht⟩
  · exact (ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none rate rewards C_star C_h s z).mp
      ((ReferenceExhaustiveGeneratedCalendarSourceLaw.noCallBefore_terminal_iff
        rate rewards C_star C_h z).mpr hn s s.isLt)
  · have hd := ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_dates
      rate rewards C_star C_h u t z ht
    have hbefore : s.val < ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
        rate rewards C_star C_h z := by
      rw [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell
        rate rewards C_star C_h u t z ht]
      have hstart := hz.2
      omega
    exact (ReferenceFirstCollectionPrecallCalendarSupport.before_cut_iff_no_call_through
      rate rewards C_star C_h s z).mp hbefore s le_rfl

theorem launchEvent_subset_episodeStartEvent (s : Fin p.T) :
    launchEvent rate rewards C_star C_h control0 s ⊆
      episodeStartEvent rate rewards C_star C_h control0 s := by
  intro w hw
  refine ⟨Or.inl hw, ?_⟩
  rw [(ReferenceGeneratedCalendarLaunchSlowInitialization.terminal_launch_numerical
    rate rewards C_star C_h control0 s w hw).1, Option.any_some]
  rfl

theorem laterRenewalEvent_subset_episodeStartEvent (s : Fin p.T) :
    laterRenewalEvent rate rewards C_star C_h control0 s ⊆
      episodeStartEvent rate rewards C_star C_h control0 s := by
  intro w hw
  refine ⟨Or.inr ⟨hw.1, ?_⟩, hw.2.2.1⟩
  rw [incomingFreezeAt_eq_oldFreezeAt_on_call rate rewards C_star C_h s (Z w) hw.1]
  exact hw.2.1

theorem firstRenewalEvent_subset_episodeStartEvent (s : Fin p.T) :
    firstRenewalEvent rate rewards C_star C_h control0 s ⊆
      episodeStartEvent rate rewards C_star C_h control0 s :=
  fun _ hw => ⟨Or.inr ⟨hw.1, hw.2.1⟩, hw.2.2.1⟩

/-- The literal renewal partition is decided entirely by strict pre-draw
source data; no exhaustive future tag is placed in the observation. -/
theorem firstRenewalEvent_eq_history_preimage (s : Fin p.T) :
    firstRenewalEvent rate rewards C_star C_h control0 s =
      startHistory rate rewards C_star C_h control0 s ⁻¹'
        {h | h.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
          (call s h.1).isSome = true ∧ ReferenceFirstCollectionLogicalPrefixExtension.NoCallBefore rate rewards C_star C_h s.castSucc h.1} := by
  ext w
  have hs := sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s (Z w)
  have hc := ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 s (Z w)
  have hn := ReferenceFirstCollectionLogicalPrefixExtension.noCallBefore_sourcePrefix
    rate rewards C_star C_h control0 s.castSucc (Z w)
  simp only [Fin.val_castSucc] at hn
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  dsimp only [startHistory]
  rw [← hs, ← hc, ← hn]
  constructor
  · intro h
    exact ⟨⟨Or.inr ⟨h.1, h.2.1⟩, h.2.2.1⟩, h.1, h.2.2.2⟩
  · rintro ⟨⟨hstart, hclear⟩, hcall, hno⟩
    refine ⟨hcall, ?_, hclear, hno⟩
    rcases hstart with hlaunch | hrenew
    · rw [call_none_at_launch rate rewards C_star C_h s (Z w) hlaunch] at hcall
      cases hcall
    · exact hrenew.2

theorem measurableSet_firstRenewalEvent (s : Fin p.T) :
    MeasurableSet (firstRenewalEvent rate rewards C_star C_h control0 s) := by
  have hc : Measurable (call s) :=
    (ReferenceCalendarCollectionCallControlLaw.callAt_measurable rate rewards C_star C_h control0 s).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (s.val + 1)) le_rfl
  have his : Measurable (fun z : Source p => (call s z).isSome) := by
    convert (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim false
      (fun _ => true) measurable_const).comp hc using 1
    funext z
    change (call s z).isSome = ReferenceCollectionOutcomeMeasurability.optionalElim false (fun _ => true) (call s z)
    cases call s z <;> rfl
  rw [firstRenewalEvent_eq_history_preimage]
  exact (((measurableSet_sourceStartEvent rate rewards C_star C_h control0 s).inter
    (((measurableSet_singleton true).preimage his).inter
      (ReferenceFirstCollectionLogicalPrefixExtension.measurableSet_noCallBefore
        rate rewards C_star C_h control0 s.castSucc))).preimage measurable_fst).preimage
          (measurable_startHistory rate rewards C_star C_h control0 s)

/-- Launch, renewed FIRST, and strict later renewal are exhaustive and
pairwise disjoint on the actual episode opportunity. -/
theorem episodeStartEvent_partition (s : Fin p.T) :
    episodeStartEvent rate rewards C_star C_h control0 s =
      launchEvent rate rewards C_star C_h control0 s ∪
        firstRenewalEvent rate rewards C_star C_h control0 s ∪
          laterRenewalEvent rate rewards C_star C_h control0 s := by
  ext w
  constructor
  · rintro ⟨hstart, hclear⟩
    rcases hstart with hl | ⟨hc, hg⟩
    · exact Or.inl (Or.inl hl)
    · by_cases hn : ReferenceFirstCollectionLogicalPrefixExtension.NoCallBefore rate rewards C_star C_h s.castSucc (Z w)
      · exact Or.inl (Or.inr ⟨hc, hg, hclear, hn⟩)
      · right
        refine ⟨hc, ?_, hclear, hn⟩
        rw [← incomingFreezeAt_eq_oldFreezeAt_on_call rate rewards C_star C_h s (Z w) hc]
        exact hg
  · rintro ((hl | hf) | hr)
    · exact launchEvent_subset_episodeStartEvent rate rewards C_star C_h control0 s hl
    · exact firstRenewalEvent_subset_episodeStartEvent rate rewards C_star C_h control0 s hf
    · exact laterRenewalEvent_subset_episodeStartEvent rate rewards C_star C_h control0 s hr

theorem initial_events_disjoint (s : Fin p.T) :
    Disjoint (launchEvent rate rewards C_star C_h control0 s)
      (firstRenewalEvent rate rewards C_star C_h control0 s) ∧
    Disjoint (launchEvent rate rewards C_star C_h control0 s)
      (laterRenewalEvent rate rewards C_star C_h control0 s) ∧
    Disjoint (firstRenewalEvent rate rewards C_star C_h control0 s)
      (laterRenewalEvent rate rewards C_star C_h control0 s) := by
  refine ⟨Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_⟩
  · intro w hl hf
    have hc := hf.1
    rw [call_none_at_launch rate rewards C_star C_h s (Z w) hl] at hc
    cases hc
  · intro w hl hr
    have hc := hr.1
    rw [call_none_at_launch rate rewards C_star C_h s (Z w) hl] at hc
    cases hc
  · intro _ hf hr
    exact hr.2.2.2 hf.2.2.2

omit control0 in
private theorem first_call_date (u t s : Fin p.T) (z : Source p)
    (hf : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t)
    (hc : (call s z).isSome = true) (hn : ReferenceFirstCollectionLogicalPrefixExtension.NoCallBefore rate rewards C_star C_h s.castSucc z) :
    t = s := by
  have hst := (noCallBefore_on_firstCell rate rewards C_star C_h u t z hf s.castSucc).mp hn
  have hts : t.val ≤ s.val := by
    by_contra h
    have hb : s.val < ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
        rate rewards C_star C_h z := by
      rw [ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell
        rate rewards C_star C_h u t z hf]
      omega
    rw [(ReferenceFirstCollectionPrecallCalendarSupport.before_cut_iff_no_call_through
      rate rewards C_star C_h s z).mp hb s le_rfl] at hc
    cases hc
  exact Fin.ext (by change s.val ≤ t.val at hst; omega)

open ReferenceGeneratedRankCalendarFoundation ReferenceGeneratedCalendarPathAgreement
  ReferenceGeneratedCalendarResidualBlock ReferenceGeneratedCalendarRootRoundLaw in
/-- Strict pre-draw source transport through the complete real calendar,
back to the SAME original root. No future branch is observed by the test. -/
theorem generated_sourcePrefix_root (b : Bool) (u t : Fin p.T)
    (w : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h (.generated b u t)) :
    sourcePrefix control0 t.val (Z ⟨.generated b u t, w⟩) =
      sourcePrefix control0 t.val (calendarOriginalLift rate rewards C_star C_h b u t _ w).1.1.val := by
  let k := p.T - (t.val + 1)
  have hk : t.val + 1 + k ≤ p.T := by dsimp only [k]; omega
  let root := calendarAncestor rate rewards C_star C_h b u t k 0 (Nat.zero_le _) w
  have hroot : root = calendarOriginalLift rate rewards C_star C_h b u t k w :=
    calendarAncestor_original rate rewards C_star C_h b u t k 0 (Nat.zero_le _) w
  have hp := (calendarObservation_ancestor_preserves rate rewards C_star C_h control0 b u t
    k hk w 0 (Nat.zero_le _)).2.1
  have hs := congrArg (sourcePrefix control0 t.val) hp
  simp only [Nat.add_zero, ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
    control0 t.val (t.val + 1) (Nat.le_succ _)] at hs
  change sourcePrefix control0 t.val (calendarCurrentSource rate rewards C_star C_h control0 b u t k hk w) =
    sourcePrefix control0 t.val (calendarCurrentSource rate rewards C_star C_h control0 b u t 0 (by omega) root) at hs
  have hi : sourcePrefix control0 t.val
      (calendarCurrentSource rate rewards C_star C_h control0 b u t 0 (by omega) root) =
        sourcePrefix control0 t.val root.1.1.val :=
    by
      cases b <;> exact congrArg Prod.fst
        (rootInstalledSource_history rate rewards C_star C_h control0 _ u t root.1.1 root.2)
  exact hs.trans (hi.trans (congrArg (fun v : CalendarSample rate rewards C_star C_h b u t 0 =>
    sourcePrefix control0 t.val v.1.1.val) hroot))

private theorem corrected_freeze_not_reached (s : Fin p.T) (z : Source p)
    (u : Fin p.T)
    (hc : z ∈ ReferenceFirstCollectionCorrectedSliceNumericalPrefix.correctedCell rate rewards C_star C_h u s)
    (hcall : (call s z).isSome = true) :
    (incomingFreezeAt rate rewards C_star C_h s z).any (fun g => decide (g ≤ s.val + 1)) ≠ true := by
  rw [incomingFreezeAt_eq_oldFreezeAt_on_call rate rewards C_star C_h s z hcall]
  obtain ⟨g, hg, hgt⟩ := hc.2
  rw [hg, Option.any_some]
  intro h
  have hh := of_decide_eq_true h
  omega

/-- Every actual renewed FIRST start belongs to its genuine original
generated-true component. No successful draw or terminal tag is a premise. -/
theorem firstRenewalEvent_component (s : Fin p.T) (w : Omega)
    (hf : w ∈ firstRenewalEvent rate rewards C_star C_h control0 s) :
    ∃ u : Fin p.T, w.1 = .generated true u s := by
  rcases w with ⟨i, w⟩
  cases i with
  | noCall =>
    have hn := (ReferenceExhaustiveGeneratedCalendarSourceLaw.noCallBefore_terminal_iff
      rate rewards C_star C_h w.1.val).mpr w.1.property s s.isLt
    have hc := hf.1
    change (call s w.1.val).isSome = true at hc
    rw [(ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_iff_callAt_none rate rewards C_star C_h s w.1.val).mp hn] at hc
    cases hc
  | stopped u t =>
    have ht := first_call_date rate rewards C_star C_h u t s w.1.val w.1.property.1.1 hf.1 hf.2.2.2
    subst t
    exact (corrected_freeze_not_reached rate rewards C_star C_h s w.1.val u w.1.property.1 hf.1 hf.2.1).elim
  | generated b u t =>
    have hcell := ReferenceGeneratedCalendarLivePayoff.calendarCurrentSource_firstCell
      rate rewards C_star C_h control0 b u t _ (by omega) w
    have ht := first_call_date rate rewards C_star C_h u t s _ hcell hf.1 hf.2.2.2
    subst t
    cases b with
    | true => exact ⟨u, rfl⟩
    | false =>
      let root := ReferenceGeneratedRankCalendarFoundation.calendarOriginalLift rate rewards C_star C_h false u s _ w
      have hp := generated_sourcePrefix_root rate rewards C_star C_h control0 false u s w
      have hc : call s (Z ⟨.generated false u s, w⟩) = call s root.1.1.val := by
        rw [ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 s,
          hp, ← ReferenceCalendarCollectionCallControlLaw.callAt_factor rate rewards C_star C_h control0 s]
      have hg : incomingFreezeAt rate rewards C_star C_h s (Z ⟨.generated false u s, w⟩) =
          incomingFreezeAt rate rewards C_star C_h s root.1.1.val := by
        rw [incomingFreezeAt_sourcePrefix rate rewards C_star C_h control0 s, hp,
          ← incomingFreezeAt_sourcePrefix rate rewards C_star C_h control0 s]
      have hfirst := root.1.1.property
      change root.1.1.val ∈ ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent rate rewards C_star C_h u s at hfirst
      rw [ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_eq_correctedCell] at hfirst
      exact (corrected_freeze_not_reached rate rewards C_star C_h s root.1.1.val u hfirst.1
        (hc ▸ hf.1) (hg ▸ hf.2.1)).elim

/-- On a true root at date `s`, the actual source has no earlier call and
cannot be the finite launch. The extra gate is the literal actual start. -/
theorem firstRenewalEvent_iff_component (s : Fin p.T) (w : Omega) :
    w ∈ firstRenewalEvent rate rewards C_star C_h control0 s ↔
      w ∈ episodeStartEvent rate rewards C_star C_h control0 s ∧
        ∃ u : Fin p.T, w.1 = .generated true u s := by
  constructor
  · intro hf
    exact ⟨firstRenewalEvent_subset_episodeStartEvent rate rewards C_star C_h control0 s hf,
      firstRenewalEvent_component rate rewards C_star C_h control0 s w hf⟩
  · rintro ⟨hs, u, hu⟩
    rcases w with ⟨i, w⟩
    dsimp only at hu
    subst i
    have hf := ReferenceGeneratedCalendarLivePayoff.calendarCurrentSource_firstCell
      rate rewards C_star C_h control0 true u s _ (by omega) w
    have hd := ReferenceFirstCollectionLogicalNumericalAlignment.firstCall_dates
      rate rewards C_star C_h u s _ hf
    have hn := (noCallBefore_on_firstCell rate rewards C_star C_h u s _ hf s.castSucc).mpr le_rfl
    obtain ⟨hstart, hclear⟩ := hs
    rcases hstart with hl | ⟨hc, hg⟩
    · have hstart := hl.2
      have hsu := hd.1
      change ReferenceCompletePhysicalHistory.physicalStart rate
        (Z ⟨.generated true u s, w⟩) rewards C_star C_h ≤ u.val at hsu
      have hus := hd.2.1
      omega
    · exact ⟨hc, hg, hclear, hn⟩

end InitialPartition

section InitialCylinders

open ReferenceGeneratedCalendarLaterRenewalSlowInitialization

private theorem measurableSet_component (i : ReferenceExhaustiveGeneratedCalendarSourceLaw.Component p) :
    MeasurableSet {w : Omega | w.1 = i} := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro j
  change MeasurableSet {x : ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h j | j = i}
  by_cases hj : j = i <;>
    simp only [hj, Set.ofPred_true, Set.ofPred_false, MeasurableSet.univ, MeasurableSet.empty]

/-- The actual FIRST stratum is the unnormalized union of its original true
root components, each retaining the actual source PRE-clear opportunity. -/
theorem firstRenewalEvent_eq_iUnion (s : Fin p.T) :
    firstRenewalEvent rate rewards C_star C_h control0 s =
      ⋃ u : Fin p.T, {w : Omega | w.1 = .generated true u s} ∩
        episodeStartEvent rate rewards C_star C_h control0 s := by
  ext w
  rw [firstRenewalEvent_iff_component]
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨fun ⟨hs, u, hu⟩ => ⟨u, hu, hs⟩, fun ⟨u, hu, hs⟩ => ⟨hs, u, hu⟩⟩

private theorem first_components_pairwise (s : Fin p.T) :
    Pairwise (fun u v : Fin p.T => Disjoint
      ({w : Omega | w.1 = .generated true u s} ∩ episodeStartEvent rate rewards C_star C_h control0 s)
      ({w : Omega | w.1 = .generated true v s} ∩ episodeStartEvent rate rewards C_star C_h control0 s)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro w hu hv
  exact huv (ReferenceExhaustiveGeneratedCalendarSourceLaw.Component.generated.inj
    (hu.1.symm.trans hv.1)).2.1

/-- Restriction to the actual start splits the original measure additively.
No first-call date, future success, or component measure is normalized. -/
theorem episodeStartEvent_measure_partition (s : Fin p.T) (mu : Measure Omega) :
    mu.restrict (episodeStartEvent rate rewards C_star C_h control0 s) =
      mu.restrict (launchEvent rate rewards C_star C_h control0 s) +
        mu.restrict (firstRenewalEvent rate rewards C_star C_h control0 s) +
          mu.restrict (laterRenewalEvent rate rewards C_star C_h control0 s) := by
  obtain ⟨hlf, hlr, hfr⟩ := initial_events_disjoint rate rewards C_star C_h control0 s
  have hboth : Disjoint
      (launchEvent rate rewards C_star C_h control0 s ∪ firstRenewalEvent rate rewards C_star C_h control0 s)
      (laterRenewalEvent rate rewards C_star C_h control0 s) := by
    apply Set.disjoint_left.mpr
    intro w hw hr
    rcases hw with hl | hf
    · exact Set.disjoint_left.mp hlr hl hr
    · exact Set.disjoint_left.mp hfr hf hr
  rw [episodeStartEvent_partition, Measure.restrict_union hboth
    (measurableSet_laterRenewalEvent rate rewards C_star C_h control0 s),
    Measure.restrict_union hlf (measurableSet_firstRenewalEvent rate rewards C_star C_h control0 s)]

/-- A present clear mark is exactly the singleton selected by the launch
initializer's archived-cell filter. This is a deterministic test transport. -/
theorem archive_filter_at_clear_mark (s : Fin p.T) (w : Omega) (e : LogicalCell p rate)
    (he : currentMark rate rewards C_star C_h control0 s w = some e)
    (hc : e.before.overflow = false) :
    (archive rate rewards C_star C_h control0 w).filter
      (fun f => decide (f.time = s ∧ f.before.overflow = false)) = [e] := by
  let L := (archive rate rewards C_star C_h control0 w).filter
    (fun f => decide (f.time = s ∧ f.before.overflow = false))
  have hn : L.Nodup :=
    ((ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalReadout_chronology
      rate rewards C_star C_h control0 w).filter _).imp (fun h hEq => by
        cases hEq
        exact Nat.lt_irrefl _ h)
  apply List.Perm.eq_singleton
  apply (List.perm_ext_iff_of_nodup hn (List.nodup_singleton e)).mpr
  intro f
  simp only [L, List.mem_filter, decide_eq_true_eq, List.mem_singleton]
  constructor
  · rintro ⟨hm, ht, _⟩
    have hf := (currentMark_eq_some_iff rate rewards C_star C_h control0 s w f).mpr ⟨hm, ht⟩
    exact Option.some.inj (hf.symm.trans he)
  · intro h
    subst f
    obtain ⟨hm, ht⟩ := (currentMark_eq_some_iff rate rewards C_star C_h control0 s w e).mp he
    exact ⟨hm, ht, hc⟩

private theorem archive_filter_coefficient (s : Fin p.T) (w : Omega)
    (f : LogicalCell p rate → ℝ≥0∞) :
    (((archive rate rewards C_star C_h control0 w).filter
      (fun e => decide (e.time = s ∧ e.before.overflow = false))).map f).sum =
      match currentMark rate rewards C_star C_h control0 s w with
      | none => 0
      | some e => if e.before.overflow then 0 else f e := by
  cases he : currentMark rate rewards C_star C_h control0 s w with
  | none =>
    have hnil : (archive rate rewards C_star C_h control0 w).filter
        (fun e => decide (e.time = s ∧ e.before.overflow = false)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e hm
      simp only [decide_eq_true_eq]
      rintro ⟨ht, _⟩
      have hs := (currentMark_eq_some_iff rate rewards C_star C_h control0 s w e).mpr ⟨hm, ht⟩
      rw [he] at hs
      cases hs
    rw [hnil, List.map_nil, List.sum_nil]
  | some e =>
    cases hc : e.before.overflow with
    | false =>
      rw [archive_filter_at_clear_mark rate rewards C_star C_h control0 s w e he hc]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hc,
        Bool.false_eq_true, ite_false]
    | true =>
      have hnil : (archive rate rewards C_star C_h control0 w).filter
          (fun d => decide (d.time = s ∧ d.before.overflow = false)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro d hm
        simp only [decide_eq_true_eq]
        rintro ⟨ht, hd⟩
        have hs := (currentMark_eq_some_iff rate rewards C_star C_h control0 s w d).mpr ⟨hm, ht⟩
        have hde := Option.some.inj (hs.symm.trans he)
        rw [hde, hc] at hd
        cases hd
      simp only [hnil, List.map_nil, List.sum_nil, hc, ite_true]

/-- The accepted launch cylinder, transported to the sole actual optional
mark and start history, under the raw law and every original fixed-ID law. -/
theorem terminalLaw_launch_initial_cylinder (ids : Option (CompletePublicTable.IDArray p))
    (s : Fin p.T) (U : SlowSet p)
    (Phi : Source p × List (LogicalCell p rate) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w : Omega, Phi (startHistory rate rewards C_star C_h control0 s w) *
      initialSetCylinder rate U (currentMark rate rewards C_star C_h control0 s w)
      ∂(ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)).restrict
          (launchEvent rate rewards C_star C_h control0 s)) =
    ∫⁻ w : Omega, Phi (startHistory rate rewards C_star C_h control0 s w) *
      initialMassCylinder rate U (currentMark rate rewards C_star C_h control0 s w)
      ∂(ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)).restrict
          (launchEvent rate rewards C_star C_h control0 s) := by
  have h := ReferenceGeneratedCalendarLaunchSlowInitialization.terminal_launch_slow_cylinder
    rate rewards C_star C_h control0 ids s U Phi hPhi
  change (∫⁻ w : Omega, Phi (startHistory rate rewards C_star C_h control0 s w) *
      (((archive rate rewards C_star C_h control0 w).filter
        (fun e => decide (e.time = s ∧ e.before.overflow = false))).map
          (fun e => if e.slowSet = U then (1 : ℝ≥0∞) else 0)).sum ∂_) =
    ∫⁻ w : Omega, Phi (startHistory rate rewards C_star C_h control0 s w) *
      (((archive rate rewards C_star C_h control0 w).filter
        (fun e => decide (e.time = s ∧ e.before.overflow = false))).map
          (fun e => initialMass rate e.before U)).sum ∂_ at h
  simp_rw [archive_filter_coefficient rate rewards C_star C_h control0] at h
  exact h

/-- Sum the original FIRST component laws on the actual pre-draw FIRST
event. The arbitrary test still sees only `startHistory`. -/
theorem terminalLaw_firstRenewal_initial_cylinder (ids : Option (CompletePublicTable.IDArray p))
    (s : Fin p.T) (U : SlowSet p)
    (Phi : Source p × List (LogicalCell p rate) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w : Omega, Phi (startHistory rate rewards C_star C_h control0 s w) *
      initialSetCylinder rate U (currentMark rate rewards C_star C_h control0 s w)
      ∂(ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)).restrict
          (firstRenewalEvent rate rewards C_star C_h control0 s)) =
    ∫⁻ w : Omega, Phi (startHistory rate rewards C_star C_h control0 s w) *
      initialMassCylinder rate U (currentMark rate rewards C_star C_h control0 s w)
      ∂(ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)).restrict
          (firstRenewalEvent rate rewards C_star C_h control0 s) := by
  let mu := ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
    (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)
  let PhiStart : Source p × List (LogicalCell p rate) → ℝ≥0∞ :=
    fun h => if h.1 ∈ sourceStartEvent rate rewards C_star C_h s then Phi h else 0
  have hPhiStart : Measurable PhiStart := hPhi.ite
    ((measurableSet_sourceStartEvent rate rewards C_star C_h control0 s).preimage measurable_fst) measurable_const
  have hsets (u : Fin p.T) : MeasurableSet
      ({w : Omega | w.1 = .generated true u s} ∩ episodeStartEvent rate rewards C_star C_h control0 s) :=
    (measurableSet_component rate rewards C_star C_h (.generated true u s)).inter
      (measurableSet_episodeStartEvent rate rewards C_star C_h control0 s)
  have htransport (u : Fin p.T) (f : Option (LogicalCell p rate) → ℝ≥0∞) :
      (∫⁻ w : Omega, Phi (startHistory rate rewards C_star C_h control0 s w) *
        f (currentMark rate rewards C_star C_h control0 s w)
        ∂mu.restrict ({w : Omega | w.1 = .generated true u s} ∩
          episodeStartEvent rate rewards C_star C_h control0 s)) =
      ∫⁻ w : Omega, if w.1 = .generated true u s then
        PhiStart (startHistory rate rewards C_star C_h control0 s w) *
          f (currentMark rate rewards C_star C_h control0 s w) else 0 ∂mu := by
    rw [← lintegral_indicator (hsets u)]
    apply lintegral_congr
    intro w
    have hg : (startHistory rate rewards C_star C_h control0 s w).1 ∈ sourceStartEvent rate rewards C_star C_h s ↔
        w ∈ episodeStartEvent rate rewards C_star C_h control0 s :=
      (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s (Z w)).symm
    by_cases ht : w.1 = .generated true u s <;>
      by_cases hs : w ∈ episodeStartEvent rate rewards C_star C_h control0 s <;>
      simp only [PhiStart, Set.indicator, Set.mem_inter_iff, Set.mem_ofPred_eq, hg,
        ht, hs, ite_true, ite_false, zero_mul, and_true, and_false]
  rw [firstRenewalEvent_eq_iUnion,
    Measure.restrict_iUnion (first_components_pairwise rate rewards C_star C_h control0 s) hsets,
    lintegral_sum_measure, lintegral_sum_measure]
  apply tsum_congr
  intro u
  rw [htransport u (initialSetCylinder rate U), htransport u (initialMassCylinder rate U)]
  exact terminalLaw_first_renewal_initial_cylinder rate rewards C_star C_h control0 ids u s U PhiStart hPhiStart

/-- Complete actual initial joint law, on the sole accepted before-draw
history and optional current mark. Only the original positive ID atom is
normalized in the fixed-ID case; every exhaustive component retains its mass.
No coverage, seed, sampler success, or state equality is a caller premise. -/
theorem terminalLaw_initial_cylinder (ids : Option (CompletePublicTable.IDArray p))
    (s : Fin p.T) (U : SlowSet p)
    (Phi : Source p × List (LogicalCell p rate) → ℝ≥0∞) (hPhi : Measurable Phi) :
    (∫⁻ w : Omega, Phi (startHistory rate rewards C_star C_h control0 s w) *
      initialSetCylinder rate U (currentMark rate rewards C_star C_h control0 s w)
      ∂(ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)).restrict
          (episodeStartEvent rate rewards C_star C_h control0 s)) =
    ∫⁻ w : Omega, Phi (startHistory rate rewards C_star C_h control0 s w) *
      initialMassCylinder rate U (currentMark rate rewards C_star C_h control0 s w)
      ∂(ids.elim (ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw rate rewards C_star C_h control0)
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw rate rewards C_star C_h control0)).restrict
          (episodeStartEvent rate rewards C_star C_h control0 s) := by
  rw [episodeStartEvent_measure_partition, lintegral_add_measure, lintegral_add_measure,
    lintegral_add_measure, lintegral_add_measure,
    terminalLaw_launch_initial_cylinder rate rewards C_star C_h control0 ids s U Phi hPhi,
    terminalLaw_firstRenewal_initial_cylinder rate rewards C_star C_h control0 ids s U Phi hPhi]
  congr 1
  rw [← lintegral_indicator (measurableSet_laterRenewalEvent rate rewards C_star C_h control0 s),
    ← lintegral_indicator (measurableSet_laterRenewalEvent rate rewards C_star C_h control0 s)]
  have hset (o : Option (LogicalCell p rate)) :
      o.elim 0 (slowSetCoefficient rate U) = initialSetCylinder rate U o := by
    cases o <;> rfl
  have hmass (o : Option (LogicalCell p rate)) :
      o.elim 0 (initialMassCoefficient rate U) = initialMassCylinder rate U o := by
    cases o <;> rfl
  have h := terminalLaw_laterRenewal_initial_cylinder rate rewards C_star C_h control0 ids s U Phi hPhi
  simp only [renewalCylinder] at h
  simp_rw [hset, hmass] at h
  exact h

end InitialCylinders

end Bandits.Support.ReferenceGeneratedCalendarEpisodeInitialLaw
