/-
Copyright (c) 2026 Bandits formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarEpisodeTransitionCore

/-!
# Later generated calendar transition tests

Sources: ZIP4 `04_slow_fast_learner.tex:329-390` and
`06_interruptions.tex:391-426`.

Internal one-round results on the original unnormalized generated calendar.
These do not assert an episode law or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceGeneratedCalendarEpisodeSlowLaw
open ReferenceGeneratedCalendarEpisodeHistoryTransport
open ReferenceGeneratedCalendarEpisodeTransitionCore
open ReferenceGeneratedCalendarQuantizedRoundKernel
open ReferenceGeneratedRankCalendarFoundation ReferenceGeneratedCalendarResidualBlock
open ReferenceGeneratedCalendarPathAgreement ReferenceGeneratedCalendarMarkedPath
open ReferenceGeneratedCalendarRoundInnovation ReferenceGeneratedCalendarNoncallRoundLaw
open ReferenceGeneratedCalendarRoundLaw ReferenceGeneratedInvocationCallSplice
open ReferencePostInvocationNoncallGeometry ReferencePostInvocationSupportedDisintegration
open ReferenceGeneratedCalendarJointRebase
open ReferenceOriginalCalendarEpisodeChronology

namespace Bandits.Support.ReferenceGeneratedCalendarEpisodeLaterTransition

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) :=
  Subtype.instMeasurableSpace

attribute [local instance] ReferenceRankInstallationRecorderFoundation.optionSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.listMeasurableSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.sumMeasurableSingleton

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p) (b0 : Bool) (u0 t0 : Fin p.T)
  (k : ℕ) (hk : t0.val + 1 + k < p.T)

local notation "q" => (Fin.mk (t0.val + 1 + k) hk)
local notation "Sample" => CalendarSample rate rewards C_star C_h b0 u0 t0 k
local notation "Vector" => AssignmentParameterFibreKernel.AssignmentVector p
local notation "Scalar" => ContinuousControlSlice.Scalar
local notation "Control" => ContinuousLearningRows.TimeControl p
local notation "stored" => calendarStoredState rate rewards C_star C_h control0 b0 u0 t0 k hk.le
local notation "current" => calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 k hk.le
local notation "flag" => calendarCallFlag rate rewards C_star C_h control0 b0 u0 t0 k (by omega)
local notation "invoke" => calendarInvocationSource rate rewards C_star C_h control0 b0 u0 t0 k hk
local notation "sourceAt" => calendarCallSourceAt rate rewards C_star C_h control0 b0 u0 t0 k hk
local notation "refill" => calendarCallRefill rate rewards C_star C_h control0 b0 u0 t0 k hk
local notation "hsource" => calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0
local notation "joint" => calendarStepSourceJoint rate rewards C_star C_h control0 b0 u0 t0
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- The complete incoming source history survives the actual selected-label
UPDATE refill as well as replacement of the entire current physical control.
The other auxiliary label and all assignment coordinates remain present. -/
theorem calendarCallRefill_sourceHistory (s : Fin p.T) (hs : s.val ≤ t0.val + 1 + k)
    (w : Sample) (a : Scalar × Scalar) (c : Control) (x : Scalar) :
    hsource s q k hk.le (refill w a c x) = hsource s q k hk.le w := by
  let filled := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
    (noncallDate_after t0 k) k (w, (c, a))
  have ho := calendarObservation_withUpdateScalar rate rewards C_star C_h control0 b0 u0 t0
    k hk filled x
  have hz : current (refill w a c x) = current filled :=
    congrArg (fun o : TaggedPrefix rate (calendarBoundary t0 k hk.le) => o.2.val.1.1.1.2) ho
  have hst : stored (refill w a c x) = stored filled := by
    have he := congrArg (fun o : TaggedPrefix rate (calendarBoundary t0 k hk.le) =>
      o.2.val.2.2.2) ho
    rw [← calendarStoredState_spec, ← calendarStoredState_spec] at he
    exact Option.some.inj he
  have hh : hsource s q k hk.le (refill w a c x) = hsource s q k hk.le filled := by
    unfold calendarSourceHistory
    rw [hz, hst]
  exact hh.trans (congrArg Prod.fst
    (calendarSourceHistory_fillInnovation rate rewards C_star C_h control0 b0 u0 t0 s k hk hs w (c, a)))

/-- The old set is the genuinely installed CALL set, including renewal. Its
control invariance follows from the accepted installed-view and PRE theorem;
it is not identified with the incoming stored seed. -/
theorem calendarCallRefill_oldSet (w : Sample) (v : Vector) (hc : flag w = true)
    (a : Scalar × Scalar) (c : Control) (x : Scalar) :
    (calendarInvocationCell rate rewards C_star C_h control0 b0 u0 t0 k hk
      (refill w a c x) v
      (calendarCallRefill_call rate rewards C_star C_h control0 b0 u0 t0 k hk w hc a c x)).slowSet =
      (nativeCell rate rewards C_star C_h control0 q (invoke w v hc)
        ReferenceFirstLiveActualRefreshTestLaw.scalarZero).slowSet := by
  rw [calendarCallRefill_cell]
  obtain ⟨hv, hS⟩ := calendarCall_fixed_parameters rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc c
  change (if (nativeBefore rate rewards C_star C_h control0 q (sourceAt w v hc c)).overflow then
      frozenSlowSet p else (nativeSourceCell rate rewards C_star C_h q (sourceAt w v hc c)).selected.view.payload.slowSet) = _
  rw [hv, hS]
  rfl

/-- Source quantization reads the accepted raw UPDATE of the same native
cell. This does not invert a floored estimate to recover its recorder. -/
theorem nativeCell_sourceEstimate (z : InvocationSource rate rewards C_star C_h q) (x : Scalar) :
    sourceCellEstimate rate (nativeCell rate rewards C_star C_h control0 q z x) =
      RecordedRoundMoments.rawEstimate Q (nativeBefore rate rewards C_star C_h control0 q z)
        (nativeSourceCell rate rewards C_star C_h q z).input := by
  funext i
  exact sourceCellEstimate_eq_rawEstimate rate _ _ rfl i

/-- A refill test keeps the actual exposed history and installed old set
beside the source estimate, physical proposal and selected residual output. -/
theorem calendarCallRefill_optional_test (s : Fin p.T) (hs : s.val ≤ t0.val + 1 + k)
    (w : Sample) (v : Vector) (hc : flag w = true) (a : Scalar × Scalar)
    (c : Control) (x : Scalar) (F : TransitionData rate s q → ℝ≥0∞) :
    optionalTransitionTest rate s q F (joint s k hk (refill w a c x, v)) =
      F (hsource s q k hk.le w,
        ((nativeCell rate rewards C_star C_h control0 q (invoke w v hc)
          ReferenceFirstLiveActualRefreshTestLaw.scalarZero).slowSet,
        (RecordedRoundMoments.rawEstimate Q (nativeBefore rate rewards C_star C_h control0 q (sourceAt w v hc c))
          (nativeSourceCell rate rewards C_star C_h q (sourceAt w v hc c)).input,
          ((! (nativeBefore rate rewards C_star C_h control0 q (sourceAt w v hc c)).overflow &&
            ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
              (ReferenceSourceCurrentControlFreshness.u_t p q (sourceAt w v hc c).val)),
            (nativeCell rate rewards C_star C_h control0 q (sourceAt w v hc c) x).nextSlowSet)))) := by
  have hc' := calendarCallRefill_call rate rewards C_star C_h control0 b0 u0 t0 k hk w hc a c x
  simp only [calendarStepSourceJoint, calendarStepCell, dite_eq_left hc', sourceOptionalEstimate_some,
    optionalTransitionTest]
  rw [calendarCallRefill_sourceHistory rate rewards C_star C_h control0 b0 u0 t0 k hk s hs,
    calendarCallRefill_oldSet rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc,
    calendarCallRefill_cell, nativeCell_sourceEstimate, nativeCell_proposal]
  rfl

/-- Evaluation of the actual correlated-history CALL test through the
original physical control and selected UPDATE fibres. Renewal keeps its
installed old set; no slow-set distribution is assumed. -/
theorem calendarCallRefill_quantized_history_test (s : Fin p.T)
    (hs : s.val ≤ t0.val + 1 + k) (w : Sample) (v : Vector) (hc : flag w = true)
    (a : Scalar × Scalar) (F : TransitionData rate s q → ℝ≥0∞) :
    (∫⁻ y, ∫⁻ c, ∫⁻ V, ∫⁻ x,
      optionalTransitionTest rate s q F (joint s k hk (refill w a c x, v))
      ∂calendarCallRefreshFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc c V
      ∂calendarCallRefreshLaw rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc c
      ∂calendarCallControlFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc y
      ∂calendarCallControlLaw rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc) =
      installationTestSum rate rewards q
        (nativeSourceCell rate rewards C_star C_h q (invoke w v hc)).selected.view
        (nativeBefore rate rewards C_star C_h control0 q (invoke w v hc))
        (fun x B V => F (hsource s q k hk.le w,
          ((nativeCell rate rewards C_star C_h control0 q (invoke w v hc)
            ReferenceFirstLiveActualRefreshTestLaw.scalarZero).slowSet, (x, (B, V))))) := by
  let f := fun x B V => F (hsource s q k hk.le w,
    ((nativeCell rate rewards C_star C_h control0 q (invoke w v hc)
      ReferenceFirstLiveActualRefreshTestLaw.scalarZero).slowSet, (x, (B, V))))
  refine Eq.trans ?_ (calendarCall_quantized_test rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc f 0)
  apply lintegral_congr_ae
  apply ae_iff_of_countable.mpr
  intro y hy
  have hf := calendarCall_quantized_fibre_readout rate rewards C_star C_h control0 b0 u0 t0
    k hk w v hc f 0 y hy
  have he : ∀ᵐ c ∂calendarCallControlFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc y,
      (∫⁻ V, ∫⁻ x, optionalTransitionTest rate s q F (joint s k hk (refill w a c x, v))
        ∂calendarCallRefreshFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc c V
        ∂calendarCallRefreshLaw rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc c) =
      commonUpdateTest rate rewards q
        (nativeSourceCell rate rewards C_star C_h q (invoke w v hc)).selected.view
        (nativeBefore rate rewards C_star C_h control0 q (invoke w v hc)) f 0 y := by
    filter_upwards [hf] with c hfc
    refine Eq.trans ?_ hfc.symm
    apply lintegral_congr_ae
    apply ae_iff_of_countable.mpr
    intro V hV
    have hx := calendarCallRefreshFibre_support rate rewards C_star C_h control0 b0 u0 t0
      k hk w v hc a c V hV
    have hxx : ∀ᵐ x ∂calendarCallRefreshFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc c V,
        optionalTransitionTest rate s q F (joint s k hk (refill w a c x, v)) =
          f (RecordedRoundMoments.rawEstimate Q (nativeBefore rate rewards C_star C_h control0 q (sourceAt w v hc c))
            (nativeSourceCell rate rewards C_star C_h q (sourceAt w v hc c)).input)
            (!(nativeBefore rate rewards C_star C_h control0 q (sourceAt w v hc c)).overflow &&
              ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
                (ReferenceSourceCurrentControlFreshness.u_t p q (sourceAt w v hc c).val)) V := by
      filter_upwards [hx] with x hxx
      rw [calendarCallRefill_optional_test rate rewards C_star C_h control0 b0 u0 t0 k hk s hs w v hc]
      rw [calendarCallRefill_cell rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc a c x] at hxx
      exact congrArg (fun V => f
        (RecordedRoundMoments.rawEstimate Q (nativeBefore rate rewards C_star C_h control0 q (sourceAt w v hc c))
          (nativeSourceCell rate rewards C_star C_h q (sourceAt w v hc c)).input)
        (!(nativeBefore rate rewards C_star C_h control0 q (sourceAt w v hc c)).overflow &&
          ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
            (ReferenceSourceCurrentControlFreshness.u_t p q (sourceAt w v hc c).val)) V) hxx
    let : IsProbabilityMeasure (calendarCallRefreshFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc c V) := by
      unfold calendarCallRefreshFibre
      infer_instance
    exact (lintegral_congr_ae hxx).trans (by simp only [lintegral_const, measure_univ, mul_one])
  let : IsProbabilityMeasure (calendarCallControlFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc y) := by
    unfold calendarCallControlFibre
    infer_instance
  exact (lintegral_congr_ae he).trans (by simp only [lintegral_const, measure_univ, mul_one])

/-- The actual CALL view has the episode's original strict-seed anchor.
Coverage and the earlier seed's clear flag are derived from chronology. -/
theorem nativeSource_episode_anchor (s : Fin p.T) (hsq : s.val ≤ (q).val)
    (hq : (q).val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s)
    (z : InvocationSource rate rewards C_star C_h q)
    (hs : z.val ∈ sourceStartEvent rate rewards C_star C_h s)
    (hc : (nativeBefore rate rewards C_star C_h control0 q z).overflow = false) :
    ∃ A : RecordedQueueRun.RunState p.K,
      prefixNumerical rate rewards C_star C_h s.castSucc
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z.val) = some A ∧
      A.overflow = false ∧
      (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor =
        RecordedQueueRun.scoreWeight Q A := by
  let cell := nativeSourceCell rate rewards C_star C_h q z
  have hr := nativeSourceCell_spec rate rewards C_star C_h q z
  have hen : ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled rate rewards C_star C_h q z.val = true := by
    simp only [ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled, hr.1, Option.bind_some,
      ReferenceFirstCollectionCurrentRetainedGate.cell0, hr.2.2, Option.some_or, Option.any_some]
    exact cell.enabled
  obtain ⟨rho, P, r, c, v, hr', _, _, _, huniq, hb, _, _, hv, ha, _⟩ :=
    nominalEnabled_episode_data rate rewards C_star C_h z.val q hen
  have hrr := Option.some.inj (hr'.symm.trans hr.1)
  subst r
  have hvv : v = cell.selected := Option.some.inj (hv.symm.trans cell.selection_actual)
  subst v
  obtain ⟨rho0, ht, hb0⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s z.val hs
  have hcover : EpisodeCovers
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h)[rho0.val] q :=
    ⟨hb0, ht ▸ hsq, ht ▸ hq⟩
  have he := huniq rho0 hcover
  rw [← he] at hb
  have hclear : (prefixNumerical rate rewards C_star C_h (q).castSucc z.val).any
      (fun S => !S.overflow) = true := by
    rw [nativeBefore_prefix rate rewards C_star C_h control0 q z, Option.any_some, hc]
    rfl
  obtain ⟨A, hA, hAc, hanchor⟩ := episode_anchor_of_cover rate rewards C_star C_h control0
    z.val q rho0 P hcover hb hclear
  rw [ht] at hA
  exact ⟨A, hA, hAc, ha.trans hanchor⟩

/-- CALL's incoming numerical PRE equals the source-history replay, without
assuming a replay or seed certificate. -/
theorem calendarCall_sourceHistory_replay (s : Fin p.T) (hs : s.val ≤ t0.val + 1 + k)
    (w : Sample) (v : Vector) (hc : flag w = true)
    (hstart : (hsource s q k hk.le w).1.1 ∈ sourceStartEvent rate rewards C_star C_h s)
    (hq : (q).val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s) :
    sourceEpisodeReplay rate rewards C_star C_h s q (hsource s q k hk.le w) =
      some (nativeBefore rate rewards C_star C_h control0 q (invoke w v hc)) := by
  have hb := calendarInvocationCell_before rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc
  change some (nativeBefore rate rewards C_star C_h control0 q (invoke w v hc)) = _ at hb
  have hn := calendarObservation_numerical rate rewards C_star C_h control0 b0 u0 t0 k hk.le w
  exact (calendarSourceHistory_replay rate rewards C_star C_h control0 b0 u0 t0 s q hs
    k hk.le le_rfl w hstart hq).trans (hn.symm.trans hb.symm)

/-- On the actual retained episode gate the evaluated native CALL kernel is
exactly the common episode kernel at the same installed old set. -/
theorem calendarCallNativeTransitionTest_eq_history (s : Fin p.T)
    (hs : s.val ≤ t0.val + 1 + k) (w : Sample) (v : Vector) (hc : flag w = true)
    (F : TransitionData rate s q → ℝ≥0∞)
    (hstart : (hsource s q k hk.le w).1.1 ∈ sourceStartEvent rate rewards C_star C_h s)
    (hret : hsource s q k hk.le w ∈ sourceHistoryRetained rate rewards C_star C_h s q) :
    installationTestSum rate rewards q
      (nativeSourceCell rate rewards C_star C_h q (invoke w v hc)).selected.view
      (nativeBefore rate rewards C_star C_h control0 q (invoke w v hc))
      (fun x B V => F (hsource s q k hk.le w,
        ((nativeCell rate rewards C_star C_h control0 q (invoke w v hc)
          ReferenceFirstLiveActualRefreshTestLaw.scalarZero).slowSet, (x, (B, V))))) =
      episodeTransitionTest rate rewards C_star C_h s q F (hsource s q k hk.le w)
        (nativeCell rate rewards C_star C_h control0 q (invoke w v hc)
          ReferenceFirstLiveActualRefreshTestLaw.scalarZero).slowSet := by
  let z := invoke w v hc
  let h := hsource s q k hk.le w
  have hpre := calendarCall_sourceHistory_replay rate rewards C_star C_h control0 b0 u0 t0
    k hk s hs w v hc hstart hret.2.1
  have hclear : (nativeBefore rate rewards C_star C_h control0 q z).overflow = false := by
    have ht := hret.2.2
    rw [hpre, Option.any_some, Bool.not_eq_true'] at ht
    exact ht
  have hp : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z.val = h.1.1 :=
    ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q s.val hs _ _
  have hsz : z.val ∈ sourceStartEvent rate rewards C_star C_h s := by
    apply (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s z.val).mpr
    rw [hp]
    exact hstart
  obtain ⟨A, hA, _, ha⟩ := nativeSource_episode_anchor rate rewards C_star C_h control0
    t0 k hk s hs hret.2.1 z hsz hclear
  rw [hp] at hA
  have hU : (nativeCell rate rewards C_star C_h control0 q z
      ReferenceFirstLiveActualRefreshTestLaw.scalarZero).slowSet =
      (nativeSourceCell rate rewards C_star C_h q z).selected.view.payload.slowSet := by
    change (if (nativeBefore rate rewards C_star C_h control0 q z).overflow then _ else _) = _
    rw [hclear]
    rfl
  change sourceEpisodeReplay rate rewards C_star C_h s q h =
    some (nativeBefore rate rewards C_star C_h control0 q z) at hpre
  change _ = episodeTransitionTest rate rewards C_star C_h s q F h _
  simp only [episodeTransitionTest, hA, hpre]
  rw [hU]
  exact (episodeRoundTest_eq_installationTestSum rate rewards q A _ _ ha _).symm

/-- The actual active CALL disintegration gives the retained transition
identity for arbitrary history events. The incoming component is not
normalized, and this calculation uses no old-set law. -/
theorem calendarCallTest_retained_transition (s : Fin p.T)
    (hs : s.val ≤ t0.val + 1 + k) (E : Set (History rate s q))
    (F : TransitionData rate s q → ℝ≥0∞) (w : Sample) :
    calendarCallTest rate rewards C_star C_h control0 b0 u0 t0 k hk
      (fun wv => if hsource s q k hk.le wv.1 ∈ E then
        retainedSourceTest rate rewards C_star C_h s q F (joint s k hk wv) else 0) w =
    calendarCallTest rate rewards C_star C_h control0 b0 u0 t0 k hk
      (fun wv => if hsource s q k hk.le wv.1 ∈ E then
        retainedKernelTest rate rewards C_star C_h s q F (joint s k hk wv) else 0) w := by
  unfold calendarCallTest
  split
  next ha =>
    apply lintegral_congr
    intro a
    apply lintegral_congr
    intro v
    let h := hsource s q k hk.le w
    let U := (nativeCell rate rewards C_star C_h control0 q (invoke w v ha.1)
      ReferenceFirstLiveActualRefreshTestLaw.scalarZero).slowSet
    let G : TransitionData rate s q → ℝ≥0∞ := fun y =>
      if y.1 ∈ E then if y.1.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
        y.1 ∈ sourceHistoryRetained rate rewards C_star C_h s q then F y else 0 else 0
    have hA (c : Control) (x : Scalar) :
        (if hsource s q k hk.le (refill w a c x) ∈ E then
          retainedSourceTest rate rewards C_star C_h s q F
            (joint s k hk (refill w a c x, v)) else 0) =
        optionalTransitionTest rate s q G (joint s k hk (refill w a c x, v)) := by
      have hc' := calendarCallRefill_call rate rewards C_star C_h control0 b0 u0 t0 k hk w ha.1 a c x
      simp only [calendarStepSourceJoint, calendarStepCell, dite_eq_left hc',
        retainedSourceTest, optionalTransitionTest, G]
    have hB (c : Control) (x : Scalar) :
        (if hsource s q k hk.le (refill w a c x) ∈ E then
          retainedKernelTest rate rewards C_star C_h s q F
            (joint s k hk (refill w a c x, v)) else 0) =
        if h ∈ E then if h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
          h ∈ sourceHistoryRetained rate rewards C_star C_h s q then
          episodeTransitionTest rate rewards C_star C_h s q F h U else 0 else 0 := by
      have hc' := calendarCallRefill_call rate rewards C_star C_h control0 b0 u0 t0 k hk w ha.1 a c x
      simp only [calendarStepSourceJoint, calendarStepCell, dite_eq_left hc',
        retainedKernelTest, retainedSourceTest, optionalTransitionTest, kernelLiftTest,
        calendarCallRefill_sourceHistory rate rewards C_star C_h control0 b0 u0 t0 k hk s hs,
        calendarCallRefill_oldSet rate rewards C_star C_h control0 b0 u0 t0 k hk w v ha.1]
      rfl
    simp_rw [hA, hB]
    have hr (c : Control) (V : SlowSet p) :
        calendarCallRefreshFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v ha.1 c V Set.univ = 1 := by
      unfold calendarCallRefreshFibre
      exact measure_univ
    have hR (c : Control) :
        calendarCallRefreshLaw rate rewards C_star C_h control0 b0 u0 t0 k hk w v ha.1 c Set.univ = 1 := by
      unfold calendarCallRefreshLaw
      exact measure_univ
    have hc (y : ReferenceRankInstallationCommonUpdateJointLaw.PairUpdate p × Bool) :
        calendarCallControlFibre rate rewards C_star C_h control0 b0 u0 t0 k hk w v ha.1 y Set.univ = 1 := by
      unfold calendarCallControlFibre
      exact measure_univ
    have hC : calendarCallControlLaw rate rewards C_star C_h control0 b0 u0 t0 k hk w v ha.1 Set.univ = 1 := by
      unfold calendarCallControlLaw
      rw [← Set.univ_prod_univ, Measure.prod_prod]
      unfold ReferenceRankInstallationCommonUpdateJointLaw.commonUpdateKernel
      rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
      unfold ReferenceRankInstallationSourceKernelComposition.installationRecorderFastOutputKernel
      rw [Set.preimage_univ, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
      unfold ReferenceRankInstallationSourceKernelComposition.installationRecorderFastRawKernel
      rw [Set.preimage_univ, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
      unfold FastRewardSliceLaw.liveRecordingFastPushforward
      rw [Set.preimage_univ, Measure.map_apply (FastRewardSliceLaw.measurable_liveRecordingFastPair
        p _ _ _ _ _ _ _ _ _ _ _) MeasurableSet.univ]
      simp only [Set.preimage_univ, measure_univ, one_mul]
    simp only [lintegral_const, hr, hR, hc, hC, mul_one]
    refine (calendarCallRefill_quantized_history_test rate rewards C_star C_h control0 b0 u0 t0
      k hk s hs w v ha.1 a G).trans ?_
    change installationTestSum rate rewards q
      (nativeSourceCell rate rewards C_star C_h q (invoke w v ha.1)).selected.view
      (nativeBefore rate rewards C_star C_h control0 q (invoke w v ha.1))
      (fun x B V => G (h, (U, (x, (B, V))))) = _
    by_cases hE : h ∈ E
    · simp only [G, hE, ite_true]
      by_cases hg : h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
          h ∈ sourceHistoryRetained rate rewards C_star C_h s q
      · simp only [hg, ite_true, and_self]
        exact calendarCallNativeTransitionTest_eq_history rate rewards C_star C_h control0 b0 u0 t0
          k hk s hs w v ha.1 F hg.1 hg.2
      · simp only [hg, ite_false, installationTestSum, lintegral_zero, zero_mul, Finset.sum_const_zero]
    · simp only [G, hE, ite_false, installationTestSum, lintegral_zero, zero_mul, Finset.sum_const_zero]
  next ha => rfl

/-- Literal history-dependent observer of the accepted complete noncall
numerical tuple. Optional absence has value zero; present bottom remains a
present UPDATE. The old set is read from the same incoming past. -/
def noncallHistoryTest (s : Fin p.T) (F : TransitionData rate s q → ℝ≥0∞)
    (y : NoncallRoundData rate) : ℝ≥0∞ :=
  let h := prefixSourceHistory rate control0 s q y.1
  if h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
      h ∈ sourceHistoryRetained rate rewards C_star C_h s q then
    match y.2.2 with
    | (some u, .inr (_, _, B, V)) =>
      F (h, (y.1.2.1, ((fun j => (RecordedQueueRun.acceptedArrival (u.2.2.1 j) : ℝ) / ((Q).n : ℝ)), (B, V))))
    | _ => 0
  else 0

theorem measurable_noncallHistoryTest (s : Fin p.T)
    (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    Measurable (noncallHistoryTest rate rewards C_star C_h control0 t0 k hk s F) := by
  let G : TransitionData rate s q → ℝ≥0∞ := fun y =>
    if y.1.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
      y.1 ∈ sourceHistoryRetained rate rewards C_star C_h s q then F y else 0
  have hG : Measurable G := hF.ite
    (((measurableSet_sourceStartEvent rate rewards C_star C_h control0 s).preimage measurable_fst.fst.fst).inter
      ((measurableSet_sourceHistoryRetained rate rewards C_star C_h s q).preimage measurable_fst))
    measurable_const
  let g : (Option (NumericalUpdate p) × ReferencePostInvocationCollectionNativeLaw.Outcome p) ×
      (BootstrapPrivateRoundStreams.SourceInput p × (SlowSet p × List (LogicalCell p rate))) → ℝ≥0∞ :=
    fun y => match y.1 with
    | (some u, .inr (_, _, B, V)) => G (prefixSourceHistory rate control0 s q y.2,
      (y.2.2.1, ((fun j => (RecordedQueueRun.acceptedArrival (u.2.2.1 j) : ℝ) / ((Q).n : ℝ)), (B, V))))
    | _ => 0
  have hg : Measurable g := by
    apply measurable_from_prod_countable_right
    intro u
    rcases u with ⟨u, o⟩
    cases u with
    | none => exact measurable_const
    | some u =>
      cases o with
      | inl o => exact measurable_const
      | inr o =>
        rcases o with ⟨i, j, B, V⟩
        exact hG.comp ((measurable_prefixSourceHistory (B := SlowSet p) rate control0 s q).prodMk
          (measurable_snd.fst.prodMk (measurable_const.prodMk
            (measurable_const.prodMk measurable_const))))
  have he : noncallHistoryTest rate rewards C_star C_h control0 t0 k hk s F =
      fun y : NoncallRoundData rate => g (y.2.2, y.1) := by
    funext y
    rcases y with ⟨past, n, u, o⟩
    cases u <;> cases o <;> simp only [noncallHistoryTest, g, G, ite_self]
  rw [he]
  exact hg.comp (measurable_snd.snd.prodMk measurable_fst)

/-- The accepted noncall law applied to an actual exposed-history test,
with raw original recorder masses beside the complete numerical UPDATE.
There is no fixed-history or numerical-kernel premise. -/
theorem calendarLaw_noncall_history_test (s : Fin p.T)
    (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv : Sample × Vector, if flag wv.1 = false then
      noncallHistoryTest rate rewards C_star C_h control0 t0 k hk s F
        (calendarNoncallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk wv.1) else 0
      ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)) =
    ∫⁻ w, if flag w = false then
      ∑ i : Option (Fin p.K), ∑ o : ReferencePostInvocationCollectionNativeLaw.Outcome p,
        noncallHistoryTest rate rewards C_star C_h control0 t0 k hk s F
          (calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le w,
            (calendarNoncallNumericalForRaw rate rewards C_star C_h control0 b0 u0 t0 k hk w i o,
              (calendarNoncallUpdateForOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk w o, o))) *
          calendarNoncallRawMass rate rewards C_star C_h control0 b0 u0 t0 k hk w i o else 0
      ∂(calendarLaw rate rewards C_star C_h control0 b0 u0 t0 k hk.le).map
        (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k) := by
  apply calendarLaw_noncall_numerical_test rate rewards C_star C_h control0 b0 u0 t0 k hk
    (noncallHistoryTest rate rewards C_star C_h control0 t0 k hk s F)
  have hU : @Measurable (SlowSet p) (SlowSet p)
      ReferenceGeneratedCalendarNoncallRoundLaw.slowSetMeasurableSpace slowSetMeasurableSpace id :=
    (measurable_id : Measurable (id : SlowSet p → SlowSet p)).mono le_top le_rfl
  exact (measurable_noncallHistoryTest rate rewards C_star C_h control0 t0 k hk s F hF).comp
    ((measurable_fst.fst.prodMk ((hU.comp measurable_fst.snd.fst).prodMk measurable_fst.snd.snd)).prodMk
      measurable_snd)

/-- The proper-past observer reads exactly the already accepted source
history, including every strict predecessor estimate. -/
theorem prefixSourceHistory_calendarRoundPast (s : Fin p.T)
    (hs : s.val ≤ t0.val + 1 + k) (w : Sample) :
    prefixSourceHistory rate control0 s q
      (calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le w) =
      hsource s q k hk.le w := by
  simp only [prefixSourceHistory, calendarRoundPast, calendarSourceHistory,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 s.val _ hs]

/-- The retained source-history gate produces the actual incoming clear
flag. The numerical POST, including a first detecting UPDATE, is not tested. -/
theorem calendarHistory_pending_clear (s : Fin p.T) (hs : s.val ≤ t0.val + 1 + k)
    (w : Sample)
    (hstart : (hsource s q k hk.le w).1.1 ∈ sourceStartEvent rate rewards C_star C_h s)
    (hret : hsource s q k hk.le w ∈ sourceHistoryRetained rate rewards C_star C_h s q) :
    (calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k (by omega) w).2 = true := by
  have hp := calendarSourceHistory_replay rate rewards C_star C_h control0 b0 u0 t0 s q hs
    k hk.le le_rfl w hstart hret.2.1
  have ht := hret.2.2
  rw [hp] at ht
  change ((calendarObservation rate rewards C_star C_h control0 b0 u0 t0 k hk.le w).2.val.2.2.1).any
    (fun S => !S.overflow) = true
  rw [calendarObservation_numerical]
  exact ht

/-- On an actual noncall, the history-dependent numerical observer is the
retained source test. Clear LIVE seed agreement is supplied by generated
geometry; absent, disabled and incoming-overflow branches remain literal. -/
theorem noncallHistoryTest_actual (s : Fin p.T) (hs : s.val ≤ t0.val + 1 + k)
    (w : Sample) (v : Vector) (hc : flag w = false)
    (F : TransitionData rate s q → ℝ≥0∞) :
    noncallHistoryTest rate rewards C_star C_h control0 t0 k hk s F
        (calendarNoncallRoundReadout rate rewards C_star C_h control0 b0 u0 t0 k hk w) =
      retainedSourceTest rate rewards C_star C_h s q F (joint s k hk (w, v)) := by
  have hnot : ¬ flag w = true := by rw [hc]; exact Bool.false_ne_true
  have hp := prefixSourceHistory_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0
    k hk s hs w
  let h := hsource s q k hk.le w
  unfold noncallHistoryTest calendarNoncallRoundReadout
  dsimp only
  rw [hp]
  change (if h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
      h ∈ sourceHistoryRetained rate rewards C_star C_h s q then _ else 0) = _
  by_cases hg : h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
      h ∈ sourceHistoryRetained rate rewards C_star C_h s q
  · rw [ite_eq_left hg]
    dsimp only [h] at hg
    have hcl := calendarHistory_pending_clear rate rewards C_star C_h control0 b0 u0 t0
      k hk s hs w hg.1 hg.2
    cases he : calendarNoncallCell rate rewards C_star C_h control0 b0 u0 t0 k hk w with
    | none =>
      simp only [calendarNoncallUpdate, calendarNoncallOutcome, he, Option.map_none,
        ReferencePostInvocationCollectionNativeLaw.optionalOutcome, retainedSourceTest,
        calendarStepSourceJoint, calendarStepCell, dite_eq_right hnot,
        show noncallDateCell rate rewards C_star C_h q (current w)
          (calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k w).1.2 (stored w).1 = none from he,
        optionalTransitionTest, ite_self]
    | some e =>
      obtain ⟨_, input, _, _, _, _, _, hn, _, _, harr, _⟩ :=
        calendarNoncallCell_actualInput rate rewards C_star C_h control0 b0 u0 t0 k hk w v hc e he
      have hU := (calendarObservation_noncall_clear_cell rate rewards C_star C_h control0 b0 u0 t0
        k hk w v hc hcl e he).1
      have hx : sourceCellEstimate rate e =
          fun j => (RecordedQueueRun.acceptedArrival (e.arrivals j) : ℝ) / ((Q).n : ℝ) := by
        funext j
        rw [sourceCellEstimate_eq_rawEstimate rate e input hn j, harr]
        rfl
      have hstep : calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk w v = some e := by
        rw [calendarStepCell, dite_eq_right hnot]
        exact he
      simp only [calendarNoncallUpdate, calendarNoncallOutcome, he, Option.map_some,
        ReferencePostInvocationCollectionNativeLaw.optionalOutcome,
        ReferencePostInvocationCollectionNativeLaw.cellOutcome, cellUpdate,
        retainedSourceTest, calendarStepSourceJoint, hstep, sourceOptionalEstimate_some,
        optionalTransitionTest, hg, hU, hx]
      rfl
  · rw [ite_eq_right hg]
    dsimp only [h] at hg
    simp only [retainedSourceTest, calendarStepSourceJoint, hg, ite_false]

/-- Actual retained noncall source tests are evaluated jointly with the
proper history and complete raw numerical data. Coefficients remain the
original native raw masses, including zero-mass and stopped recorder atoms. -/
theorem calendarLaw_noncall_retained_source_test (s : Fin p.T)
    (hs : s.val ≤ t0.val + 1 + k) (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv : Sample × Vector, if flag wv.1 = false then
      retainedSourceTest rate rewards C_star C_h s q F (joint s k hk wv) else 0
      ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)) =
    ∫⁻ w, if flag w = false then
      ∑ i : Option (Fin p.K), ∑ o : ReferencePostInvocationCollectionNativeLaw.Outcome p,
        noncallHistoryTest rate rewards C_star C_h control0 t0 k hk s F
          (calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le w,
            (calendarNoncallNumericalForRaw rate rewards C_star C_h control0 b0 u0 t0 k hk w i o,
              (calendarNoncallUpdateForOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk w o, o))) *
          calendarNoncallRawMass rate rewards C_star C_h control0 b0 u0 t0 k hk w i o else 0
      ∂(calendarLaw rate rewards C_star C_h control0 b0 u0 t0 k hk.le).map
        (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k) := by
  refine Eq.trans ?_ (calendarLaw_noncall_history_test rate rewards C_star C_h control0 b0 u0 t0 k hk s F hF)
  apply lintegral_congr
  intro wv
  split
  next hc =>
    rw [noncallHistoryTest_actual rate rewards C_star C_h control0 b0 u0 t0 k hk s hs wv.1 wv.2 hc]
    rfl
  next hc => rfl

/-- The retained actual active CALL identity under the original raw
unnormalized calendar law, jointly with any measurable source-history event.
The proof evaluates the same-source physical and selected-refresh fibres. -/
theorem calendarLaw_call_retained_transition_test (s : Fin p.T)
    (hs : s.val ≤ t0.val + 1 + k) (E : Set (History rate s q)) (hE : MeasurableSet E)
    (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv : Sample × Vector,
      if wv.1 ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then
        if hsource s q k hk.le wv.1 ∈ E then
          retainedSourceTest rate rewards C_star C_h s q F (joint s k hk wv) else 0 else 0
      ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)) =
    ∫⁻ wv : Sample × Vector,
      if wv.1 ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then
        if hsource s q k hk.le wv.1 ∈ E then
          retainedKernelTest rate rewards C_star C_h s q F (joint s k hk wv) else 0 else 0
      ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega) := by
  let A : Sample × Vector → ℝ≥0∞ := fun wv => if hsource s q k hk.le wv.1 ∈ E then
    retainedSourceTest rate rewards C_star C_h s q F (joint s k hk wv) else 0
  let B : Sample × Vector → ℝ≥0∞ := fun wv => if hsource s q k hk.le wv.1 ∈ E then
    retainedKernelTest rate rewards C_star C_h s q F (joint s k hk wv) else 0
  have hj := measurable_calendarStepSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s k hk
  have he : MeasurableSet {wv : Sample × Vector | hsource s q k hk.le wv.1 ∈ E} :=
    hE.preimage ((measurable_calendarSourceHistory rate rewards C_star C_h control0 b0 u0 t0
    s q k hk.le).comp measurable_fst)
  have hA : Measurable A :=
    ((measurable_retainedSourceTest rate rewards C_star C_h control0 s q F hF).comp hj).ite he measurable_const
  have hB : Measurable B :=
    ((measurable_retainedKernelTest rate rewards C_star C_h control0 s q F hF).comp hj).ite he measurable_const
  refine (calendarLaw_call_round_test rate rewards C_star C_h control0 b0 u0 t0 k hk A hA).trans ?_
  refine Eq.trans ?_ (calendarLaw_call_round_test rate rewards C_star C_h control0 b0 u0 t0 k hk B hB).symm
  exact lintegral_congr (calendarCallTest_retained_transition rate rewards C_star C_h control0 b0 u0 t0
    k hk s hs E F)

/-- Every original fixed-ID component has the actual joint innovation
transport. Only the genuine original ID atom is normalized; generated
component masses and every whole-vector fibre remain unnormalized. This is
transport, not an evaluation of the noncall common kernel. -/
theorem generated_fixedID_component_source_joint_innovation_test
    (ids : CompletePublicTable.IDArray p) (s : Fin p.T)
    (hs : s.val ≤ t0.val + 1 + k)
    (F : History rate s q × (Estimate p × Option (LogicalCell p rate)) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ w, F (terminalSourceJoint rate rewards C_star C_h control0 s q ⟨.generated b0 u0 t0, w⟩)
      ∂ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw rate rewards C_star C_h control0
        ids (.generated b0 u0 t0)) =
      (CompletePublicTable.idArrayMeasure p {ids})⁻¹ *
      ∫⁻ w, ∫⁻ x, ∫⁻ v,
        let filled := calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
          (noncallDate_after t0 k) k (w, x)
        let mark := calendarStepCell rate rewards C_star C_h control0 b0 u0 t0 k hk filled v
        if (hsource s q k hk.le w).1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids then
          F (hsource s q k hk.le w, (sourceOptionalEstimate rate mark, mark)) else 0
        ∂calendarExtensionKernel rate rewards C_star C_h control0 b0 u0 t0 k (by omega)
          (calendarFillInnovation rate rewards C_star C_h control0 b0 u0 t0 q
            (noncallDate_after t0 k) k (w, x))
        ∂innovationLaw (p := p)
        ∂(calendarLaw rate rewards C_star C_h control0 b0 u0 t0 k hk.le).map
          (calendarEraseInnovation rate rewards C_star C_h control0 b0 u0 t0 q (noncallDate_after t0 k) k) := by
  let E : Set (History rate s q × (Estimate p × Option (LogicalCell p rate))) :=
    {y | y.1.1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection ids}
  have hE : MeasurableSet E := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
    measurable_fst.fst.fst
  have hfixed := generated_component_source_joint_step_test rate rewards C_star C_h control0 b0 u0 t0
    (some ids) s k hk hs F hF
  have hraw := generated_component_source_joint_step_test rate rewards C_star C_h control0 b0 u0 t0
    none s k hk hs (E.indicator F) (hF.indicator hE)
  have hinno := generated_component_source_joint_innovation_test rate rewards C_star C_h control0 b0 u0 t0
    s k hk hs (E.indicator F) (hF.indicator hE)
  dsimp only at hfixed hraw hinno
  refine hfixed.trans ?_
  simp only [Option.elim, lintegral_smul_measure]
  apply congrArg (fun z : ℝ≥0∞ => (CompletePublicTable.idArrayMeasure p {ids})⁻¹ * z)
  have hsection := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
    (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega))
  rw [← lintegral_indicator hsection]
  refine Eq.trans ?_ (hraw.symm.trans hinno)
  apply lintegral_congr
  intro wv
  have hID : (calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega) wv).1.1 =
      (joint s k hk wv).1.1.1.1.1 :=
    congrArg (fun y : History rate s q × (Estimate p × Option (LogicalCell p rate)) => y.1.1.1.1.1)
      (calendarSourceJoint_step rate rewards C_star C_h control0 b0 u0 t0 s k hk hs wv)
  simp only [Set.indicator_apply, E, Set.mem_preimage, ReferenceFixedIDSourceSection.fixedIDSourceSection,
    Set.mem_ofPred_eq]
  rw [hID]

open ReferenceActivePhysicalStep in
private theorem collectionCall_selection_payload (r : Record rate)
    (P : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm P.slowSet → ℝ)
    (hcall : ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r = some ⟨P, ledger, started, weights⟩)
    (v : ReferenceActivePhysicalStep.Selection r.input)
    (hv : r.output.preparation.coordinator.selection = some v) : v.view.payload = P := by
  unfold ReferenceLaterCollectionArrivalReadout.laterCollectionCall at hcall
  split at hcall
  next =>
    cases hc : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp only [hc] at hcall <;> contradiction
    | collection old oldLedger clock cutoff outcome =>
      cases outcome <;> simp only [hc] at hcall
      all_goals try contradiction
      case continuing core snapshot boundary checked =>
        cases Option.some.inj hcall
        simp only [hc, DispatchCut.selection] at hv
        cases Option.some.inj hv
        rfl
    | live a b base outcome =>
      cases outcome <;> simp only [hc] at hcall
      all_goals try contradiction
      case cutoffChosen dispatched hs newLedger hi he hd hclock hp hn arm =>
        split at hcall
        next =>
          cases Option.some.inj hcall
          simp only [hc, DispatchCut.selection, selectionAt] at hv
          cases Option.some.inj hv
          rfl
        next => contradiction
    | invalidCollectionCutoff => simp only [hc] at hcall; contradiction
    | dagger => simp only [hc] at hcall; contradiction
  next => contradiction

/-- An actual continuing LIVE input has the SAME original episode anchor
as the strict source seed. Its PRE-clear condition supplies earlier clear. -/
theorem continuingSource_episode_anchor (s : Fin p.T) (hsq : s.val ≤ (q).val)
    (hq : (q).val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s)
    (z : ContinuingLiveSource rate rewards C_star C_h q)
    (hs : z.val ∈ sourceStartEvent rate rewards C_star C_h s)
    (hc : (continuingBefore rate rewards C_star C_h q z).overflow = false) :
    ∃ A : RecordedQueueRun.RunState p.K,
      prefixNumerical rate rewards C_star C_h s.castSucc
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z.val) = some A ∧
      A.overflow = false ∧
      (continuingSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor =
        RecordedQueueRun.scoreWeight Q A := by
  let cell := continuingSourceCell rate rewards C_star C_h q z
  have hr := continuingSourceCell_spec rate rewards C_star C_h q z
  have hen : ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled rate rewards C_star C_h q z.val = true := by
    simp only [ReferenceExhaustiveGeneratedCalendarSourceLaw.nominalEnabled, hr.1, Option.bind_some,
      ReferenceFirstCollectionCurrentRetainedGate.cell0, hr.2.1, Option.some_or, Option.any_some]
    rw [← hr.2.2]
    exact cell.enabled
  obtain ⟨rho, P, r, c, v, hr', _, _, _, huniq, hb, _, _, hv, ha, _⟩ :=
    nominalEnabled_episode_data rate rewards C_star C_h z.val q hen
  have hrr := Option.some.inj (hr'.symm.trans hr.1)
  subst r
  have hvv : v = cell.selected := Option.some.inj (hv.symm.trans cell.selection_actual)
  subst v
  obtain ⟨rho0, ht, hb0⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s z.val hs
  have hcover : EpisodeCovers
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h)[rho0.val] q :=
    ⟨hb0, ht ▸ hsq, ht ▸ hq⟩
  have he := huniq rho0 hcover
  rw [← he] at hb
  have hclear : (prefixNumerical rate rewards C_star C_h (q).castSucc z.val).any
      (fun S => !S.overflow) = true := by
    rw [ReferencePostInvocationPrefixLocality.continuingBefore_spec rate rewards C_star C_h q z,
      Option.any_some, hc]
    rfl
  obtain ⟨A, hA, hAc, hanchor⟩ := episode_anchor_of_cover rate rewards C_star C_h control0
    z.val q rho0 P hcover hb hclear
  rw [ht] at hA
  exact ⟨A, hA, hAc, ha.trans hanchor⟩

/-- A COLLECTION round inside the actual retained source episode is enabled
and has its original old anchor equal to the SAME strict source seed's
weight. Neither enablement nor an anchor equality is an input. -/
theorem collectionSource_episode_anchor (s : Fin p.T) (hsq : s.val ≤ (q).val)
    (hq : (q).val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s)
    (z : CollectionDateSource rate rewards C_star C_h q)
    (hs : z.val ∈ sourceStartEvent rate rewards C_star C_h s)
    (hc : (collectionBefore rate rewards C_star C_h q z).overflow = false) :
    (collectionInput rate rewards C_star C_h q z).enabled = true ∧
    ∃ A : RecordedQueueRun.RunState p.K,
      prefixNumerical rate rewards C_star C_h s.castSucc
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z.val) = some A ∧
      A.overflow = false ∧
      (collectionArguments rate rewards C_star C_h q z).1.anchor = RecordedQueueRun.scoreWeight Q A := by
  obtain ⟨rho0, ht, hb0⟩ := sourceStartEvent_episode_birth rate rewards C_star C_h s z.val hs
  have hcover : EpisodeCovers
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h)[rho0.val] q :=
    ⟨hb0, ht ▸ hsq, ht ▸ hq⟩
  have hen := (nominalEnabled_iff_unique_episode rate rewards C_star C_h z.val q).mpr
    ⟨rho0, hcover, fun other ho => complete_episode_interval_at_most_one
      rate rewards C_star C_h z.val q other rho0 ho hcover⟩
  obtain ⟨rho, P, r, c, v, hr, hi, hcen, _, huniq, hb, _, _, hv, ha, _⟩ :=
    nominalEnabled_episode_data rate rewards C_star C_h z.val q hen
  have hr' := collectionRecord_spec rate rewards C_star C_h q z
  have hrr := Option.some.inj (hr.symm.trans hr'.1)
  subst r
  have hin : c = collectionInput rate rewards C_star C_h q z :=
    Option.some.inj (hi.symm.trans (Option.some_get hr'.2.1).symm)
  have hp := collectionCall_selection_payload rate (collectionRecord rate rewards C_star C_h q z)
    (collectionArguments rate rewards C_star C_h q z).1
    (collectionArguments rate rewards C_star C_h q z).2.1
    (collectionArguments rate rewards C_star C_h q z).2.2.1
    (collectionArguments rate rewards C_star C_h q z).2.2.2
    (collectionArguments_spec rate rewards C_star C_h q z) v hv
  have he := huniq rho0 hcover
  rw [← he] at hb
  have hclear : (prefixNumerical rate rewards C_star C_h (q).castSucc z.val).any
      (fun S => !S.overflow) = true := by
    rw [ReferencePostInvocationPrefixLocality.collectionBefore_spec rate rewards C_star C_h q z,
      Option.any_some, hc]
    rfl
  obtain ⟨A, hA, hAc, hanchor⟩ := episode_anchor_of_cover rate rewards C_star C_h control0
    z.val q rho0 P hcover hb hclear
  rw [ht] at hA
  exact ⟨hin ▸ hcen, A, hA, hAc, (congrArg (fun P : ReferenceActivePhysicalStep.Payload rate => P.anchor) hp).symm.trans
    (ha.trans hanchor)⟩

/-- The continuing LIVE native kernel evaluates to the common episode
kernel, with its strict seed constructed internally from the original
source. The old set is the actual installed set, with no distribution input. -/
theorem continuingSource_quantized_episode_test (s : Fin p.T) (hsq : s.val ≤ (q).val)
    (hq : (q).val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s)
    (z : ContinuingLiveSource rate rewards C_star C_h q)
    (hs : z.val ∈ sourceStartEvent rate rewards C_star C_h s)
    (hc : (continuingBefore rate rewards C_star C_h q z).overflow = false)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (f : Estimate p → Bool → SlowSet p → ℝ≥0∞) :
    ∃ A : RecordedQueueRun.RunState p.K,
      prefixNumerical rate rewards C_star C_h s.castSucc
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z.val) = some A ∧
      A.overflow = false ∧
      (∫⁻ x, outcomeTest rate (continuingBefore rate rewards C_star C_h q z)
        (ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q z) f 0
        (ReferencePostInvocationLiveNativeLaw.sourceOutcome rate rewards C_star C_h control0 q z a x)
        ∂innovationLaw (p := p)) =
      episodeRoundTest rate rewards q A (continuingBefore rate rewards C_star C_h q z)
        (continuingSourceCell rate rewards C_star C_h q z).selected.view.payload.slowSet f := by
  obtain ⟨A, hA, hAc, ha⟩ := continuingSource_episode_anchor rate rewards C_star C_h control0 t0 k hk
    s hsq hq z hs hc
  refine ⟨A, hA, hAc, ?_⟩
  have hi (i : Option (Fin p.K)) : ReferencePostInvocationLiveNativeLaw.inputForMarker
      rate rewards C_star C_h q z i = episodeRoundInput rate rewards q A i := by
    have hr := liveRound_reward rate rewards C_star C_h q z i
    have hx := congrArg RecordedQueueRun.RoundInput.rate (liveRound_eq_fixedRoundInput rate rewards C_star C_h q z i)
    change (ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q z i).rate =
      CanonicalRecordingRates.xi p rate.eta.val (continuingSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor at hx
    rw [ha] at hx
    have he : (ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q z i).enabled =
        (episodeRoundInput rate rewards q A i).enabled := (continuingSourceCell rate rewards C_star C_h q z).enabled
    have hm : (ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q z i).recordedArm =
        (episodeRoundInput rate rewards q A i).recordedArm := rfl
    change (ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q z i).reward =
      (episodeRoundInput rate rewards q A i).reward at hr
    change (ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q z i).rate =
      (episodeRoundInput rate rewards q A i).rate at hx
    generalize ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q z i = c at he hm hr hx ⊢
    generalize episodeRoundInput rate rewards q A i = d at he hm hr hx ⊢
    cases c
    cases d
    cases he
    cases hm
    cases hr
    cases hx
    rfl
  refine (live_source_quantized_test rate rewards C_star C_h q control0 z a hc f 0).trans ?_
  unfold episodeRoundTest
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro V _
  simp only [hi, ha, proposalBitLaw_mass]
  cases B with
  | true =>
    simp only [ite_true, episodeNextLaw, hc, Bool.false_eq_true, ite_false,
      Bool.not_false, Bool.true_and,
      ReferencePostInvocationLiveNativeLaw.residualLaw, hi, ha,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), RecordedSlowRefresh.residualPMF_apply]
    ac_rfl
  | false =>
    simp only [Bool.false_eq_true, ite_false, episodeNextLaw, hc, Bool.not_false, Bool.true_and, Measure.dirac_apply,
      Set.mem_singleton_iff, Set.indicator_apply, Pi.one_apply]
    simp only [eq_comm]
    ac_rfl

/-- The enabled, retained COLLECTION native kernel evaluates to the
common episode kernel at its actual incoming old set. Enablement and the
strict seed are derived from the original source episode. -/
theorem collectionSource_quantized_episode_test (s : Fin p.T) (hsq : s.val ≤ (q).val)
    (hq : (q).val + 1 < FollowerCutoffScan.gridBoundary p rate.eta.val s)
    (z : CollectionDateSource rate rewards C_star C_h q)
    (hs : z.val ∈ sourceStartEvent rate rewards C_star C_h s)
    (hc : (collectionBefore rate rewards C_star C_h q z).overflow = false)
    (U : SlowSet p) (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (f : Estimate p → Bool → SlowSet p → ℝ≥0∞) :
    ∃ A : RecordedQueueRun.RunState p.K,
      prefixNumerical rate rewards C_star C_h s.castSucc
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 s.val z.val) = some A ∧
      A.overflow = false ∧
      (∫⁻ x, outcomeTest rate (collectionBefore rate rewards C_star C_h q z)
        (ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q z) f 0
        (ReferencePostInvocationCollectionNativeLaw.sourceOutcome rate rewards C_star C_h control0 q z U a x)
        ∂innovationLaw (p := p)) =
      episodeRoundTest rate rewards q A (collectionBefore rate rewards C_star C_h q z) U f := by
  obtain ⟨hen, A, hA, hAc, ha⟩ := collectionSource_episode_anchor rate rewards C_star C_h control0 t0 k hk
    s hsq hq z hs hc
  refine ⟨A, hA, hAc, ?_⟩
  have hi (i : Option (Fin p.K)) : ReferencePostInvocationCollectionNativeLaw.markerRound
      rate rewards C_star C_h q z i = episodeRoundInput rate rewards q A i := by
    have hr := collectionRound_reward rate rewards C_star C_h q z i
    have hx := congrArg RecordedQueueRun.RoundInput.rate
      (collectionRound_eq_fixedRoundInput rate rewards C_star C_h q z i)
    change (ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q z i).rate =
      CanonicalRecordingRates.xi p rate.eta.val (collectionArguments rate rewards C_star C_h q z).1.anchor at hx
    rw [ha] at hx
    have he : (ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q z i).enabled =
        (episodeRoundInput rate rewards q A i).enabled := hen
    have hm : (ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q z i).recordedArm =
        (episodeRoundInput rate rewards q A i).recordedArm := rfl
    change (ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q z i).reward =
      (episodeRoundInput rate rewards q A i).reward at hr
    change (ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q z i).rate =
      (episodeRoundInput rate rewards q A i).rate at hx
    generalize ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q z i = c at he hm hr hx ⊢
    generalize episodeRoundInput rate rewards q A i = d at he hm hr hx ⊢
    cases c
    cases d
    cases he
    cases hm
    cases hr
    cases hx
    rfl
  refine (collection_source_quantized_test rate rewards C_star C_h q control0 z U a hen hc f 0).trans ?_
  unfold episodeRoundTest
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro V _
  simp only [hi, ReferencePostInvocationCollectionNativeLaw.recorderPMF, ha, proposalBitLaw_mass]
  cases B with
  | true =>
    simp only [ite_true, episodeNextLaw, hc, Bool.false_eq_true, ite_false,
      Bool.not_false, Bool.true_and, ReferencePostInvocationCollectionNativeLaw.auxiliaryMass, hi, ha,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), RecordedSlowRefresh.residualPMF_apply]
    ac_rfl
  | false =>
    simp only [Bool.false_eq_true, ite_false, episodeNextLaw, hc, Bool.not_false, Bool.true_and,
      ReferencePostInvocationCollectionNativeLaw.auxiliaryMass, Measure.dirac_apply,
      Set.mem_singleton_iff, Set.indicator_apply, Pi.one_apply]
    simp only [eq_comm]
    ac_rfl

/-- The actual noncall raw numerical masses evaluate the retained common
kernel at the same exposed history and incoming set. The retained gate
produces enablement, clear PRE, strict seed and original anchor internally. -/
theorem calendarNoncall_retained_history_raw_sum (s : Fin p.T)
    (hs : s.val ≤ t0.val + 1 + k) (w : Sample) (hc : flag w = false)
    (F : TransitionData rate s q → ℝ≥0∞) :
    (∑ i : Option (Fin p.K), ∑ o : ReferencePostInvocationCollectionNativeLaw.Outcome p,
      noncallHistoryTest rate rewards C_star C_h control0 t0 k hk s F
        (calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le w,
          (calendarNoncallNumericalForRaw rate rewards C_star C_h control0 b0 u0 t0 k hk w i o,
            (calendarNoncallUpdateForOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk w o, o))) *
        calendarNoncallRawMass rate rewards C_star C_h control0 b0 u0 t0 k hk w i o) =
      if (hsource s q k hk.le w).1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
          hsource s q k hk.le w ∈ sourceHistoryRetained rate rewards C_star C_h s q then
        episodeTransitionTest rate rewards C_star C_h s q F (hsource s q k hk.le w) (stored w).1 else 0 := by
  let h := hsource s q k hk.le w
  let f : Estimate p → Bool → SlowSet p → ℝ≥0∞ := fun x B V => F (h, ((stored w).1, (x, (B, V))))
  have hp := prefixSourceHistory_calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk s hs w
  by_cases hg : h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
      h ∈ sourceHistoryRetained rate rewards C_star C_h s q
  · dsimp only [h] at hg
    rw [ite_eq_left hg]
    have hstart : current w ∈ sourceStartEvent rate rewards C_star C_h s :=
      (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s (current w)).mpr hg.1
    have hpre := calendarSourceHistory_replay rate rewards C_star C_h control0 b0 u0 t0 s q hs
      k hk.le le_rfl w hg.1 hg.2.2.1
    by_cases hlive : current w ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
        rate rewards C_star C_h q
    · let z : ContinuingLiveSource rate rewards C_star C_h q := ⟨current w, hlive⟩
      rw [ReferencePostInvocationPrefixLocality.continuingBefore_spec rate rewards C_star C_h q z] at hpre
      have hclear : (continuingBefore rate rewards C_star C_h q z).overflow = false := by
        have ht := hg.2.2.2
        rw [hpre, Option.any_some, Bool.not_eq_true'] at ht
        exact ht
      have hU := calendarNoncall_live_seed rate rewards C_star C_h control0 b0 u0 t0 k hk w hlive
        (calendarHistory_pending_clear rate rewards C_star C_h control0 b0 u0 t0 k hk s hs w hg.1 hg.2)
      obtain ⟨A, hA, _, htest⟩ := continuingSource_quantized_episode_test rate rewards C_star C_h control0
        t0 k hk s hs hg.2.2.1 z hstart hclear (calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k w).1.2 f
      have he (i : Option (Fin p.K)) (o : ReferencePostInvocationCollectionNativeLaw.Outcome p) :
          noncallHistoryTest rate rewards C_star C_h control0 t0 k hk s F
            (calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le w,
              (calendarNoncallNumericalForRaw rate rewards C_star C_h control0 b0 u0 t0 k hk w i o,
                (calendarNoncallUpdateForOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk w o, o))) =
          outcomeTest rate (continuingBefore rate rewards C_star C_h q z)
            (ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q z) f 0 o := by
        unfold noncallHistoryTest
        rw [hp, ite_eq_left hg]
        cases o with
        | inl o => rfl
        | inr o =>
          rcases o with ⟨i, j, B, V⟩
          simp only [calendarNoncallUpdateForOutcome, dite_eq_left hlive]
          rfl
      simp_rw [he]
      refine (calendarNoncallRaw_refill_test rate rewards C_star C_h control0 b0 u0 t0 k hk w hc
        (fun io => outcomeTest rate (continuingBefore rate rewards C_star C_h q z)
          (ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q z) f 0 io.2)).symm.trans ?_
      simp_rw [calendarNoncallOutcome_fill_live rate rewards C_star C_h control0 b0 u0 t0 k hk w hlive]
      refine htest.trans ?_
      change prefixNumerical rate rewards C_star C_h s.castSucc h.1.1 = some A at hA
      change sourceEpisodeReplay rate rewards C_star C_h s q h = _ at hpre
      change _ = episodeTransitionTest rate rewards C_star C_h s q F h (stored w).1
      simp only [episodeTransitionTest, hA, hpre]
      rw [← hU]
    · have hcol := (calendarNoncall_phase rate rewards C_star C_h control0 b0 u0 t0 k hk w hc).resolve_left hlive
      let z : CollectionDateSource rate rewards C_star C_h q := ⟨current w, hcol⟩
      rw [ReferencePostInvocationPrefixLocality.collectionBefore_spec rate rewards C_star C_h q z] at hpre
      have hclear : (collectionBefore rate rewards C_star C_h q z).overflow = false := by
        have ht := hg.2.2.2
        rw [hpre, Option.any_some, Bool.not_eq_true'] at ht
        exact ht
      obtain ⟨A, hA, _, htest⟩ := collectionSource_quantized_episode_test rate rewards C_star C_h control0
        t0 k hk s hs hg.2.2.1 z hstart hclear (stored w).1
          (calendarOriginalLift rate rewards C_star C_h b0 u0 t0 k w).1.2 f
      have he (i : Option (Fin p.K)) (o : ReferencePostInvocationCollectionNativeLaw.Outcome p) :
          noncallHistoryTest rate rewards C_star C_h control0 t0 k hk s F
            (calendarRoundPast rate rewards C_star C_h control0 b0 u0 t0 k hk.le w,
              (calendarNoncallNumericalForRaw rate rewards C_star C_h control0 b0 u0 t0 k hk w i o,
                (calendarNoncallUpdateForOutcome rate rewards C_star C_h control0 b0 u0 t0 k hk w o, o))) =
          outcomeTest rate (collectionBefore rate rewards C_star C_h q z)
            (ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q z) f 0 o := by
        unfold noncallHistoryTest
        rw [hp, ite_eq_left hg]
        cases o with
        | inl o => rfl
        | inr o =>
          rcases o with ⟨i, j, B, V⟩
          simp only [calendarNoncallUpdateForOutcome, dite_eq_right hlive, dite_eq_left hcol]
          rfl
      simp_rw [he]
      refine (calendarNoncallRaw_refill_test rate rewards C_star C_h control0 b0 u0 t0 k hk w hc
        (fun io => outcomeTest rate (collectionBefore rate rewards C_star C_h q z)
          (ReferencePostInvocationCollectionNativeLaw.markerRound rate rewards C_star C_h q z) f 0 io.2)).symm.trans ?_
      simp_rw [calendarNoncallOutcome_fill_collection rate rewards C_star C_h control0 b0 u0 t0 k hk w hlive hcol]
      refine htest.trans ?_
      change prefixNumerical rate rewards C_star C_h s.castSucc h.1.1 = some A at hA
      change sourceEpisodeReplay rate rewards C_star C_h s q h = _ at hpre
      change _ = episodeTransitionTest rate rewards C_star C_h s q F h (stored w).1
      simp only [episodeTransitionTest, hA, hpre]
      rfl
  · dsimp only [h] at hg
    simp only [noncallHistoryTest, hp, hg, ite_false, zero_mul, Finset.sum_const_zero]

private theorem episodeRoundTest_const (A S : RecordedQueueRun.RunState p.K)
    (U : SlowSet p) (c : ℝ≥0∞) : episodeRoundTest rate rewards q A S U (fun _ _ _ => c) = c := by
  have hN (i : Option (Fin p.K)) (B : Bool) : episodeNextLaw rate rewards q A S U i B Set.univ = 1 := by
    unfold episodeNextLaw
    split
    · exact measure_univ
    · split <;> exact measure_univ
  have hV (i : Option (Fin p.K)) (B : Bool) :
      (∑ V : SlowSet p, episodeNextLaw rate rewards q A S U i B {V}) = 1 := by
    have h := (lintegral_fintype (μ := episodeNextLaw rate rewards q A S U i B) (fun _ => 1)).symm
    simpa only [one_mul, lintegral_const, hN] using h
  have hP : (∑ B : Bool, ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B}) = 1 := by
    have h := (lintegral_fintype (μ := ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate)
      (fun _ => 1)).symm
    simpa only [one_mul, lintegral_const, measure_univ] using h
  have hI : (∑ i : Option (Fin p.K), RecordedRoundMoments.recordingOutcomePMF
      (anchorRates rate (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A)) i) = 1 := by
    simpa only [tsum_fintype] using (RecordedRoundMoments.recordingOutcomePMF
      (anchorRates rate (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A))).tsum_coe
  unfold episodeRoundTest
  have hv (i : Option (Fin p.K)) (B : Bool) :
      (∑ V : SlowSet p, c * (episodeNextLaw rate rewards q A S U i B {V} *
        (RecordedRoundMoments.recordingOutcomePMF
          (anchorRates rate (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A)) i *
          ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B}))) =
      c * (RecordedRoundMoments.recordingOutcomePMF
        (anchorRates rate (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A)) i *
        ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B}) := by
    calc
      _ = (∑ V : SlowSet p, episodeNextLaw rate rewards q A S U i B {V}) *
          (c * (RecordedRoundMoments.recordingOutcomePMF
            (anchorRates rate (RecordedQueueRun.scoreWeight Q A) (RecordedSlowRefresh.scoreWeight_pos Q A)) i *
            ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B})) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro V _
        ac_rfl
      _ = _ := by rw [hV, one_mul]
  simp_rw [hv]
  simp only [← mul_assoc, ← Finset.mul_sum, hP, hI, mul_one]

private theorem episodeTransitionTest_kernelLift (s : Fin p.T)
    (F : TransitionData rate s q → ℝ≥0∞) (h : History rate s q) (U : SlowSet p) :
    episodeTransitionTest rate rewards C_star C_h s q (kernelLiftTest rate rewards C_star C_h s q F) h U =
      episodeTransitionTest rate rewards C_star C_h s q F h U := by
  cases hA : prefixNumerical rate rewards C_star C_h s.castSucc h.1.1 with
  | none => simp only [episodeTransitionTest, hA]
  | some A =>
    cases hS : sourceEpisodeReplay rate rewards C_star C_h s q h with
    | none => simp only [episodeTransitionTest, hA, hS]
    | some S =>
      simp only [episodeTransitionTest, kernelLiftTest, hA, hS]
      exact episodeRoundTest_const rate rewards t0 k hk A S U _

/-- Actual retained noncall identity under the original unnormalized
calendar law. Both sides use the SAME old set and history. -/
theorem calendarLaw_noncall_retained_transition_test (s : Fin p.T)
    (hs : s.val ≤ t0.val + 1 + k) (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv : Sample × Vector, if flag wv.1 = false then
      retainedSourceTest rate rewards C_star C_h s q F (joint s k hk wv) else 0
      ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)) =
    ∫⁻ wv : Sample × Vector, if flag wv.1 = false then
      retainedKernelTest rate rewards C_star C_h s q F (joint s k hk wv) else 0
      ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega) := by
  have hl := calendarLaw_noncall_retained_source_test rate rewards C_star C_h control0 b0 u0 t0 k hk s hs F hF
  have hr := calendarLaw_noncall_retained_source_test rate rewards C_star C_h control0 b0 u0 t0 k hk s hs
    (kernelLiftTest rate rewards C_star C_h s q F)
    (measurable_kernelLiftTest rate rewards C_star C_h s q F hF)
  refine hl.trans (Eq.trans ?_ hr.symm)
  apply lintegral_congr
  intro w
  split
  next hc =>
    rw [calendarNoncall_retained_history_raw_sum rate rewards C_star C_h control0 b0 u0 t0 k hk s hs w hc F,
      calendarNoncall_retained_history_raw_sum rate rewards C_star C_h control0 b0 u0 t0 k hk s hs w hc
        (kernelLiftTest rate rewards C_star C_h s q F), episodeTransitionTest_kernelLift]
  next hc => rfl

private theorem retainedSourceTest_zero_of_stopped (s : Fin p.T)
    (hs : s.val ≤ t0.val + 1 + k) (wv : Sample × Vector)
    (hc : (calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k (by omega) wv.1).2 ≠ true)
    (F : TransitionData rate s q → ℝ≥0∞) :
    retainedSourceTest rate rewards C_star C_h s q F (joint s k hk wv) = 0 := by
  have hg : ¬ ((hsource s q k hk.le wv.1).1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
      hsource s q k hk.le wv.1 ∈ sourceHistoryRetained rate rewards C_star C_h s q) := by
    intro hg
    exact hc (calendarHistory_pending_clear rate rewards C_star C_h control0 b0 u0 t0 k hk s hs wv.1 hg.1 hg.2)
  simp only [retainedSourceTest, calendarStepSourceJoint, hg, ite_false]

private theorem calendarLaw_retained_partition (s : Fin p.T)
    (hs : s.val ≤ t0.val + 1 + k) (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv : Sample × Vector, retainedSourceTest rate rewards C_star C_h s q F (joint s k hk wv)
      ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)) =
    (∫⁻ wv : Sample × Vector, if wv.1 ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then
      retainedSourceTest rate rewards C_star C_h s q F (joint s k hk wv) else 0
      ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)) +
    (∫⁻ wv : Sample × Vector, if flag wv.1 = false then
      retainedSourceTest rate rewards C_star C_h s q F (joint s k hk wv) else 0
      ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)) := by
  let A : Sample × Vector → ℝ≥0∞ := fun wv => retainedSourceTest rate rewards C_star C_h s q F (joint s k hk wv)
  have he (wv : Sample × Vector) : A wv =
      (if wv.1 ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then A wv else 0) +
      (if flag wv.1 = false then A wv else 0) := by
    by_cases hc : flag wv.1 = true
    · by_cases hcl : (calendarPendingFlags rate rewards C_star C_h control0 b0 u0 t0 k (by omega) wv.1).2 = true
      · have ha : wv.1 ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk := ⟨hc, hcl⟩
        simp only [ha, ite_true, hc, Bool.true_eq_false, ite_false, add_zero]
      · have hz : A wv = 0 := retainedSourceTest_zero_of_stopped rate rewards C_star C_h control0 b0 u0 t0
          k hk s hs wv hcl F
        simp only [hz, ite_self, add_zero]
    · have hnc : flag wv.1 = false := Bool.eq_false_iff.mpr hc
      simp only [calendarActiveEvent, Set.mem_ofPred_eq, hnc, Bool.false_eq_true, false_and,
        ite_false, ite_true, zero_add]
  have hA : Measurable A := (measurable_retainedSourceTest rate rewards C_star C_h control0 s q F hF).comp
    (measurable_calendarStepSourceJoint rate rewards C_star C_h control0 b0 u0 t0 s k hk)
  have hm : Measurable (fun wv : Sample × Vector =>
      if wv.1 ∈ calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk then A wv else 0) :=
    hA.ite ((measurableSet_calendarActiveEvent rate rewards C_star C_h control0 b0 u0 t0 k hk).preimage
    (measurable_fst : Measurable (Prod.fst : Sample × Vector → Sample))) measurable_const
  exact (lintegral_congr he).trans (lintegral_add_left hm _)

/-- Combined actual later CALL and noncall retained identity for the raw
unnormalized generated calendar law. Stopped and absent branches contribute
zero only through their actual source retention and optional-cell gates. -/
theorem calendarLaw_retained_transition_test (s : Fin p.T)
    (hs : s.val ≤ t0.val + 1 + k) (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ wv : Sample × Vector, retainedSourceTest rate rewards C_star C_h s q F (joint s k hk wv)
      ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega)) =
    ∫⁻ wv : Sample × Vector, retainedKernelTest rate rewards C_star C_h s q F (joint s k hk wv)
      ∂calendarLaw rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega) := by
  have hcall := calendarLaw_call_retained_transition_test rate rewards C_star C_h control0 b0 u0 t0 k hk
    s hs Set.univ MeasurableSet.univ F hF
  simp only [Set.mem_univ, ite_true] at hcall
  have hnoncall := calendarLaw_noncall_retained_transition_test rate rewards C_star C_h control0 b0 u0 t0
    k hk s hs F hF
  refine (calendarLaw_retained_partition rate rewards C_star C_h control0 b0 u0 t0 k hk s hs F hF).trans ?_
  rw [hcall, hnoncall]
  exact (calendarLaw_retained_partition rate rewards C_star C_h control0 b0 u0 t0 k hk s hs
    (kernelLiftTest rate rewards C_star C_h s q F)
    (measurable_kernelLiftTest rate rewards C_star C_h s q F hF)).symm

private theorem episodeTransitionTest_history_indicator (s : Fin p.T)
    (E : Set (History rate s q)) (F : TransitionData rate s q → ℝ≥0∞)
    (h : History rate s q) (U : SlowSet p) :
    episodeTransitionTest rate rewards C_star C_h s q (fun y => if y.1 ∈ E then F y else 0) h U =
      if h ∈ E then episodeTransitionTest rate rewards C_star C_h s q F h U else 0 := by
  by_cases he : h ∈ E
  · simp only [episodeTransitionTest, episodeRoundTest, he, ite_true]
  · cases hA : prefixNumerical rate rewards C_star C_h s.castSucc h.1.1 <;>
      cases hS : sourceEpisodeReplay rate rewards C_star C_h s q h <;>
      simp only [episodeTransitionTest, hA, hS, episodeRoundTest, he, ite_false,
        zero_mul, Finset.sum_const_zero]

private theorem retainedSourceTest_history_indicator (s : Fin p.T)
    (E : Set (History rate s q)) (F : TransitionData rate s q → ℝ≥0∞)
    (v : History rate s q × (Estimate p × Option (LogicalCell p rate))) :
    retainedSourceTest rate rewards C_star C_h s q (fun y => if y.1 ∈ E then F y else 0) v =
      if v.1 ∈ E then retainedSourceTest rate rewards C_star C_h s q F v else 0 := by
  unfold retainedSourceTest
  by_cases hg : v.1.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
      v.1 ∈ sourceHistoryRetained rate rewards C_star C_h s q
  · simp only [hg, and_self, ite_true]
    cases ho : v.2.2 <;> simp only [optionalTransitionTest, ho, ite_self]
  · simp only [hg, ite_false, ite_self]

private theorem retainedKernelTest_history_indicator (s : Fin p.T)
    (E : Set (History rate s q)) (F : TransitionData rate s q → ℝ≥0∞)
    (v : History rate s q × (Estimate p × Option (LogicalCell p rate))) :
    retainedKernelTest rate rewards C_star C_h s q (fun y => if y.1 ∈ E then F y else 0) v =
      if v.1 ∈ E then retainedKernelTest rate rewards C_star C_h s q F v else 0 := by
  unfold retainedKernelTest retainedSourceTest
  by_cases hg : v.1.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
      v.1 ∈ sourceHistoryRetained rate rewards C_star C_h s q
  · simp only [hg, and_self, ite_true]
    cases ho : v.2.2 with
    | none => simp only [optionalTransitionTest, ho, ite_self]
    | some e =>
      simp only [optionalTransitionTest, ho, kernelLiftTest]
      exact episodeTransitionTest_history_indicator rate rewards C_star C_h t0 k hk s E F v.1 e.slowSet
  · simp only [hg, ite_false, ite_self]

/-- Combined actual later CALL and noncall retained transition identity for
RAW and EVERY original fixed-ID generated component. The original component
mass is unnormalized; only the genuine original ID atom is normalized.
No old-set distribution, desired kernel, replay, seed or anchor premise is
supplied by the consumer. -/
theorem generated_component_later_retained_transition_test
    (ids : Option (CompletePublicTable.IDArray p)) (s : Fin p.T)
    (hs : s.val ≤ t0.val + 1 + k) (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, retainedSourceTest rate rewards C_star C_h s q F
        (terminalSourceJoint rate rewards C_star C_h control0 s q ⟨.generated b0 u0 t0, w⟩)
      ∂ids.elim
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b0 u0 t0))
        (fun id => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw
          rate rewards C_star C_h control0 id (.generated b0 u0 t0))) =
    ∫⁻ w, retainedKernelTest rate rewards C_star C_h s q F
        (terminalSourceJoint rate rewards C_star C_h control0 s q ⟨.generated b0 u0 t0, w⟩)
      ∂ids.elim
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw rate rewards C_star C_h control0 (.generated b0 u0 t0))
        (fun id => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw
          rate rewards C_star C_h control0 id (.generated b0 u0 t0)) := by
  have hl := generated_component_source_joint_step_test rate rewards C_star C_h control0 b0 u0 t0 ids s k hk hs
    (retainedSourceTest rate rewards C_star C_h s q F)
    (measurable_retainedSourceTest rate rewards C_star C_h control0 s q F hF)
  have hr := generated_component_source_joint_step_test rate rewards C_star C_h control0 b0 u0 t0 ids s k hk hs
    (retainedKernelTest rate rewards C_star C_h s q F)
    (measurable_retainedKernelTest rate rewards C_star C_h control0 s q F hF)
  refine hl.trans (Eq.trans ?_ hr.symm)
  cases ids with
  | none => exact calendarLaw_retained_transition_test rate rewards C_star C_h control0 b0 u0 t0 k hk s hs F hF
  | some id =>
    let E : Set (History rate s q) := {h | h.1.1 ∈ ReferenceFixedIDSourceSection.fixedIDSourceSection id}
    have hE : MeasurableSet E := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection id).preimage
      measurable_fst.fst
    have h := calendarLaw_retained_transition_test rate rewards C_star C_h control0 b0 u0 t0 k hk s hs
      (fun y => if y.1 ∈ E then F y else 0) (hF.ite (hE.preimage measurable_fst) measurable_const)
    simp only [Option.elim, lintegral_smul_measure]
    apply congrArg (fun z : ℝ≥0∞ => (CompletePublicTable.idArrayMeasure p {id})⁻¹ * z)
    have hsection := (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection id).preimage
      (measurable_calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega))
    rw [← lintegral_indicator hsection, ← lintegral_indicator hsection]
    have hID (wv : Sample × Vector) :
        (calendarCurrentSource rate rewards C_star C_h control0 b0 u0 t0 (k + 1) (by omega) wv).1.1 =
        (joint s k hk wv).1.1.1.1.1 :=
      congrArg (fun y : History rate s q × (Estimate p × Option (LogicalCell p rate)) => y.1.1.1.1.1)
        (calendarSourceJoint_step rate rewards C_star C_h control0 b0 u0 t0 s k hk hs wv)
    convert h using 1
    · apply lintegral_congr
      intro wv
      rw [retainedSourceTest_history_indicator]
      simp only [Set.indicator_apply, E, Set.mem_preimage, ReferenceFixedIDSourceSection.fixedIDSourceSection,
        Set.mem_ofPred_eq]
      simp only [hID wv]
      by_cases hid : (joint s k hk wv).1.1.1.1.1 = id <;> simp only [hid, ite_true, ite_false]
    · apply lintegral_congr
      intro wv
      rw [retainedKernelTest_history_indicator]
      simp only [Set.indicator_apply, E, Set.mem_preimage, ReferenceFixedIDSourceSection.fixedIDSourceSection,
        Set.mem_ofPred_eq]
      simp only [hID wv]
      by_cases hid : (joint s k hk wv).1.1.1.1.1 = id <;> simp only [hid, ite_true, ite_false]

end Bandits.Support.ReferenceGeneratedCalendarEpisodeLaterTransition
