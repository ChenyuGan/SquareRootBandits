/-
Copyright (c) 2026 Bandits formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarBeforeFirstTransitionAssembly
public import Bandits.Support.ReferenceGeneratedCalendarEpisodeLaterTransition

/-!
# Entire retained terminal transition test

Sources: ZIP4 `04_slow_fast_learner.tex:151-174,176-215,329-390` and
`06_interruptions.tex:391-426`.

The original exhaustive terminal experiment is partitioned before its first
call, at its ROOT, and after its ROOT. The accepted branch identities are
combined with their original unnormalized masses, for the raw law and every
original fixed ID. Initially stopped suffixes contribute zero because their
incoming numerical state has already overflowed. Physical play is preserved.
The common kernel retains the same history and actual incoming slow set.
This is an internal transition identity, not a manuscript closure claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceGeneratedCalendarEpisodeSlowLaw
open ReferenceGeneratedCalendarEpisodeHistoryTransport
open ReferenceGeneratedCalendarEpisodeTransitionCore
open ReferenceGeneratedCalendarEpisodePrefixRecombination
open ReferenceFirstCollectionLogicalPrefixExtension

namespace Bandits.Support.ReferenceGeneratedCalendarEpisodeTerminalTransition

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) :=
  Subtype.instMeasurableSpace

attribute [local instance] ReferenceRankInstallationPostUpdateProposalLaw.listMeasurableSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.sumMeasurableSingleton

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Omega" => ReferenceExhaustiveGeneratedCalendarSourceLaw.Omega rate rewards C_star C_h
local notation "Component" => ReferenceExhaustiveGeneratedCalendarSourceLaw.Component p
local notation "Payload" => ReferenceExhaustiveGeneratedCalendarSourceLaw.Payload rate rewards C_star C_h
local notation "Lambda" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw
  rate rewards C_star C_h control0
local notation "fixedLambda" => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
  rate rewards C_star C_h control0
local notation "componentLaw" => ReferenceExhaustiveGeneratedCalendarSourceLaw.componentLaw
  rate rewards C_star C_h control0
local notation "fixedComponentLaw" => ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDComponentLaw
  rate rewards C_star C_h control0

private theorem measurable_sigma_mk {I : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] (i : I) : Measurable (Sigma.mk i : B i → Sigma B) :=
  measurable_iff_le_map.mpr (iInf_le _ i)

/-- Pull an actual terminal almost-everywhere fact to its original component.
The fixed-ID case uses the original fixed-ID component itself. -/
private theorem component_ae (ids : Option (CompletePublicTable.IDArray p))
    {P : Omega → Prop} (hP : ∀ᵐ w ∂ids.elim Lambda fixedLambda, P w)
    (i : Component) :
    ∀ᵐ w ∂ids.elim (componentLaw i) (fun id => fixedComponentLaw id i), P ⟨i, w⟩ := by
  cases ids with
  | none =>
    exact ae_of_ae_map (measurable_sigma_mk i).aemeasurable
      ((Measure.ae_sum_iff.mp hP) i)
  | some id =>
    exact ae_of_ae_map (measurable_sigma_mk i).aemeasurable
      ((Measure.ae_sum_iff.mp hP) i)

/-- Disintegrate only the existing finite sigma sum, retaining every mass. -/
private theorem terminal_components (ids : Option (CompletePublicTable.IDArray p))
    (G : Omega → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ w, G w ∂ids.elim Lambda fixedLambda) =
      ∑' i : Component,
        ∫⁻ w, G ⟨i, w⟩
          ∂ids.elim (componentLaw i) (fun id => fixedComponentLaw id i) := by
  cases ids with
  | none =>
    rw [Option.elim_none, ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw,
      lintegral_sum_measure]
    apply tsum_congr
    intro i
    exact lintegral_map hG (measurable_sigma_mk i)
  | some id =>
    rw [Option.elim_some, ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw,
      lintegral_sum_measure]
    apply tsum_congr
    intro i
    exact lintegral_map hG (measurable_sigma_mk i)

omit control0 in
/-- The strict-past boundary `q.succ` excludes a call at `q` itself. -/
private theorem noCallBefore_on_firstCell (u t q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t) :
    NoCallBefore rate rewards C_star C_h q.succ z ↔ q.val < t.val := by
  have hboundary := ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell
    rate rewards C_star C_h u t z hz
  rw [← hboundary, ReferenceFirstCollectionPrecallCalendarSupport.before_cut_iff_no_call_through]
  constructor
  · intro h v hv
    exact (noCallAt_iff_callAt_none rate rewards C_star C_h v z).mp
      (h v (by simp only [Fin.val_succ]; omega))
  · intro h v hv
    exact (noCallAt_iff_callAt_none rate rewards C_star C_h v z).mpr
      (h v (by simp only [Fin.val_succ] at hv; omega))

omit control0 in
private theorem generated_beforeFirstCall (b : Bool) (u t q : Fin p.T)
    (w : Payload (.generated b u t)) :
    (⟨.generated b u t, w⟩ : Omega) ∈ beforeFirstCall rate rewards C_star C_h q.succ ↔
      q.val < t.val := by
  let z := ReferenceExhaustiveGeneratedCalendarSourceLaw.originalSource
    rate rewards C_star C_h ⟨.generated b u t, w⟩
  have hz : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t := by
    cases b with
    | false =>
      exact (ReferenceFirstLiveCollectionPathJoin.firstLiveCollectionEvent_facts
        rate rewards C_star C_h u t _
          (ReferenceGeneratedRankCalendarFoundation.calendarOriginalLift
            rate rewards C_star C_h false u t _ w).1.1.property).1
    | true =>
      exact (ReferenceGeneratedRankCalendarFoundation.calendarOriginalLift
        rate rewards C_star C_h true u t _ w).1.1.property.1
  exact noCallBefore_on_firstCell rate rewards C_star C_h u t q z hz

/-- At and after an initially stopped call, every present physical cell has
an overflowed incoming state. The retained gate therefore contributes zero;
this does not remove that physical suffix from the experiment. -/
private theorem ae_stopped_retained_tests_zero
    (ids : Option (CompletePublicTable.IDArray p)) (u t s q : Fin p.T)
    (htq : t.val ≤ q.val) :
    ∀ᵐ w ∂ids.elim (componentLaw (.stopped u t))
      (fun id => fixedComponentLaw id (.stopped u t)),
      ∀ F : TransitionData rate s q → ℝ≥0∞,
        retainedSourceTest rate rewards C_star C_h s q F
          (terminalSourceJoint rate rewards C_star C_h control0 s q ⟨.stopped u t, w⟩) = 0 ∧
        retainedKernelTest rate rewards C_star C_h s q F
          (terminalSourceJoint rate rewards C_star C_h control0 s q ⟨.stopped u t, w⟩) = 0 := by
  filter_upwards
    [component_ae rate rewards C_star C_h control0 ids
      (ae_retainedSourceTest rate rewards C_star C_h control0 ids) (.stopped u t),
     component_ae rate rewards C_star C_h control0 ids
      (ae_retainedEvent_currentMark rate rewards C_star C_h control0 ids) (.stopped u t)]
    with w htest hret
  have hzero (G : TransitionData rate s q → ℝ≥0∞) :
      retainedSourceTest rate rewards C_star C_h s q G
        (terminalSourceJoint rate rewards C_star C_h control0 s q ⟨.stopped u t, w⟩) = 0 := by
    rw [htest s q G]
    by_cases hg : (⟨.stopped u t, w⟩ : Omega) ∈
        episodeStartEvent rate rewards C_star C_h control0 s ∧
      (⟨.stopped u t, w⟩ : Omega) ∈ retainedEvent rate rewards C_star C_h control0 s q
    · rw [ite_eq_left hg]
      cases he : currentMark rate rewards C_star C_h control0 q ⟨.stopped u t, w⟩ with
      | none => simp only [optionalTransitionTest, terminalSourceJoint, he]
      | some e =>
        obtain ⟨hm, htime⟩ := (currentMark_eq_some_iff rate rewards C_star C_h control0
          q ⟨.stopped u t, w⟩ e).mp he
        have hte : t.val ≤ e.time.val := by rw [htime]; exact htq
        have heq := (ReferenceInitialStoppedCalendar.initialStoppedPast_suffix_fields
          rate rewards C_star C_h control0 u t (Fin.last p.T) w e hm hte).2
        have hstop : e.before.overflow = true := by
          rw [heq]
          exact ReferenceInitialStoppedCalendar.suffixBefore_stopped
            rate rewards C_star C_h u t e.time hte w.1
        have hclear := ((hret s q e he).mp hg.2).2.2
        rw [hclear] at hstop
        cases hstop
    · exact ite_eq_right hg
  intro F
  exact ⟨hzero F, hzero (kernelLiftTest rate rewards C_star C_h s q F)⟩

/-- Entire retained source/common-kernel joint-test equality in the original
terminal experiment, raw and under every original fixed-ID law. The common
kernel uses the SAME actual history and old slow set. All start, retention,
seed, PRE, rate, reward, proposal and residual joins are supplied internally
by the accepted branch producers; no incoming slow-set law is assumed. -/
theorem terminal_retained_transition_test
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, retainedSourceTest rate rewards C_star C_h s q F
        (terminalSourceJoint rate rewards C_star C_h control0 s q w)
      ∂ids.elim Lambda fixedLambda) =
    ∫⁻ w, retainedKernelTest rate rewards C_star C_h s q F
        (terminalSourceJoint rate rewards C_star C_h control0 s q w)
      ∂ids.elim Lambda fixedLambda := by
  let S : Omega → ℝ≥0∞ := fun w => retainedSourceTest rate rewards C_star C_h s q F
    (terminalSourceJoint rate rewards C_star C_h control0 s q w)
  let K : Omega → ℝ≥0∞ := fun w => retainedKernelTest rate rewards C_star C_h s q F
    (terminalSourceJoint rate rewards C_star C_h control0 s q w)
  let E := beforeFirstCall rate rewards C_star C_h q.succ
  have hE : MeasurableSet E := measurableSet_beforeFirstCall rate rewards C_star C_h control0 q.succ
  have hS : Measurable S :=
    (measurable_retainedSourceTest rate rewards C_star C_h control0 s q F hF).comp
      (measurable_terminalSourceJoint rate rewards C_star C_h control0 s q)
  have hK : Measurable K :=
    (measurable_retainedKernelTest rate rewards C_star C_h control0 s q F hF).comp
      (measurable_terminalSourceJoint rate rewards C_star C_h control0 s q)
  have hafter :
      (∫⁻ w, if w ∈ E then 0 else S w ∂ids.elim Lambda fixedLambda) =
      ∫⁻ w, if w ∈ E then 0 else K w ∂ids.elim Lambda fixedLambda := by
    have hSa : Measurable (fun w => if w ∈ E then (0 : ℝ≥0∞) else S w) :=
      measurable_const.ite hE hS
    have hKa : Measurable (fun w => if w ∈ E then (0 : ℝ≥0∞) else K w) :=
      measurable_const.ite hE hK
    rw [terminal_components rate rewards C_star C_h control0 ids _ hSa,
      terminal_components rate rewards C_star C_h control0 ids _ hKa]
    apply tsum_congr
    intro i
    cases i with
    | noCall =>
      apply lintegral_congr
      intro w
      have hn : (⟨.noCall, w⟩ : Omega) ∈ E := by
        intro v _
        exact (ReferenceExhaustiveGeneratedCalendarSourceLaw.noCallBefore_terminal_iff
          rate rewards C_star C_h w.1.val).mpr w.1.property v v.isLt
      simp only [hn, ite_true]
    | stopped u t =>
      by_cases hqt : q.val < t.val
      · apply lintegral_congr
        intro w
        have hn : (⟨.stopped u t, w⟩ : Omega) ∈ E := by
          intro v hv
          exact ReferenceInitialStoppedCalendar.initialStoppedEvent_noCallBefore
            rate rewards C_star C_h u t w.1.val w.1.property v
              (by simp only [Fin.val_succ] at hv; simp only [Fin.val_castSucc]; omega)
        simp only [hn, ite_true]
      · apply lintegral_congr_ae
        filter_upwards [ae_stopped_retained_tests_zero rate rewards C_star C_h control0
          ids u t s q (Nat.le_of_not_gt hqt)] with w hw
        obtain ⟨hs, hk⟩ := hw F
        dsimp only [S, K]
        rw [hs, hk]
    | generated b u t =>
      by_cases hqt : q.val < t.val
      · apply lintegral_congr
        intro w
        have hn := (generated_beforeFirstCall rate rewards C_star C_h b u t q w).mpr hqt
        simp only [E, hn, ite_true]
      · have hn (w : Payload (.generated b u t)) :
            (⟨.generated b u t, w⟩ : Omega) ∉ E :=
          fun h => hqt ((generated_beforeFirstCall rate rewards C_star C_h b u t q w).mp h)
        simp_rw [ite_eq_right (hn _)]
        by_cases hdate : q = t
        · subst q
          exact generated_component_root_retained_transition_test
            rate rewards C_star C_h control0 b u t ids s hsq F hF
        · have htq : t.val < q.val := by
            have hne : q.val ≠ t.val := fun h => hdate (Fin.ext h)
            omega
          obtain ⟨k, hk⟩ : ∃ k : ℕ, t.val + 1 + k = q.val :=
            ⟨q.val - t.val - 1, by omega⟩
          have hkT : t.val + 1 + k < p.T := by omega
          have htime : (⟨t.val + 1 + k, hkT⟩ : Fin p.T) = q := Fin.ext hk
          cases htime
          exact ReferenceGeneratedCalendarEpisodeLaterTransition.generated_component_later_retained_transition_test
            rate rewards C_star C_h control0 b u t k hkT ids s hsq F hF
  have hbefore :=
    ReferenceGeneratedCalendarBeforeFirstTransitionAssembly.terminal_beforeFirstCall_retained_transition_test
      rate rewards C_star C_h control0 ids s q hsq F hF
  have hsplit (G : Omega → ℝ≥0∞) :
      G = (fun w => if w ∈ E then G w else 0) +
        (fun w => if w ∈ E then 0 else G w) := by
    funext w
    by_cases hw : w ∈ E <;>
      simp only [Pi.add_apply, hw, ite_true, ite_false, zero_add, add_zero]
  change (∫⁻ w, S w ∂ids.elim Lambda fixedLambda) =
    ∫⁻ w, K w ∂ids.elim Lambda fixedLambda
  rw [hsplit S, hsplit K]
  simp only [Pi.add_apply]
  have hSb : Measurable (fun w => if w ∈ E then S w else 0) :=
    hS.ite hE measurable_const
  have hKb : Measurable (fun w => if w ∈ E then K w else 0) :=
    hK.ite hE measurable_const
  rw [lintegral_add_left hSb, lintegral_add_left hKb]
  exact congrArg₂ (· + ·) hbefore hafter

end Bandits.Support.ReferenceGeneratedCalendarEpisodeTerminalTransition
