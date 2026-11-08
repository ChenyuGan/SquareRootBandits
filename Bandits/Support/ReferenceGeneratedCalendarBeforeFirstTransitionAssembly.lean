/-
Copyright (c) 2026 Bandits formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarErasedCollectionTransition
public import Bandits.Support.ReferenceGeneratedCalendarFirstLiveEpisodeTransition

/-!
# Before-first-call terminal transition assembly

Sources: ZIP4 `04_slow_fast_learner.tex:329-390` and
`06_interruptions.tex:391-426`.

The first-LIVE and first-COLLECTION identities are combined on the original
erased prefix measure. Outside both physical domains, the strict past has no
current mark, so both retained tests vanish. The terminal transports then
give the original joint-test identity, raw and at every original fixed ID.
All component masses and the current no-call gate are retained. This is an
internal transition identity, not a manuscript or main-regret closure claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation (LogicalCell SlowSet)
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceGeneratedCalendarEpisodeHistoryTransport
open ReferenceGeneratedCalendarEpisodeSlowLaw (Estimate)
open ReferenceGeneratedCalendarEpisodeTransitionCore
open ReferenceGeneratedCalendarPrefixProposalErasure
open ReferenceGeneratedCalendarEpisodePrefixRecombination
open ReferenceFirstCollectionLogicalPrefixExtension
open ReferenceFirstLiveCalendarMarkedTransition
open ReferenceGeneratedCalendarErasedCollectionTransition

namespace Bandits.Support.ReferenceGeneratedCalendarBeforeFirstTransitionAssembly

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

local notation "Obs" => ReferenceFirstLiveCalendarMarkedTransition.Observation p rate
local notation "Scalar" => ContinuousControlSlice.Scalar
local notation "scalarLaw" => ContinuousControlSlice.scalarLaw
local notation "Innovation" => ContinuousLearningRows.TimeControl p × Scalar
local notation "Lambda" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw
  rate rewards C_star C_h control0

include control0 in
/-- Off both actual physical domains, the prefix operation preserves the
strict past. This includes absent, future, stopped and failed-launch sources;
no numerical state or incoming-set presence is assumed. -/
private theorem prefixCurrentMark_absent (q : Fin p.T) (o : Obs)
    (hpast : ∀ e ∈ o.2.2, e.time.val < q.val)
    (hg : currentCellGate rate rewards C_star C_h q o.1 ≠ true)
    (hd : o.1 ∉ ReferenceFirstCollectionOneRoundLogicalCell.actualDomain
      (rate := rate) rewards C_star C_h q)
    (x : Scalar) (ux : Innovation) :
    prefixCurrentMark rate rewards C_star C_h q (refillProposal q (o, x), ux) = none := by
  let z := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q o.1 ux.1
  let a := roundAuxiliary q ((refillProposal q (o, x)).2.1, ux.2)
  have hgz : currentCellGate rate rewards C_star C_h q z ≠ true := by
    rw [currentCellGate_replace_current rate rewards C_star C_h control0]
    exact hg
  have hdz : z ∉ ReferenceFirstCollectionOneRoundLogicalCell.actualDomain
      (rate := rate) rewards C_star C_h q := by
    intro hz
    apply hd
    apply (ReferenceFirstCollectionOneRoundLogicalCell.actualDomain_iff_oldSelector
      rewards C_star C_h q o.1).mpr
    exact (ReferenceFirstCollectionOldSelectorRecordingLaw.oldSelector_replaceCurrent
      rate rewards C_star C_h control0 q o.1 ux.1).mp
        ((ReferenceFirstCollectionOneRoundLogicalCell.actualDomain_iff_oldSelector
          rewards C_star C_h q z).mp hz)
  have htag := currentCellTag_absent rate rewards C_star C_h q z hgz a
  have hcell (U : SlowSet p) :
      collectionCellAt rate rewards C_star C_h q U (z, a) = none := by
    unfold collectionCellAt ReferenceFirstCollectionOneRoundLogicalCell.sourceCell?
    rw [dite_eq_right hdz]
  have hfind : o.2.2.find? (fun e => e.time == q) = none := by
    apply List.find?_eq_none.mpr
    intro e he h
    exact (hpast e he).ne (congrArg Fin.val (beq_iff_eq.mp h))
  change ((extendedPrefixStep rate rewards C_star C_h q (z, a)
    (incomingFromList rate o.2.2, o.2.2)).2.find? (fun e => e.time == q)) = none
  unfold extendedPrefixStep prefixStep prefixCandidate
  rw [htag]
  dsimp only
  cases hi : incomingFromList rate o.2.2 with
  | none => exact hfind
  | some U =>
    dsimp only
    rw [hcell]
    exact hfind

/-- Exhaust the original erased observer without normalizing any branch.
The current no-call condition is inside both complete innovation integrals.
The first-LIVE input includes birth and both positive-offset phases, and the
first-COLLECTION input includes its disabled and absent-retention cases. -/
theorem beforePrefix_retained_transition_test
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ o, ∫⁻ x, ∫⁻ ux, if noCallAt rate rewards C_star C_h q o.1 then
      retainedSourceTest rate rewards C_star C_h s q F
        (prefixSourceJoint rate rewards C_star C_h control0 s q (refillProposal q (o, x), ux))
      else 0 ∂calendarInnovationLaw p ∂scalarLaw
      ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
        (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
          (eraseProposal q)) =
    ∫⁻ o, ∫⁻ x, ∫⁻ ux, if noCallAt rate rewards C_star C_h q o.1 then
      retainedKernelTest rate rewards C_star C_h s q F
        (prefixSourceJoint rate rewards C_star C_h control0 s q (refillProposal q (o, x), ux))
      else 0 ∂calendarInnovationLaw p ∂scalarLaw
      ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
        (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
          (eraseProposal q) := by
  let μ := (ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
    (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
      (eraseProposal q)
  let L : Set Obs := {o | currentCellGate rate rewards C_star C_h q o.1 = true}
  let S : Obs → ℝ≥0∞ := fun o => ∫⁻ x, ∫⁻ ux,
    if noCallAt rate rewards C_star C_h q o.1 then
      retainedSourceTest rate rewards C_star C_h s q F
        (prefixSourceJoint rate rewards C_star C_h control0 s q (refillProposal q (o, x), ux))
    else 0 ∂calendarInnovationLaw p ∂scalarLaw
  let K : Obs → ℝ≥0∞ := fun o => ∫⁻ x, ∫⁻ ux,
    if noCallAt rate rewards C_star C_h q o.1 then
      retainedKernelTest rate rewards C_star C_h s q F
        (prefixSourceJoint rate rewards C_star C_h control0 s q (refillProposal q (o, x), ux))
    else 0 ∂calendarInnovationLaw p ∂scalarLaw
  have hL : MeasurableSet L := measurableSet_eq_fun
    ((measurable_currentCellGate rate rewards C_star C_h q).comp measurable_fst)
    measurable_const
  have hrestrict (f : Obs → Scalar → Innovation → ℝ≥0∞) :
      (∫⁻ o in L, ∫⁻ x, ∫⁻ ux, f o x ux ∂calendarInnovationLaw p ∂scalarLaw ∂μ) =
      ∫⁻ o, ∫⁻ x, ∫⁻ ux, if o ∈ L then f o x ux else 0
        ∂calendarInnovationLaw p ∂scalarLaw ∂μ := by
    rw [← lintegral_indicator hL]
    apply lintegral_congr
    intro o
    by_cases ho : o ∈ L <;>
      simp only [Set.indicator_apply, ho, ite_true, ite_false, lintegral_zero]
  have hlive : (∫⁻ o in L, S o ∂μ) = ∫⁻ o in L, K o ∂μ := by
    dsimp only [S, K]
    rw [hrestrict, hrestrict]
    exact ReferenceGeneratedCalendarFirstLiveEpisodeTransition.beforePrefix_firstLive_retained_transition_test
      rate rewards C_star C_h control0 ids s q hsq F hF
  have hcompl : (∫⁻ o in Lᶜ, S o ∂μ) = ∫⁻ o in Lᶜ, K o ∂μ := by
    apply lintegral_congr_ae
    filter_upwards
      [(ae_erased_prefix_firstCollection_transition_test rate rewards C_star C_h control0
        ids s q hsq).filter_mono ae_restrict_le,
       (ae_erased_prefix_collection_incoming rate rewards C_star C_h control0
        ids q).filter_mono ae_restrict_le,
       ae_restrict_mem hL.compl] with o hc hp ho
    have hg : currentCellGate rate rewards C_star C_h q o.1 ≠ true := ho
    by_cases hd : o.1 ∈ ReferenceFirstCollectionOneRoundLogicalCell.actualDomain
        (rate := rate) rewards C_star C_h q
    · exact hc hd F
    · dsimp only [S, K]
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro ux
      have hm := prefixCurrentMark_absent rate rewards C_star C_h control0 q o hp.1 hg hd x ux
      simp only [retainedKernelTest, retainedSourceTest, prefixSourceJoint, hm,
        optionalTransitionTest, ite_self]
  exact (lintegral_add_compl S hL).symm.trans
    ((congrArg₂ (· + ·) hlive hcompl).trans (lintegral_add_compl K hL))

/-- The entire original before-first-call retained source/common-kernel
joint-test identity, raw and under every original fixed-ID terminal law.
The `q.succ` event excludes a ROOT at the current date. There is no incoming
slow-set law, boundedness, integrability, seed, PRE or coverage premise. -/
theorem terminal_beforeFirstCall_retained_transition_test
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, if w ∈ beforeFirstCall rate rewards C_star C_h q.succ then
      retainedSourceTest rate rewards C_star C_h s q F
        (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0
      ∂ids.elim Lambda
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
          rate rewards C_star C_h control0)) =
    ∫⁻ w, if w ∈ beforeFirstCall rate rewards C_star C_h q.succ then
      retainedKernelTest rate rewards C_star C_h s q F
        (terminalSourceJoint rate rewards C_star C_h control0 s q w) else 0
      ∂ids.elim Lambda
        (ReferenceExhaustiveGeneratedCalendarSourceLaw.fixedIDTerminalLaw
          rate rewards C_star C_h control0) := by
  rw [terminal_beforeFirstCall_source_erasure_test rate rewards C_star C_h control0
        ids s q hsq F hF,
    terminal_beforeFirstCall_kernel_erasure_test rate rewards C_star C_h control0
        ids s q hsq F hF]
  have hmeas
      (G : History rate s q × (Estimate p × Option (LogicalCell p rate)) → ℝ≥0∞)
      (hG : Measurable G) :
      Measurable (fun v : Obs × Scalar => ∫⁻ ux,
        if noCallAt rate rewards C_star C_h q v.1.1 then
          G (prefixSourceJoint rate rewards C_star C_h control0 s q
            (refillProposal q v, ux)) else 0 ∂calendarInnovationLaw p) := by
    have hJ : Measurable (fun v : (Obs × Scalar) × Innovation =>
        prefixSourceJoint rate rewards C_star C_h control0 s q
          (refillProposal q v.1, v.2)) :=
      (measurable_prefixSourceJoint rate rewards C_star C_h control0 s q).comp
        (((measurable_refillProposal q).comp measurable_fst).prodMk measurable_snd)
    have hno : MeasurableSet {v : (Obs × Scalar) × Innovation |
        noCallAt rate rewards C_star C_h q v.1.1.1} :=
      (measurableSet_noCallAt rate rewards C_star C_h control0 q).preimage
        measurable_fst.fst.fst
    exact ((hG.comp hJ).ite hno measurable_const).lintegral_prod_right'
  rw [lintegral_prod _ (hmeas _
      (measurable_retainedSourceTest rate rewards C_star C_h control0 s q F hF)).aemeasurable,
    lintegral_prod _ (hmeas _
      (measurable_retainedKernelTest rate rewards C_star C_h control0 s q F hF)).aemeasurable]
  exact beforePrefix_retained_transition_test rate rewards C_star C_h control0 ids s q hsq F hF

end Bandits.Support.ReferenceGeneratedCalendarBeforeFirstTransitionAssembly
