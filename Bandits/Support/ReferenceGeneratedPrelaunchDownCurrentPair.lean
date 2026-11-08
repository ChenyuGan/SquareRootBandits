/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownPastFactor

/-!
# Original-source prelaunch DOWN current-pair cylinders

Sources: `appendix_a_local_protocol.tex:111-138`,
`appendix_b_communication.tex:724-736`, `07_public_setup.tex:60-112,127-142`,
and `05_binary_transport.tex:20-42` in `sources/zip4/manuscript/`.

The predictable indicator is the complete existing prefix indicator. Current
positivity is separately the presence of the actual current prelaunch test.
Deleting one original DOWN pair preserves that positivity, but generally changes
the test's sample. All probabilities below use the full original source law,
including all rows and every original private coordinate and the selected J.
The named next consumer is the genuine prelaunch/mixed at-birth recurrence,
after actual historical-cohort and old/new chronology joins. Those producers,
launch-bank ancestry, stopped tails and publication-conditioned laws remain
separate. These are internal identities, with no manuscript closure assertion.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownCurrentPair

open MeasureTheory ConstructorDimensions BootstrapDimensions
open ReferenceGeneratedPrelaunchDownPrefix ReferencePrelaunchCarriedMeasurability
open ReferenceSelectedAffinePairLaw GeneratedBootstrapRoundLaw
open ReferencePrelaunchFollower
open scoped Classical ENNReal

variable {p : ConstructorDimensions.Parameters}

/-- Literal current positive-test event, separate from the predictable indicator. -/
def A_r (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T) : Prop :=
  (source_prelaunch_down_current_test rate rewards C_star C_h z i r).isSome = true

/-- Inverse deletion retains IDs, the entire private tuple, every forward bit,
entire continuous slices, all UP pairs, and whole entries at every other time.
The final conjunct also retains every other whole original row. -/
theorem pair_replacement_coordinates (j : Fin (M p)) (r : Fin p.T)
    (i : Fin (p.m - 1)) (v : Remainder p j r (0, i)) (a a0 : Pair p) :
    let z := (fixedPairSplit p j r (0, i)).symm (a, v)
    let z0 := (fixedPairSplit p j r (0, i)).symm (a0, v)
    z.1.1 = z0.1.1 ∧ z.2 = z0.2 ∧
      (∀ q, ReferencePrelaunchDownInvariance.DownCoordinateAgreement (z.1.2 q) (z0.1.2 q)) ∧
      (∀ q t, t ≠ r → (z.1.2 q).2 t = (z0.1.2 q).2 t) ∧
      (∀ q, q ≠ j → z.1.2 q = z0.1.2 q) := by
  dsimp only
  let z := (fixedPairSplit p j r (0, i)).symm (a, v)
  let z0 := (fixedPairSplit p j r (0, i)).symm (a0, v)
  have h := fixedPairSplit_inverse_coordinates p j r (0, i) a v
  have h0 := fixedPairSplit_inverse_coordinates p j r (0, i) a0 v
  change ((z.1.2 j).2 r).2 (0, i) = a ∧ _ at h
  change ((z0.1.2 j).2 r).2 (0, i) = a0 ∧ _ at h0
  have hother (q : Fin (M p)) (hq : q ≠ j) : z.1.2 q = z0.1.2 q :=
    (h.2.2.2.2.2.2.2 ⟨q, hq⟩).trans (h0.2.2.2.2.2.2.2 ⟨q, hq⟩).symm
  have htime (q : Fin (M p)) (t : Fin p.T) (ht : t ≠ r) :
      (z.1.2 q).2 t = (z0.1.2 q).2 t := by
    by_cases hq : q = j
    · subst q
      exact (h.2.2.2.2.2.2.1 ⟨t, ht⟩).trans (h0.2.2.2.2.2.2.1 ⟨t, ht⟩).symm
    · rw [hother q hq]
  refine ⟨h.2.1.trans h0.2.1.symm, h.2.2.1.trans h0.2.2.1.symm, ?_, htime, hother⟩
  intro q
  by_cases hq : q = j
  · subst q
    refine ⟨?_, ?_, ?_⟩
    · intro u t
      exact congrFun (congrFun (h.2.2.2.1.trans h0.2.2.2.1.symm) u) t
    · intro t
      by_cases ht : t = r
      · subst t
        exact h.2.2.2.2.1.trans h0.2.2.2.2.1.symm
      · exact congrArg Prod.fst (htime j t ht)
    · intro t f
      by_cases ht : t = r
      · subst t
        have hc : ((1 : Fin 2), f) ≠ (0, i) := by
          intro he
          have he' := congrArg (fun c : ContinuousLearningRows.Channel p => c.1) he
          norm_num at he'
        exact (h.2.2.2.2.2.1 ⟨(1, f), hc⟩).trans (h0.2.2.2.2.2.1 ⟨(1, f), hc⟩).symm
      · exact congrArg (fun e => e.2 (1, f)) (htime j t ht)
  · rw [hother q hq]
    exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

/-- IDs and G's complete public/private strict past agree under replacement.
The private component is the full PastView: all base block inputs and J, every
retained player scalar, and the complete coordinator target stream. -/
theorem same_ids_past_of_pair_replacement (j : Fin (M p)) (r : Fin p.T)
    (i : Fin (p.m - 1)) (v : Remainder p j r (0, i)) (a a0 : Pair p) :
    let z := (fixedPairSplit p j r (0, i)).symm (a, v)
    let z0 := (fixedPairSplit p j r (0, i)).symm (a0, v)
    z.1.1 = z0.1.1 ∧ past p r (sourceCoordinates z).2 = past p r (sourceCoordinates z0).2 := by
  dsimp only
  let z := (fixedPairSplit p j r (0, i)).symm (a, v)
  let z0 := (fixedPairSplit p j r (0, i)).symm (a0, v)
  obtain ⟨hids, hp, hrows, htime, _⟩ := pair_replacement_coordinates j r i v a a0
  have hJ : ActualInitializationPhysicalStep.selectedRowIndex p z =
      ActualInitializationPhysicalStep.selectedRowIndex p z0 :=
    congrArg (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      PrivateSourceStreams.coordinatorIndex p e.1.2) hp
  refine ⟨hids, Prod.ext ?_ ?_⟩
  · funext t
    change CompleteRowStoppingLaw.calendarizeRow p
      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) t.1 =
      CompleteRowStoppingLaw.calendarizeRow p
      (z0.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z0)) t.1
    rw [hJ]
    apply Prod.ext
    · funext u
      exact (hrows _).1 u t.1
    · exact htime _ t.1 (by
        have ht := t.2
        change t.1.val < r.val at ht
        intro he
        exact (Nat.ne_of_lt ht) (congrArg Fin.val he))
  · change (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p r z.2).1 =
      (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p r z0.2).1
    apply Prod.ext
    · exact congrArg (fun e => (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p r e).1.1) hp
    · apply Prod.ext
      · funext label
        exact congrArg (fun e =>
          (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p r e).1.2.1 label) hp
      · exact congrArg (fun e =>
          (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p r e).1.2.2) hp

/-- If the deleted original row is not J, the entire selected row is retained,
including its current DOWN sample. J itself is still the original private J. -/
theorem selected_row_eq_of_pair_replacement_off_J (j : Fin (M p)) (r : Fin p.T)
    (i : Fin (p.m - 1)) (v : Remainder p j r (0, i)) (a a0 : Pair p)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p
      ((fixedPairSplit p j r (0, i)).symm (a, v)) ≠ j) :
    (sourceCoordinates ((fixedPairSplit p j r (0, i)).symm (a, v))).2.1 =
      (sourceCoordinates ((fixedPairSplit p j r (0, i)).symm (a0, v))).2.1 := by
  obtain ⟨_, hp, _, _, hother⟩ := pair_replacement_coordinates j r i v a a0
  have hindex := congrArg (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
    PrivateSourceStreams.coordinatorIndex p e.1.2) hp
  change ActualInitializationPhysicalStep.selectedRowIndex p
      ((fixedPairSplit p j r (0, i)).symm (a, v)) =
    ActualInitializationPhysicalStep.selectedRowIndex p
      ((fixedPairSplit p j r (0, i)).symm (a0, v)) at hindex
  change ((fixedPairSplit p j r (0, i)).symm (a, v)).1.2 _ =
    ((fixedPairSplit p j r (0, i)).symm (a0, v)).1.2 _
  rw [← hindex]
  exact hother _ hJ

/-- Exact predictable-I invariance, with all birth/count/flag/endpoint guards. -/
theorem past_indicator_pair_invariant (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (alpha k ell : ℕ) (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (j : Fin (M p)) (r : Fin p.T) (v : Remainder p j r (0, i)) (a a0 : Pair p) :
    source_prelaunch_down_past_indicator rate rewards C_star C_h
      ((fixedPairSplit p j r (0, i)).symm (a, v)) i alpha k ell hAlpha r w ↔
    source_prelaunch_down_past_indicator rate rewards C_star C_h
      ((fixedPairSplit p j r (0, i)).symm (a0, v)) i alpha k ell hAlpha r w := by
  let z := (fixedPairSplit p j r (0, i)).symm (a, v)
  let z0 := (fixedPairSplit p j r (0, i)).symm (a0, v)
  obtain ⟨hi, hp⟩ := same_ids_past_of_pair_replacement j r i v a a0
  -- BF reconstructs the literal indicator for every completion. Use the same
  -- whole-row/private completion on both sides of the equal ID/past view.
  have h := ReferenceGeneratedPrelaunchDownPastFactor.indicatorFromPast_reconstruct
    rate rewards C_star C_h i r alpha k ell hAlpha w z.1.2 (sourceCoordinates z).2 z
  have h0 := ReferenceGeneratedPrelaunchDownPastFactor.indicatorFromPast_reconstruct
    rate rewards C_star C_h i r alpha k ell hAlpha w z.1.2 (sourceCoordinates z).2 z0
  have hview : (z.1.1, past p r (sourceCoordinates z).2) =
      (z0.1.1, past p r (sourceCoordinates z0).2) := Prod.ext hi hp
  rw [hview] at h
  exact h.symm.trans h0

theorem processed_remains (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r : Fin p.T)
    (hc : (ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p r).val).crossing = none) :
    (ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p r).val).completed < n_boot p := by
  have he := GeneratedBootstrapRoundLaw.processed_completed z.1.1 rewards C_star C_h
    rate.eta (roundBlockIndex p r) (sourceCoordinates z).2 hc
  change (ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
    (roundBlockIndex p r).val).completed = (roundBlockIndex p r).val at he
  rw [he]
  exact (roundBlockIndex p r).isLt

/-- Evaluate the actual test on its processed branch. The activation selector
and remaining-block proof are local comparison inputs, not source-root inputs. -/
theorem current_test_of_processed (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T)
    (hc : (ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p r).val).crossing = none) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let b := ReferenceInitializationRun.run x (roundBlockIndex p r).val
    source_prelaunch_down_current_test rate rewards C_star C_h z i r =
      match b.activation (ActualReferenceInitializationBlock.refFollower i) with
      | none => none
      | some activation => ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row activation r
          (ReferenceInitializationRun.ownEntry
            (ReferenceInitializationRun.physical x b (processed_remains rate rewards C_star C_h z r hc))
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) r) := by
  dsimp only
  cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl processed =>
    rcases processed with active | inactive
    · have hbd := active.val.1.property.2.2
      have ha := active.property.choose_spec.1
      have ha' : (ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
          (roundBlockIndex p r).val).activation (ActualReferenceInitializationBlock.refFollower i) =
          some active.val.2.1 :=
        (congrArg (fun b : ReferenceInitializationRun.Boundary p =>
          b.activation (ActualReferenceInitializationBlock.refFollower i)) hbd).symm.trans ha
      have hsub : (⟨active.val.1.val, active.val.1.property.1⟩ :
          {b : ReferenceInitializationRun.Boundary p // b.completed < n_boot p}) =
          ⟨ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
            (roundBlockIndex p r).val, processed_remains rate rewards C_star C_h z r hc⟩ :=
        Subtype.ext hbd
      have ho := congrArg (fun b : {b : ReferenceInitializationRun.Boundary p // b.completed < n_boot p} =>
        ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical (sourceReferenceInput rate rewards C_star C_h z) b.val b.property)
          (PublicDiscreteDraws.followerPlayer p.two_le_m (ActualReferenceInitializationBlock.refFollower i)) r) hsub
      simp only [source_prelaunch_down_current_test, hp, ha']
      exact congrArg (ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i
        (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 r) ho
    · have hbd := inactive.val.1.property.2.2
      have ha : (ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
          (roundBlockIndex p r).val).activation (ActualReferenceInitializationBlock.refFollower i) = none := by
        exact (congrArg (fun b : ReferenceInitializationRun.Boundary p =>
          b.activation (ActualReferenceInitializationBlock.refFollower i)) hbd).symm.trans
          inactive.property.choose_spec.1
      simp only [source_prelaunch_down_current_test, hp, ha]
  | inr stopped =>
    exact (stopped.property.1 ((congrArg
      (fun b : ReferenceInitializationRun.Boundary p => b.crossing) stopped.property.2.1).trans hc)).elim

/-- Stopped execution has no current prelaunch test. -/
theorem current_test_of_stopped (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T)
    (hc : (ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p r).val).crossing ≠ none) :
    source_prelaunch_down_current_test rate rewards C_star C_h z i r = none := by
  unfold source_prelaunch_down_current_test source_prelaunch_down_prefix
  simp only [sourceReferenceInput] at hc ⊢
  simp only [hc, ↓reduceDIte]

/-- Presence iff the actual processed, activated, DOWN-selected and strictly
positive own-feedback guards. No decode, failure or pending-length guard occurs. -/
theorem A_r_iff (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let b := ReferenceInitializationRun.run x (roundBlockIndex p r).val
    A_r rate rewards C_star C_h z i r ↔
      ∃ hc : b.crossing = none, ∃ activation : Activation p,
        b.activation (ActualReferenceInitializationBlock.refFollower i) = some activation ∧
        (ReferencePrelaunchFollower.downInput i x.row activation r
          (ReferenceInitializationRun.ownEntry
            (ReferenceInitializationRun.physical x b (processed_remains rate rewards C_star C_h z r hc))
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) r)).selected = true ∧
        0 < (ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical x b (processed_remains rate rewards C_star C_h z r hc))
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) r).2.val.val := by
  dsimp only
  by_cases hc : (ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p r).val).crossing = none
  · rw [A_r, current_test_of_processed rate rewards C_star C_h z i r hc]
    cases ha : (ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
        (roundBlockIndex p r).val).activation (ActualReferenceInitializationBlock.refFollower i) with
    | none => simp only [Option.isSome_none, Bool.false_eq_true, reduceCtorEq, false_and, exists_false]
    | some activation =>
      simp only [ReferenceGeneratedPrelaunchDownCohort.prelaunchTest]
      split_ifs with h
      · simp only [Option.isSome_some, Option.some.injEq, true_iff]
        exact ⟨hc, activation, rfl, h⟩
      · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
        rintro ⟨_, a, ha', hs, hy⟩
        have he := Option.some.inj ha'
        subst a
        exact h ⟨hs, hy⟩
  · rw [A_r, current_test_of_stopped rate rewards C_star C_h z i r hc]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨hc', _⟩
    exact hc hc'

/-- Expanded physical guards: source round r.val+1 is processed, the actual
activation has taken effect, the retained slot/follower coordinates select this
DOWN channel, and its own rounded physical feedback is strictly positive. -/
theorem A_r_iff_physical_guards (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let b := ReferenceInitializationRun.run x (roundBlockIndex p r).val
    A_r rate rewards C_star C_h z i r ↔
      ∃ hc : b.crossing = none, ∃ activation : Activation p,
        b.activation (ActualReferenceInitializationBlock.refFollower i) = some activation ∧
        activation.val ≤ r.val + 1 ∧
        PublicDiscreteDraws.slotDraw (x.row.2 r).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 r).1 = i ∧
        0 < (ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical x b (processed_remains rate rewards C_star C_h z r hc))
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) r).2.val.val := by
  dsimp only
  constructor
  · intro hA
    obtain ⟨hc, activation, ha, hs, hy⟩ := (A_r_iff rate rewards C_star C_h z i r).mp hA
    have hsel := of_decide_eq_true hs
    exact ⟨hc, activation, ha, hsel.1, hsel.2.1, hsel.2.2, hy⟩
  · rintro ⟨hc, activation, ha, ht, hs, hf, hy⟩
    apply (A_r_iff rate rewards C_star C_h z i r).mpr
    exact ⟨hc, activation, ha, decide_eq_true ⟨ht, hs, hf⟩, hy⟩

/-- A finite code for the actual current physical action/grid feedback and the
retained continuous slot/follower selectors, at a fixed existing boundary. -/
abbrev CurrentCode (p : ConstructorDimensions.Parameters) :=
  (Fin p.K × Fin (D p + 1)) × PublicDiscreteDraws.Slot × Fin (p.m - 1)

def fixedCurrentCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p) (hb : b.completed < n_boot p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    CurrentCode p :=
  let x := sourceReferenceInput rate rewards C_star C_h z
  let own := ReferenceInitializationRun.ownEntry (ReferenceInitializationRun.physical x b hb)
    (PublicDiscreteDraws.followerPlayer p.two_le_m (ActualReferenceInitializationBlock.refFollower i)) r
  ((own.1, ReferenceInitializationMeasurability.observationGridIndex p own.2),
    PublicDiscreteDraws.slotDraw (x.row.2 r).1,
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 r).1)

theorem measurable_fixedCurrentCode (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p) (hb : b.completed < n_boot p)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    Measurable (fixedCurrentCode rate rewards C_star C_h b hb i r) := by
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m (ActualReferenceInitializationBlock.refFollower i)
  have ha := (ReferenceInitializationMeasurability.measurable_physicalAction_at_fixedBoundary
    p C_star C_h rate.eta rewards b hb r player).comp measurable_sourceCoordinates
  have hy := ((measurable_pi_apply player).comp ((measurable_pi_apply r).comp
    (ReferenceInitializationMeasurability.measurable_physicalObservationIndex_at_fixedBoundary
      p C_star C_h rate.eta rewards b hb))).comp measurable_sourceCoordinates
  have hs : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ((sourceCoordinates z).2.1.2 r).1) :=
    measurable_fst.comp ((measurable_pi_apply r).comp
      (measurable_snd.comp (measurable_fst.comp (measurable_snd.comp measurable_sourceCoordinates))))
  unfold fixedCurrentCode
  apply Measurable.prodMk
  · apply Measurable.prodMk
    · simpa only [Function.comp_def, sourceCoordinates_referenceInput, sourceReferenceInput, player,
        ReferenceInitializationRun.ownEntry] using ha
    · simpa only [ReferenceInitializationRun.ownEntry,
        ReferenceInitializationMeasurability.observationGridIndex_ownObservation,
        Function.comp_def, sourceCoordinates_referenceInput, sourceReferenceInput, player] using hy
  · apply Measurable.prodMk
    · exact PublicDiscreteDraws.measurable_slotDraw.comp hs
    · exact (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp hs

/-- The exact positive-test guard on the finite current code. -/
def positiveFromCode (b : ReferenceInitializationRun.Boundary p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (code : CurrentCode p) : Bool :=
  decide (∃ activation : Activation p,
    b.activation (ActualReferenceInitializationBlock.refFollower i) = some activation ∧
    activation.val ≤ r.val + 1 ∧ code.2.1 = PublicDiscreteDraws.downSlot ∧
    code.2.2 = i ∧ 0 < (code.1.2.val : ℝ) / (D p : ℝ))

private theorem A_r_iff_code (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T)
    (hc : (ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p r).val).crossing = none) :
    A_r rate rewards C_star C_h z i r ↔
      positiveFromCode (ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
        (roundBlockIndex p r).val) i r
        (fixedCurrentCode rate rewards C_star C_h _
          (processed_remains rate rewards C_star C_h z r hc) i r z) = true := by
  have he := A_r_iff rate rewards C_star C_h z i r
  dsimp only at he
  constructor
  · intro hA
    obtain ⟨_, activation, ha, hs, hy⟩ := he.mp hA
    apply decide_eq_true
    have hs' := of_decide_eq_true hs
    refine ⟨activation, ha, hs'.1, hs'.2.1, hs'.2.2, ?_⟩
    simpa only [fixedCurrentCode,
      ← ReferenceInitializationMeasurability.observationGridIndex_value] using hy
  · intro hcode
    have hc' := of_decide_eq_true hcode
    obtain ⟨activation, ha, ht, hs, hf, hy⟩ := hc'
    apply he.mpr
    refine ⟨hc, activation, ha, ?_, ?_⟩
    · apply decide_eq_true
      exact ⟨ht, hs, hf⟩
    · simpa only [fixedCurrentCode,
        ← ReferenceInitializationMeasurability.observationGridIndex_value] using hy

/-- Borel current positivity is constructed from the actual run and its physical
fixed-boundary arm/grid maps; activation is taken from that same boundary. -/
theorem measurableSet_A_r (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    MeasurableSet {z | A_r rate rewards C_star C_h z i r} := by
  let boundary := fun z : BootstrapPrivateRoundStreams.SourceInput p =>
    ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r).val
  have hb : Measurable boundary :=
    (ReferenceInitializationMeasurability.measurable_run p C_star C_h rate.eta rewards
      (roundBlockIndex p r).val).comp measurable_sourceCoordinates
  let branch := fun (b : ReferenceInitializationRun.Boundary p)
      (z : BootstrapPrivateRoundStreams.SourceInput p) =>
    if b.crossing = none then
      if h : b.completed < n_boot p then
        positiveFromCode b i r (fixedCurrentCode rate rewards C_star C_h b h i r z)
      else false
    else false
  have hm (b : ReferenceInitializationRun.Boundary p) : Measurable (branch b) := by
    dsimp only [branch]
    split_ifs with hc h
    · exact (Measurable.of_discrete : Measurable (positiveFromCode b i r)).comp
        (measurable_fixedCurrentCode rate rewards C_star C_h b h i r)
    · exact measurable_const
    · exact measurable_const
  have hall : Measurable (fun z => branch (boundary z) z) :=
    (measurable_from_prod_countable_right
      (f := fun v : ReferenceInitializationRun.Boundary p × BootstrapPrivateRoundStreams.SourceInput p =>
        branch v.1 v.2) hm).comp (hb.prodMk measurable_id)
  have he (z : BootstrapPrivateRoundStreams.SourceInput p) :
      A_r rate rewards C_star C_h z i r ↔ branch (boundary z) z = true := by
    by_cases hc : (boundary z).crossing = none
    · have hr := processed_remains rate rewards C_star C_h z r hc
      change (boundary z).completed < n_boot p at hr
      simpa only [branch, hc, hr, ↓reduceIte, ↓reduceDIte] using
        A_r_iff_code rate rewards C_star C_h z i r hc
    · simp only [A_r, current_test_of_stopped rate rewards C_star C_h z i r hc,
        Option.isSome_none, Bool.false_eq_true, branch, hc, ↓reduceIte]
  convert hall (measurableSet_singleton true) using 1
  ext z
  exact he z

/-- Original IDs, fixed rewards/constants/rate, and the entire private tuple
identify the second input as the actual first input with only its row updated. -/
theorem source_input_pair_update (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (j : Fin (M p)) (r : Fin p.T) (i : Fin (p.m - 1))
    (v : Remainder p j r (0, i)) (a a0 : Pair p) :
    let x := sourceReferenceInput rate rewards C_star C_h ((fixedPairSplit p j r (0, i)).symm (a, v))
    let x0 := sourceReferenceInput rate rewards C_star C_h ((fixedPairSplit p j r (0, i)).symm (a0, v))
    x0 = {x with row := x0.row} := by
  obtain ⟨hi, hp, _⟩ := pair_replacement_coordinates j r i v a a0
  dsimp only [sourceReferenceInput, ActualReferenceInitializationBlock.referenceInput]
  rw [hi, hp]

private theorem ownEntry_update_row (x : ReferenceInitializationRun.Input p)
    (row0 : CompletePublicTable.CompleteRow p)
    (hrow : ReferencePrelaunchDownInvariance.DownCoordinateAgreement x.row row0)
    (b : ReferenceInitializationRun.Boundary p) (hb : b.completed < n_boot p)
    (player : Fin p.m) (r : Fin p.T) :
    ReferenceInitializationRun.ownEntry (ReferenceInitializationRun.physical x b hb) player r =
      ReferenceInitializationRun.ownEntry
        (ReferenceInitializationRun.physical {x with row := row0} b hb) player r := by
  apply Prod.ext
  · change BootstrapPhysicalBlock.actions _ (BootstrapPhysicalBlock.run _ r.val) r player = _
    rw [ReferencePrelaunchDownInvariance.physicalRun_eq x row0 hrow b hb r.val]
    exact congrFun (ReferencePrelaunchDownInvariance.physicalActions_eq x row0 hrow b hb _ r) player
  · apply Subtype.ext
    apply Subtype.ext
    change BootstrapPhysicalBlock.feedback _ (BootstrapPhysicalBlock.run _ r.val) r player = _
    rw [ReferencePrelaunchDownInvariance.physicalRun_eq x row0 hrow b hb r.val]
    exact ReferencePrelaunchDownInvariance.physicalFeedback_eq x row0 hrow b hb _ r player

/-- Current positivity is pair invariant. The proof computes the common run,
activation and own physical entry; no matching-history assumption is supplied. -/
theorem current_positive_pair_invariant (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (j : Fin (M p)) (r : Fin p.T)
    (v : Remainder p j r (0, i)) (a a0 : Pair p) :
    A_r rate rewards C_star C_h ((fixedPairSplit p j r (0, i)).symm (a, v)) i r ↔
      A_r rate rewards C_star C_h ((fixedPairSplit p j r (0, i)).symm (a0, v)) i r := by
  let z := (fixedPairSplit p j r (0, i)).symm (a, v)
  let z0 := (fixedPairSplit p j r (0, i)).symm (a0, v)
  let x := sourceReferenceInput rate rewards C_star C_h z
  let x0 := sourceReferenceInput rate rewards C_star C_h z0
  change A_r rate rewards C_star C_h z i r ↔ A_r rate rewards C_star C_h z0 i r
  obtain ⟨_, hp, hrows, _, _⟩ := pair_replacement_coordinates j r i v a a0
  have hJ : ActualInitializationPhysicalStep.selectedRowIndex p z =
      ActualInitializationPhysicalStep.selectedRowIndex p z0 :=
    congrArg (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      PrivateSourceStreams.coordinatorIndex p e.1.2) hp
  have hrow : ReferencePrelaunchDownInvariance.DownCoordinateAgreement x.row x0.row := by
    change ReferencePrelaunchDownInvariance.DownCoordinateAgreement
      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))
      (z0.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z0))
    rw [hJ]
    exact hrows _
  have hx : x0 = {x with row := x0.row} := source_input_pair_update rate rewards C_star C_h j r i v a a0
  have hrun : ReferenceInitializationRun.run x (roundBlockIndex p r).val =
      ReferenceInitializationRun.run x0 (roundBlockIndex p r).val := by
    rw [hx]
    exact ReferencePrelaunchDownInvariance.run_eq x x0.row hrow _
  by_cases hc : (ReferenceInitializationRun.run x (roundBlockIndex p r).val).crossing = none
  · have hc0 : (ReferenceInitializationRun.run x0 (roundBlockIndex p r).val).crossing = none := by
      rw [← hrun]; exact hc
    rw [A_r, A_r, current_test_of_processed rate rewards C_star C_h z i r hc,
      current_test_of_processed rate rewards C_star C_h z0 i r hc0]
    have hb := processed_remains rate rewards C_star C_h z r hc
    have hown := ownEntry_update_row x x0.row hrow
      (ReferenceInitializationRun.run x (roundBlockIndex p r).val) hb
      (PublicDiscreteDraws.followerPlayer p.two_le_m (ActualReferenceInitializationBlock.refFollower i)) r
    rw [← hx] at hown
    have hb0 := processed_remains rate rewards C_star C_h z0 r hc0
    have hsub : (⟨ReferenceInitializationRun.run x (roundBlockIndex p r).val, hb⟩ :
        {b : ReferenceInitializationRun.Boundary p // b.completed < n_boot p}) =
        ⟨ReferenceInitializationRun.run x0 (roundBlockIndex p r).val, hb0⟩ := Subtype.ext hrun
    have ho := congrArg (fun b : {b : ReferenceInitializationRun.Boundary p // b.completed < n_boot p} =>
      ReferenceInitializationRun.ownEntry (ReferenceInitializationRun.physical x0 b.val b.property)
        (PublicDiscreteDraws.followerPlayer p.two_le_m (ActualReferenceInitializationBlock.refFollower i)) r) hsub
    have hactual := hown.trans ho
    have hact := congrArg (fun b : ReferenceInitializationRun.Boundary p =>
      b.activation (ActualReferenceInitializationBlock.refFollower i)) hrun
    rw [hact, hactual]
    cases ha : (ReferenceInitializationRun.run x0 (roundBlockIndex p r).val).activation
        (ActualReferenceInitializationBlock.refFollower i) with
    | none => rfl
    | some activation =>
      let own := ReferenceInitializationRun.ownEntry
        (ReferenceInitializationRun.physical x0 (ReferenceInitializationRun.run x0 (roundBlockIndex p r).val) hb0)
        (PublicDiscreteDraws.followerPlayer p.two_le_m (ActualReferenceInitializationBlock.refFollower i)) r
      change (ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row activation r own).isSome = true ↔
        (ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x0.row activation r own).isSome = true
      have hs := ReferencePrelaunchDownInvariance.downSelected_eq i x.row x0.row hrow activation r own
      simp only [ReferenceGeneratedPrelaunchDownCohort.prelaunchTest, hs]
      split_ifs <;> rfl
  · have hc0 : (ReferenceInitializationRun.run x0 (roundBlockIndex p r).val).crossing ≠ none := by
      rw [← hrun]; exact hc
    simp only [A_r, current_test_of_stopped rate rewards C_star C_h z i r hc,
      current_test_of_stopped rate rewards C_star C_h z0 i r hc0]

/-- Inactive includes the stopped case: no activation selector means no test. -/
theorem not_A_r_of_inactive (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T)
    (ha : (ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p r).val).activation (ActualReferenceInitializationBlock.refFollower i) = none) :
    ¬ A_r rate rewards C_star C_h z i r := by
  intro hA
  obtain ⟨_, activation, ha', _⟩ := (A_r_iff rate rewards C_star C_h z i r).mp hA
  rw [ha] at ha'
  cases ha'

theorem not_A_r_of_stopped (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T)
    (hc : (ReferenceInitializationRun.run (sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p r).val).crossing ≠ none) :
    ¬ A_r rate rewards C_star C_h z i r := by
  intro hA
  exact hc ((A_r_iff rate rewards C_star C_h z i r).mp hA).choose

/-- On the actual selected-row stratum, positivity identifies the full executed
current test, including the true prelaunch wrong-word sentinel `sent = none`. -/
theorem current_test_eq_some_of_selected_positive
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T)
    (j : Fin (M p)) (hJ : ActualInitializationPhysicalStep.selectedRowIndex p z = j)
    (hA : A_r rate rewards C_star C_h z i r) :
    source_prelaunch_down_current_test rate rewards C_star C_h z i r =
      some {time := r, sample := ((z.1.2 j).2 r).2 (0, i), sent := none} := by
  obtain ⟨hc, activation, ha, hs, hy⟩ := (A_r_iff rate rewards C_star C_h z i r).mp hA
  rw [current_test_of_processed rate rewards C_star C_h z i r hc]
  rw [ha]
  simp only [ReferenceGeneratedPrelaunchDownCohort.prelaunchTest, hs, hy, and_self, ↓reduceIte]
  simp only [downInput, sourceReferenceInput, ActualReferenceInitializationBlock.referenceInput, hJ]

/-- The deleted pair is the sample only when its original row is J. No off-J
sample identity is asserted. -/
theorem pair_replacement_current_test (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (j : Fin (M p)) (r : Fin p.T)
    (v : Remainder p j r (0, i)) (a : Pair p)
    (hJ : ActualInitializationPhysicalStep.selectedRowIndex p
      ((fixedPairSplit p j r (0, i)).symm (a, v)) = j)
    (hA : A_r rate rewards C_star C_h ((fixedPairSplit p j r (0, i)).symm (a, v)) i r) :
    source_prelaunch_down_current_test rate rewards C_star C_h
      ((fixedPairSplit p j r (0, i)).symm (a, v)) i r =
      some {time := r, sample := a, sent := none} := by
  rw [current_test_eq_some_of_selected_positive rate rewards C_star C_h _ i r j hJ hA,
    (fixedPairSplit_inverse_coordinates p j r (0, i) a v).1]

/-- Every actual current positive test has the prelaunch wrong-word condition
for every fixed candidate. This uses its literal sent=none sentinel. -/
theorem current_test_wrong_word (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) (r : Fin p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hA : A_r rate rewards C_star C_h z i r) :
    ∃ test, source_prelaunch_down_current_test rate rewards C_star C_h z i r = some test ∧
      test.time = r ∧ test.sent ≠ some w := by
  let j := ActualInitializationPhysicalStep.selectedRowIndex p z
  refine ⟨⟨r, ((z.1.2 j).2 r).2 (0, i), none⟩,
    current_test_eq_some_of_selected_positive rate rewards C_star C_h z i r j rfl hA, rfl, ?_⟩
  intro he
  cases he

/-- A future birth boundary cannot contribute to the current predictable
indicator. No factorization of birthAt at that future boundary is asserted. -/
theorem past_indicator_false_of_lt (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (alpha k ell : ℕ) (hAlpha : alpha ≤ p.T) (r : Fin p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (h : r.val < alpha) :
    ¬ source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k ell hAlpha r w := by
  intro hI
  exact (Nat.not_le_of_lt h) hI.2.2.1

/-- The terminal-alpha indicator is false at every genuine current round.
Terminal birthAt itself remains an output predicate. -/
theorem past_indicator_false_at_terminal (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (k ell : ℕ) (r : Fin p.T) (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    ¬ source_prelaunch_down_past_indicator rate rewards C_star C_h z i p.T k ell (Nat.le_refl p.T) r w :=
  past_indicator_false_of_lt rate rewards C_star C_h z i p.T k ell (Nat.le_refl p.T) r w r.isLt

section RemainderFactors

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (i : Fin (p.m - 1)) (alpha k ell : ℕ) (hAlpha : alpha ≤ p.T)
  (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
  (j : Fin (M p)) (r : Fin p.T)

/-- Actual evaluation of the complete predictable indicator at any fixed pair. -/
def IFromRemainder (a0 : Pair p) (v : Remainder p j r (0, i)) : Prop :=
  source_prelaunch_down_past_indicator rate rewards C_star C_h
    ((fixedPairSplit p j r (0, i)).symm (a0, v)) i alpha k ell hAlpha r w

/-- Actual evaluation of current positivity at any fixed pair. -/
def AFromRemainder (a0 : Pair p) (v : Remainder p j r (0, i)) : Prop :=
  A_r rate rewards C_star C_h ((fixedPairSplit p j r (0, i)).symm (a0, v)) i r

theorem measurableSet_IFromRemainder (a0 : Pair p) :
    MeasurableSet {v | IFromRemainder rate rewards C_star C_h i alpha k ell hAlpha w j r a0 v} :=
  (ReferenceGeneratedPrelaunchDownPastFactor.measurableSet_source_prelaunch_down_past_indicator
    rate rewards C_star C_h i alpha k ell hAlpha r w).preimage
    ((fixedPairSplit p j r (0, i)).symm.measurable.comp (measurable_const.prodMk measurable_id))

theorem measurableSet_AFromRemainder (a0 : Pair p) :
    MeasurableSet {v | AFromRemainder rate rewards C_star C_h i j r a0 v} :=
  (measurableSet_A_r rate rewards C_star C_h i r).preimage
    ((fixedPairSplit p j r (0, i)).symm.measurable.comp (measurable_const.prodMk measurable_id))

theorem IFromRemainder_independent_of_pair (a0 a1 : Pair p) (v : Remainder p j r (0, i)) :
    IFromRemainder rate rewards C_star C_h i alpha k ell hAlpha w j r a0 v ↔
      IFromRemainder rate rewards C_star C_h i alpha k ell hAlpha w j r a1 v :=
  past_indicator_pair_invariant rate rewards C_star C_h i alpha k ell hAlpha w j r v a0 a1

theorem AFromRemainder_independent_of_pair (a0 a1 : Pair p) (v : Remainder p j r (0, i)) :
    AFromRemainder rate rewards C_star C_h i j r a0 v ↔
      AFromRemainder rate rewards C_star C_h i j r a1 v :=
  current_positive_pair_invariant rate rewards C_star C_h i j r v a0 a1

theorem IFromRemainder_reconstruct (a0 : Pair p) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    IFromRemainder rate rewards C_star C_h i alpha k ell hAlpha w j r a0
      (fixedPairSplit p j r (0, i) z).2 ↔
      source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k ell hAlpha r w := by
  have he := past_indicator_pair_invariant rate rewards C_star C_h i alpha k ell hAlpha w j r
    (fixedPairSplit p j r (0, i) z).2 (fixedPairSplit p j r (0, i) z).1 a0
  rw [fixedPairSplit_reconstruct] at he
  exact he.symm

theorem AFromRemainder_reconstruct (a0 : Pair p) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    AFromRemainder rate rewards C_star C_h i j r a0 (fixedPairSplit p j r (0, i) z).2 ↔
      A_r rate rewards C_star C_h z i r := by
  have he := current_positive_pair_invariant rate rewards C_star C_h i j r
    (fixedPairSplit p j r (0, i) z).2 (fixedPairSplit p j r (0, i) z).1 a0
  rw [fixedPairSplit_reconstruct] at he
  exact he.symm

end RemainderFactors

/-- The literal ID/full-private-past coordinate used in the cylinder. -/
def sourcePastView (r : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    CompletePublicTable.IDArray p × Past p r :=
  (z.1.1, past p r (sourceCoordinates z).2)

theorem measurable_sourcePastView (r : Fin p.T) : Measurable (sourcePastView r) :=
  (measurable_fst.comp measurable_fst).prodMk
    ((measurable_fst.comp (past_current_measurePreserving p r).measurable).comp
      (measurable_snd.comp measurable_sourceCoordinates))

/-- Both the original selected J stratum and the whole ID/past view factor
through the remainder, for every fixed completion pair. -/
theorem selected_past_remainder_reconstruct (i : Fin (p.m - 1))
    (j : Fin (M p)) (r : Fin p.T) (a0 : Pair p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let z0 := (fixedPairSplit p j r (0, i)).symm (a0, (fixedPairSplit p j r (0, i) z).2)
    ActualInitializationPhysicalStep.selectedRowIndex p z0 = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      sourcePastView r z0 = sourcePastView r z := by
  dsimp only
  have hc := pair_replacement_coordinates j r i (fixedPairSplit p j r (0, i) z).2
    (fixedPairSplit p j r (0, i) z).1 a0
  have hp := same_ids_past_of_pair_replacement j r i (fixedPairSplit p j r (0, i) z).2
    (fixedPairSplit p j r (0, i) z).1 a0
  rw [fixedPairSplit_reconstruct] at hc hp
  refine ⟨?_, Prod.ext hp.1.symm hp.2.symm⟩
  exact congrArg (fun e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
    PrivateSourceStreams.coordinatorIndex p e.1.2) hc.2.1.symm

section Cylinder

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (i : Fin (p.m - 1)) (alpha k ell : ℕ) (hAlpha : alpha ≤ p.T)
  (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
  (j : Fin (M p)) (r : Fin p.T)

/-- The actual measurable remainder cell. No assumed adaptedness, trace,
measurability or law input is part of this definition. -/
def remainderCell (a0 : Pair p) (Cell : Set (CompletePublicTable.IDArray p × Past p r)) :
    Set (Remainder p j r (0, i)) :=
  {v | ActualInitializationPhysicalStep.selectedRowIndex p
      ((fixedPairSplit p j r (0, i)).symm (a0, v)) = j ∧
    sourcePastView r ((fixedPairSplit p j r (0, i)).symm (a0, v)) ∈ Cell ∧
    IFromRemainder rate rewards C_star C_h i alpha k ell hAlpha w j r a0 v ∧
    AFromRemainder rate rewards C_star C_h i j r a0 v}

theorem measurableSet_remainderCell (a0 : Pair p)
    (Cell : Set (CompletePublicTable.IDArray p × Past p r)) (hCell : MeasurableSet Cell) :
    MeasurableSet (remainderCell rate rewards C_star C_h i alpha k ell hAlpha w j r a0 Cell) := by
  have hl : Measurable (fun v : Remainder p j r (0, i) =>
      (fixedPairSplit p j r (0, i)).symm (a0, v)) :=
    (fixedPairSplit p j r (0, i)).symm.measurable.comp (measurable_const.prodMk measurable_id)
  have hJ : Measurable (ActualInitializationPhysicalStep.selectedRowIndex p) :=
    BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p
  exact (measurableSet_eq_fun (hJ.comp hl) measurable_const).inter
    ((hCell.preimage ((measurable_sourcePastView r).comp hl)).inter
      ((measurableSet_IFromRemainder rate rewards C_star C_h i alpha k ell hAlpha w j r a0).inter
        (measurableSet_AFromRemainder rate rewards C_star C_h i j r a0)))

theorem remainderCell_reconstruct (a0 : Pair p)
    (Cell : Set (CompletePublicTable.IDArray p × Past p r))
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (fixedPairSplit p j r (0, i) z).2 ∈
        remainderCell rate rewards C_star C_h i alpha k ell hAlpha w j r a0 Cell ↔
      ActualInitializationPhysicalStep.selectedRowIndex p z = j ∧ sourcePastView r z ∈ Cell ∧
      source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k ell hAlpha r w ∧
      A_r rate rewards C_star C_h z i r := by
  have hview := selected_past_remainder_reconstruct i j r a0 z
  dsimp only at hview
  simp only [remainderCell, Set.mem_ofPred_eq, hview.1, hview.2,
    IFromRemainder_reconstruct, AFromRemainder_reconstruct]

/-- Exact original-source prelaunch DOWN cylinder on any measurable full
ID/private-past cell, preserving every literal guard of I and of current A.
Null cells require no division. -/
theorem source_prelaunch_down_pair_cylinder
    (Cell : Set (CompletePublicTable.IDArray p × Past p r)) (hCell : MeasurableSet Cell)
    (E : Set (Pair p)) (hE : MeasurableSet E) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ActualInitializationPhysicalStep.selectedRowIndex p z = j ∧
        (z.1.1, past p r (sourceCoordinates z).2) ∈ Cell ∧
        source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k ell hAlpha r w ∧
        A_r rate rewards C_star C_h z i r ∧ ((z.1.2 j).2 r).2 (0, i) ∈ E} =
      pairLaw p E * BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ActualInitializationPhysicalStep.selectedRowIndex p z = j ∧
          (z.1.1, past p r (sourceCoordinates z).2) ∈ Cell ∧
          source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k ell hAlpha r w ∧
          A_r rate rewards C_star C_h z i r} := by
  let a0 : Pair p := (fun _ => 0, 0)
  let S := remainderCell rate rewards C_star C_h i alpha k ell hAlpha w j r a0 Cell
  have hS : MeasurableSet S :=
    measurableSet_remainderCell rate rewards C_star C_h i alpha k ell hAlpha w j r a0 Cell hCell
  have hbase : {z | (fixedPairSplit p j r (0, i) z).2 ∈ S} =
      {z | ActualInitializationPhysicalStep.selectedRowIndex p z = j ∧
        (z.1.1, past p r (sourceCoordinates z).2) ∈ Cell ∧
        source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k ell hAlpha r w ∧
        A_r rate rewards C_star C_h z i r} := by
    ext z
    exact remainderCell_reconstruct rate rewards C_star C_h i alpha k ell hAlpha w j r a0 Cell z
  have hevent : {z | (fixedPairSplit p j r (0, i) z).1 ∈ E ∧
      (fixedPairSplit p j r (0, i) z).2 ∈ S} =
      {z | ActualInitializationPhysicalStep.selectedRowIndex p z = j ∧
        (z.1.1, past p r (sourceCoordinates z).2) ∈ Cell ∧
        source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k ell hAlpha r w ∧
        A_r rate rewards C_star C_h z i r ∧ ((z.1.2 j).2 r).2 (0, i) ∈ E} := by
    ext z
    have h := remainderCell_reconstruct rate rewards C_star C_h i alpha k ell hAlpha w j r a0 Cell z
    simp only [Set.mem_ofPred_eq, fixedPairSplit_pair]
    tauto
  have hsplit := fixedPairSplit_cylinder p j r (0, i) E S hE hS
  rw [hevent, ← fixedPairSplit_remainderLaw p j r (0, i) S hS, hbase] at hsplit
  exact hsplit

/-- Fresh affine equation probability on exactly the same original-source cell.
The sample is the actual current test on J=j and A, with sent=none. -/
theorem source_prelaunch_down_hash_half
    (Cell : Set (CompletePublicTable.IDArray p × Past p r)) (hCell : MeasurableSet Cell) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      {z | ActualInitializationPhysicalStep.selectedRowIndex p z = j ∧
        (z.1.1, past p r (sourceCoordinates z).2) ∈ Cell ∧
        source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k ell hAlpha r w ∧
        A_r rate rewards C_star C_h z i r ∧
        AffineChannelLaw.affineHash (((z.1.2 j).2 r).2 (0, i)) w = 1} =
      (1 : ENNReal) / 2 * BootstrapPrivateRoundStreams.sourceInputLaw p
        {z | ActualInitializationPhysicalStep.selectedRowIndex p z = j ∧
          (z.1.1, past p r (sourceCoordinates z).2) ∈ Cell ∧
          source_prelaunch_down_past_indicator rate rewards C_star C_h z i alpha k ell hAlpha r w ∧
          A_r rate rewards C_star C_h z i r} := by
  have h := source_prelaunch_down_pair_cylinder rate rewards C_star C_h i alpha k ell hAlpha w j r
    Cell hCell {a | AffineChannelLaw.affineHash a w = 1} MeasurableSet.of_discrete
  have hhalf : pairLaw p {a | AffineChannelLaw.affineHash a w = 1} = (1 : ENNReal) / 2 := by
    rw [pairLaw, ← AffineChannelLaw.eventProbability_eq_measure]
    exact AffineChannelLaw.affineHash_probability w 1
  rw [hhalf] at h
  exact h

end Cylinder

end Bandits.Support.ReferenceGeneratedPrelaunchDownCurrentPair
