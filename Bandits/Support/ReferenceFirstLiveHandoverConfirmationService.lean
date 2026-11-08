/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveHandoverBoundaryFactorization
public import Bandits.Support.ReferenceFirstLiveHandoverDownFeedback
public import Bandits.Support.DownServiceProbability

/-!
# First-live accepted-word DOWN confirmation service

The source event is the actual positive coordinator observation on a DOWN
round selecting a follower whose incoming state already carries this
selection's DOWN record and whose current affine hash is zero. The conditional
expectation reduction below keeps the complete original source and integrates
over the actual whole current-control law.

Sources: `05_binary_transport.tex:253-281`,
`06_interruptions.tex:286-291,431-490`, and
`appendix_a_local_protocol.tex:100-108` in the pinned ZIP4 manuscript.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open scoped Classical ENNReal

namespace Bandits.Support.ReferenceFirstLiveHandoverConfirmationService

open ReferenceFirstLiveHandoverBoundaryFactorization
open ReferenceFixedTimeSourceControlCoupling

section Context

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "H" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0

/-- Pull the actual accepted-word confirmation test through the complete
current-control conditional law on one unnormalized first-live source section.
This keeps the section indicator on the original source and leaves its actual
whole-control integral explicit for the service-law calculation. -/
theorem after_confirmation_condExp_integral
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (i : Fin (p.m - 1)) :
    mu[(fun z =>
      (if z ∈ ReferenceFirstLiveHandoverBoundaryFactorization.E_after
          rate rewards C_star C_h q s t i then (1 : ℝ) else 0) *
      (if ReferenceFirstLiveHandoverBoundaryFactorization.V_after
          rate rewards C_star C_h i t z then (1 : ℝ) else 0)) |
        H (t.val + 1)] =ᵐ[mu] fun z =>
      (if z ∈ ReferenceFirstLiveHandoverBoundaryFactorization.E_after
          rate rewards C_star C_h q s t i then (1 : ℝ) else 0) *
      ∫ control, (if ReferenceFirstLiveHandoverBoundaryFactorization.V_after
          rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
            control) then (1 : ℝ) else 0)
        ∂ContinuousLearningRows.timeControlLaw p := by
  classical
  let E := ReferenceFirstLiveHandoverBoundaryFactorization.E_after
    rate rewards C_star C_h q s t i
  let f : BootstrapPrivateRoundStreams.SourceInput p → ℝ := fun z =>
    if ReferenceFirstLiveHandoverBoundaryFactorization.V_after
      rate rewards C_star C_h i t z then 1 else 0
  let g : BootstrapPrivateRoundStreams.SourceInput p → ℝ := fun z =>
    if z ∈ E then 1 else 0
  let mus := BootstrapPrivateRoundStreams.sourceInputLaw p
  let Ht := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
    control0 (t.val + 1)
  let Hnext := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
    control0 (t.val + 2)
  let mΩ : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    Prod.instMeasurableSpace
  have hE : MeasurableSet[Ht] E := by
    dsimp [Ht, E]
    exact ReferenceFirstLiveHandoverBoundaryFactorization.measurableSet_E_after
      rate rewards C_star C_h control0 q s t hs i
  have hg : StronglyMeasurable[Ht] g := by
    change StronglyMeasurable[Ht]
      (E.indicator fun _ : BootstrapPrivateRoundStreams.SourceInput p => (1 : ℝ))
    exact stronglyMeasurable_const.indicator hE
  have hfield : Ht ≤ Hnext := by
    dsimp [Ht, Hnext]
    exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0).mono (by omega)
  have hf : StronglyMeasurable[Hnext] f := by
    dsimp [Hnext, f]
    exact ReferenceFirstLiveHandoverBoundaryFactorization.V_after_roundEnd_stronglyMeasurable
      rate rewards C_star C_h control0 i t
  have hambient : Hnext ≤ mΩ := by
    dsimp [Hnext]
    simpa [mΩ] using (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0).le (t.val + 2)
  have hfAmbient : StronglyMeasurable f := by
    simpa [mΩ] using hf.mono hambient
  have hfgAmbient : StronglyMeasurable (fun z => g z * f z) := by
    have hgAmbient : StronglyMeasurable g := by
      simpa [mΩ] using hg.mono (hfield.trans hambient)
    exact hgAmbient.mul hfAmbient
  have hnormf : ∀ z, ‖f z‖ ≤ (1 : ℝ) := by
    intro z
    by_cases hv : ReferenceFirstLiveHandoverBoundaryFactorization.V_after
      rate rewards C_star C_h i t z <;> simp [f, hv]
  have hnormfg : ∀ z, ‖g z * f z‖ ≤ (1 : ℝ) := by
    intro z
    by_cases hEz : z ∈ E <;>
      by_cases hVz : ReferenceFirstLiveHandoverBoundaryFactorization.V_after
        rate rewards C_star C_h i t z <;>
      simp [g, f, hEz, hVz]
  have hfInt : Integrable f mus := by
    refine (integrable_const (1 : ℝ)).mono' hfAmbient.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hnormf
  have hprodInt : Integrable (fun z => g z * f z) mus := by
    refine (integrable_const (1 : ℝ)).mono' hfgAmbient.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hnormfg
  have hpull := condExp_mul_of_stronglyMeasurable_left hg hprodInt hfInt
  have hraw := ReferenceFirstLiveHandoverBoundaryFactorization.V_after_condExp
    rate rewards C_star C_h control0 i t
  have hfinal :
      mus[(fun z => g z * f z) | Ht] =ᵐ[mus] fun z =>
        g z * ∫ control, (if ReferenceFirstLiveHandoverBoundaryFactorization.V_after
          rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
            control) then (1 : ℝ) else 0)
          ∂ContinuousLearningRows.timeControlLaw p := by
    filter_upwards [hpull, hraw] with z hpull hz
    calc
      mus[(fun z => g z * f z) | Ht] z = g z * mus[f | Ht] z := hpull
      _ = g z * (∫ control, (if
          ReferenceFirstLiveHandoverBoundaryFactorization.V_after rate rewards C_star C_h i t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
              control) then (1 : ℝ) else 0)
            ∂ContinuousLearningRows.timeControlLaw p) := by rw [hz]
  simpa only [mus, Ht, E, f, g, Set.indicator_apply, Set.mem_ofPred_eq] using hfinal

/-- On the actual accepted-word branch, the coordinator's physical positive
observation is exactly positivity of the original integer reward at the
selected receiver arm. -/
theorem actual_after_feedback_positive_iff_grid
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (hrW : r ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords
        rate rewards C_star C_h z))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some selected)
    (i : Fin (p.m - 1)) (hi : i ∈ selected.view.pendingAtChoice)
    (hdown : PublicDiscreteDraws.slotDraw (r.input.row.2 t).1 =
      PublicDiscreteDraws.downSlot)
    (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 t).1 = i)
    (hafter : ∃ incoming memory,
      r.input.state.followers i = .ordinary incoming memory ∧
        incoming.lastDown = some (selected.view.payload.downRecord i))
    (hzero : CoordinatorLocalArmChoice.currentDownHash selected.view.payload
      (r.input.row.2 t) i = 0) :
    0 < (r.output.preparation.feedback.observations
        (ActiveRoundActions.coordinator p.two_le_m)).val.val ↔
      0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
        (r.input.row.2 t).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val := by
  have hfeedback :=
    ReferenceFirstLiveHandoverDownFeedback.actual_first_live_after_down_feedback
      rate rewards C_star C_h z t r hr hrW selected hsel i hi hdown hdraw hafter hzero
  rw [hfeedback]
  have hD : (0 : ℝ) < (D p : ℝ) := by
    exact_mod_cast D_pos p
  constructor
  · intro hpositive
    by_contra hnot
    have hzeroIndex :
        (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (r.input.row.2 t).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val = 0 := by
      omega
    simp [RealRewardGridCount.realRewardGridValue, hzeroIndex] at hpositive
  · intro hpositive
    exact div_pos (by exact_mod_cast hpositive) hD

/-- The accepted static service law counts exactly the positive entries of
the original integer reward row after its literal grid rounding. -/
theorem positiveArms_card_eq_original_grid_count
    (t : Fin p.T) :
    (DownServiceProbability.positiveArms
      (⟨fun a => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (rewards t a),
        fun a => RealRewardGridCount.realRewardGridValue_mem_Icc
          (D p) (D_pos p) (rewards t a)⟩ : ActiveRoundActions.RewardRow p.K)).card =
      (Finset.univ.filter fun a : Fin p.K => 0 < (rewards t a).val).card := by
  have hD : (0 : ℝ) < (D p : ℝ) := by
    exact_mod_cast D_pos p
  have hpositive (a : Fin p.K) :
      0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a) ↔
        0 < (rewards t a).val := by
    constructor
    · intro h
      by_contra hnot
      have hzero : (rewards t a).val = 0 := by omega
      simp [RealRewardGridCount.realRewardGridValue, hzero] at h
    · intro h
      exact div_pos (by exact_mod_cast h) hD
  apply congrArg Finset.card
  ext a
  simp only [DownServiceProbability.positiveArms, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact hpositive a

private theorem actualRecord_time
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    r.input.time = t := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

/-- On an accepted-section source, the AFTER event is its exact physical
DOWN/zero-hash test with positivity expressed on the original integer grid. -/
theorem after_event_eq_original_grid_test
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (_hs : s ≤ t.val)
    (i : Fin (p.m - 1)) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hE : z ∈ ReferenceFirstLiveHandoverBoundaryFactorization.E_after
      rate rewards C_star C_h q s t i) :
    ReferenceFirstLiveHandoverBoundaryFactorization.V_after
        rate rewards C_star C_h i t z ↔
      ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
            some r ∧
          r ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords
              rate rewards C_star C_h z) ∧
          r.output.preparation.coordinator.selection = some selected ∧
          PublicDiscreteDraws.slotDraw (r.input.row.2 t).1 = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (r.input.row.2 t).1 = i ∧
          CoordinatorLocalArmChoice.currentDownHash selected.view.payload
            (r.input.row.2 t) i = 0 ∧
          0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
            (r.input.row.2 t).1).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val := by
  classical
  change ActualInitializationPhysicalStep.selectedRowIndex p z = q ∧
    ReferenceFirstLiveHandoverBoundaryFactorization.crossed
      rate rewards C_star C_h z ∧
    ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
      rate rewards C_star C_h z = s ∧
    s ≤ t.val ∧
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
          some r ∧
        r ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords
            rate rewards C_star C_h z) ∧
        r.output.preparation.coordinator.selection = some selected ∧
        i ∈ selected.view.pendingAtChoice ∧
        ReferenceFirstLiveHandoverBoundaryFactorization.After
          (p := p) (rate := rate) r selected i at hE
  rcases hE with ⟨_, _, _, _, r, selected, hr, hrW, hsel, hi, hafter⟩
  change (∃ r' : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ∃ selected' : ReferenceActivePhysicalStep.Selection r'.input,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
          some r' ∧
        r'.output.preparation.coordinator.selection = some selected' ∧
        PublicDiscreteDraws.slotDraw (r'.input.row.2 r'.input.time).1 =
          PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r'.input.row.2 r'.input.time).1 = i ∧
        CoordinatorLocalArmChoice.currentDownHash selected'.view.payload
          (r'.input.row.2 r'.input.time) i = 0 ∧
        0 < (r'.output.preparation.feedback.observations
          (ActiveRoundActions.coordinator p.two_le_m)).val.val) ↔ _
  constructor
  · rintro ⟨r', selected', hr', hsel', hdown, hdraw, hzero, hpositive⟩
    have hrEq : r' = r := Option.some.inj (hr'.symm.trans hr)
    subst r'
    have hselEq : selected' = selected := Option.some.inj (hsel'.symm.trans hsel)
    subst selected'
    have htime := actualRecord_time rate rewards C_star C_h t z r hr
    have hdown' : PublicDiscreteDraws.slotDraw (r.input.row.2 t).1 =
        PublicDiscreteDraws.downSlot := by simpa [htime] using hdown
    have hdraw' : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 t).1 = i := by simpa [htime] using hdraw
    have hzero' : CoordinatorLocalArmChoice.currentDownHash selected.view.payload
        (r.input.row.2 t) i = 0 := by simpa [htime] using hzero
    have hgrid := actual_after_feedback_positive_iff_grid rate rewards C_star C_h
      z t r hr hrW selected hsel i hi hdown' hdraw' hafter hzero'
    exact ⟨r, selected, hr, hrW, hsel, hdown', hdraw', hzero', hgrid.mp hpositive⟩
  · rintro ⟨r', selected', hr', hrW', hsel', hdown, hdraw, hzero, hpositive⟩
    have hrEq : r' = r := Option.some.inj (hr'.symm.trans hr)
    subst r'
    have hselEq : selected' = selected := Option.some.inj (hsel'.symm.trans hsel)
    subst selected'
    have htime := actualRecord_time rate rewards C_star C_h t z r hr
    have hdown' : PublicDiscreteDraws.slotDraw (r.input.row.2 t).1 =
        PublicDiscreteDraws.downSlot := hdown
    have hdraw' : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 t).1 = i := hdraw
    have hzero' : CoordinatorLocalArmChoice.currentDownHash selected.view.payload
        (r.input.row.2 t) i = 0 := hzero
    have hgrid := actual_after_feedback_positive_iff_grid rate rewards C_star C_h
      z t r hr hrW selected hsel i hi hdown' hdraw' hafter hzero'
    exact ⟨r, selected, hr, hsel,
      by simpa [htime] using hdown', by simpa [htime] using hdraw',
      by simpa [htime] using hzero', hgrid.mpr hpositive⟩

/-- Integrate the actual affine sample after the current scalar slice has
chosen its word. This finite partition law permits a slice dependent
first-installation payload without freezing that physical payload. -/
theorem variable_word_affine_hash_probability
    (word : ContinuousLearningRows.Slice p → AffineChannelLaw.Word (B p))
    (hword : Measurable word)
    (S : Set (ContinuousLearningRows.Slice p)) (hS : MeasurableSet S) :
    ((ContinuousControlSlice.sliceLaw p.m p.K).prod
      (AffineChannelLaw.jointLaw (B p)).toMeasure)
      ({x | x.1 ∈ S ∧ AffineChannelLaw.affineHash x.2 (word x.1) = 0}) =
      (ContinuousControlSlice.sliceLaw p.m p.K) S * ((1 : ENNReal) / 2) := by
  classical
  let sliceMeasure := ContinuousControlSlice.sliceLaw p.m p.K
  let affineMeasure := (AffineChannelLaw.jointLaw (B p)).toMeasure
  let A : AffineChannelLaw.Word (B p) → Set (ContinuousLearningRows.Slice p) :=
    fun w => {x | x ∈ S ∧ word x = w}
  let C : AffineChannelLaw.Word (B p) → Set (AffineChannelLaw.Sample (B p)) :=
    fun w => {y | AffineChannelLaw.affineHash y w = 0}
  let rectangle : AffineChannelLaw.Word (B p) →
      Set (ContinuousLearningRows.Slice p × AffineChannelLaw.Sample (B p)) :=
    fun w => A w ×ˢ C w
  let event : Set (ContinuousLearningRows.Slice p × AffineChannelLaw.Sample (B p)) :=
    {x | x.1 ∈ S ∧ AffineChannelLaw.affineHash x.2 (word x.1) = 0}
  have hAmeas : ∀ w, MeasurableSet (A w) := by
    intro w
    exact hS.inter (hword (measurableSet_singleton w))
  have hCmeas : ∀ w, MeasurableSet (C w) := by
    intro w
    exact MeasurableSet.of_discrete
  have hRectMeas : ∀ w, MeasurableSet (rectangle w) := by
    intro w
    exact (hAmeas w).prod (hCmeas w)
  have hEventUnion : event =
      ⋃ w ∈ (Finset.univ : Finset (AffineChannelLaw.Word (B p))), rectangle w := by
    ext x
    simp only [event, rectangle, A, C, Set.mem_ofPred_eq, Set.mem_iUnion,
      Finset.mem_univ, Set.mem_prod]
    constructor
    · rintro ⟨hxS, hhash⟩
      exact ⟨word x.1, trivial, ⟨hxS, rfl⟩, hhash⟩
    · rintro ⟨w, _, ⟨hxS, hwordx⟩, hhash⟩
      exact ⟨hxS, hwordx.symm ▸ hhash⟩
  have hRectDisjoint : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (AffineChannelLaw.Word (B p)))) rectangle := by
    intro w hw w' hw' hne
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    exact hne (hx.1.2.symm.trans hx'.1.2)
  have hAUnion :
      (⋃ w ∈ (Finset.univ : Finset (AffineChannelLaw.Word (B p))), A w) = S := by
    ext x
    simp only [A, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_univ]
    constructor
    · rintro ⟨w, _, hxS, _⟩
      exact hxS
    · intro hxS
      exact ⟨word x, trivial, hxS, rfl⟩
  have hADisjoint : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (AffineChannelLaw.Word (B p)))) A := by
    intro w hw w' hw' hne
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    exact hne (hx.2.symm.trans hx'.2)
  have hASum : (∑ w ∈ (Finset.univ : Finset (AffineChannelLaw.Word (B p))),
      sliceMeasure (A w)) = sliceMeasure S := by
    calc
      _ = sliceMeasure (⋃ w ∈ (Finset.univ : Finset (AffineChannelLaw.Word (B p))), A w) :=
        (MeasureTheory.measure_biUnion_finset hADisjoint (by
          intro w hw
          exact hAmeas w)).symm
      _ = sliceMeasure S := congrArg sliceMeasure hAUnion
  have hCmass (w : AffineChannelLaw.Word (B p)) :
      affineMeasure (C w) = (1 : ENNReal) / 2 := by
    change (AffineChannelLaw.jointLaw (B p)).toMeasure
      {sample | AffineChannelLaw.affineHash sample w = 0} = _
    rw [← AffineChannelLaw.eventProbability_eq_measure]
    exact AffineChannelLaw.affineHash_probability w 0
  calc
    _ = ∑ w ∈ (Finset.univ : Finset (AffineChannelLaw.Word (B p))),
          (sliceMeasure (A w) * affineMeasure (C w)) := by
      change (sliceMeasure.prod affineMeasure) event = _
      rw [hEventUnion, MeasureTheory.measure_biUnion_finset hRectDisjoint
        (by intro w hw; exact hRectMeas w)]
      simp only [rectangle, MeasureTheory.Measure.prod_prod]
    _ = (∑ w ∈ (Finset.univ : Finset (AffineChannelLaw.Word (B p))),
          sliceMeasure (A w)) * ((1 : ENNReal) / 2) := by
      simp_rw [hCmass]
      rw [Finset.sum_mul]
    _ = sliceMeasure S * ((1 : ENNReal) / 2) := by rw [hASum]

/-- The same slice dependent affine-bit law on the actual full TimeControl
carrier, using its accepted slice and affine-sample marginals. -/
theorem timeControl_variable_word_affine_hash_probability
    (channel : ContinuousLearningRows.Channel p)
    (word : ContinuousLearningRows.Slice p → AffineChannelLaw.Word (B p))
    (hword : Measurable word)
    (S : Set (ContinuousLearningRows.Slice p)) (hS : MeasurableSet S) :
    (ContinuousLearningRows.timeControlLaw p)
      {control | control.1 ∈ S ∧
        AffineChannelLaw.affineHash (control.2 channel) (word control.1) = 0} =
      (ContinuousControlSlice.sliceLaw p.m p.K) S * ((1 : ENNReal) / 2) := by
  classical
  let output : ContinuousLearningRows.TimeControl p →
      ContinuousLearningRows.Slice p × AffineChannelLaw.Sample (B p) :=
    fun control => (control.1, control.2 channel)
  let event : Set (ContinuousLearningRows.Slice p × AffineChannelLaw.Sample (B p)) :=
    {x | x.1 ∈ S ∧ AffineChannelLaw.affineHash x.2 (word x.1) = 0}
  have houtput : Measurable output := by
    exact measurable_fst.prodMk ((measurable_pi_apply channel).comp measurable_snd)
  let A : AffineChannelLaw.Word (B p) → Set (ContinuousLearningRows.Slice p) :=
    fun w => {x | x ∈ S ∧ word x = w}
  let C : AffineChannelLaw.Word (B p) → Set (AffineChannelLaw.Sample (B p)) :=
    fun w => {y | AffineChannelLaw.affineHash y w = 0}
  let rectangle : AffineChannelLaw.Word (B p) →
      Set (ContinuousLearningRows.Slice p × AffineChannelLaw.Sample (B p)) :=
    fun w => A w ×ˢ C w
  have hAmeas : ∀ w, MeasurableSet (A w) := by
    intro w
    exact hS.inter (hword (measurableSet_singleton w))
  have hCmeas : ∀ w, MeasurableSet (C w) := by
    intro w
    exact MeasurableSet.of_discrete
  have hRectMeas : ∀ w, MeasurableSet (rectangle w) := by
    intro w
    exact (hAmeas w).prod (hCmeas w)
  have hEventUnion : event =
      ⋃ w ∈ (Finset.univ : Finset (AffineChannelLaw.Word (B p))), rectangle w := by
    ext x
    simp only [event, rectangle, A, C, Set.mem_ofPred_eq, Set.mem_iUnion,
      Finset.mem_univ, Set.mem_prod]
    constructor
    · rintro ⟨hxS, hhash⟩
      exact ⟨word x.1, trivial, ⟨hxS, rfl⟩, hhash⟩
    · rintro ⟨w, _, ⟨hxS, hwordx⟩, hhash⟩
      exact ⟨hxS, hwordx.symm ▸ hhash⟩
  have hEventMeas : MeasurableSet event := by
    rw [hEventUnion]
    exact Finset.measurableSet_biUnion Finset.univ (by
      intro w hw
      exact hRectMeas w)
  have houtputLaw : (ContinuousLearningRows.timeControlLaw p).map output =
      (ContinuousControlSlice.sliceLaw p.m p.K).prod
        (AffineChannelLaw.jointLaw (B p)).toMeasure := by
    have hind := (ContinuousLearningRows.indepFun_slice_affineSamples p).comp
      measurable_id (measurable_pi_apply channel)
    have hprod := hind.map_prod_eq_prod_map_map
      (measurable_fst.comp houtput).aemeasurable
      (measurable_snd.comp houtput).aemeasurable
    have hmapSlice : (ContinuousLearningRows.timeControlLaw p).map
        (fun control => control.1) = ContinuousControlSlice.sliceLaw p.m p.K :=
      ContinuousLearningRows.map_slice p
    have hmapAffine : (ContinuousLearningRows.timeControlLaw p).map
        (fun control => control.2 channel) =
          (AffineChannelLaw.jointLaw (B p)).toMeasure :=
      ContinuousLearningRows.map_affineSample p channel
    change (ContinuousLearningRows.timeControlLaw p).map
      (fun control => (control.1, control.2 channel)) = _
    calc
      _ = ((ContinuousLearningRows.timeControlLaw p).map Prod.fst).prod
          ((ContinuousLearningRows.timeControlLaw p).map
            (fun control => control.2 channel)) := hprod
      _ = _ := by rw [hmapSlice, hmapAffine]
  have hevent :
      {control : ContinuousLearningRows.TimeControl p | control.1 ∈ S ∧
        AffineChannelLaw.affineHash (control.2 channel) (word control.1) = 0} =
        output ⁻¹' event := by
    ext control
    rfl
  rw [hevent, ← Measure.map_apply houtput hEventMeas, houtputLaw]
  exact variable_word_affine_hash_probability word hword S hS

private theorem scalar_service_probability (i : ActiveRoundActions.Follower p.m)
    (S : Finset (Fin p.K)) :
    (ContinuousControlSlice.sliceLaw p.m p.K)
      {x | PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) ∈ S} =
      ENNReal.ofReal ((S.card : ℝ) / (4 * ((p.m - 1 : ℕ) : ℝ) * p.K)) := by
  let ν := ContinuousControlSlice.sliceLaw p.m p.K
  let pairDraw : Slice p → PublicDiscreteDraws.Slot × ActiveRoundActions.Follower p.m :=
    fun x => (PublicDiscreteDraws.slotDraw x,
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x)
  let tupleDraw : Slice p → OrderedTupleSampler.Tuple p.m p.K :=
    OrderedTupleSampler.sample p.two_le_m p.m_lt_K
  let tupleSet : Set (OrderedTupleSampler.Tuple p.m p.K) :=
    {f | f.val (PublicDiscreteDraws.followerPlayer p.two_le_m i) ∈ S}
  let selectedDrawPair := fun draws : (j : PublicDiscreteDraws.DrawIndex p.m p.K) →
      PublicDiscreteDraws.DrawOutput j => (draws .slot, draws .selectedFollower)
  have hm : Measurable selectedDrawPair :=
    (measurable_pi_apply (PublicDiscreteDraws.DrawIndex.slot :
      PublicDiscreteDraws.DrawIndex p.m p.K)).prodMk
      (measurable_pi_apply (PublicDiscreteDraws.DrawIndex.selectedFollower :
        PublicDiscreteDraws.DrawIndex p.m p.K))
  have hgroup := PublicDiscreteDraws.indepFun_drawFamily_tupleInputs
    p.two_le_m p.m_lt_K (K_pos p)
  have hdrawTuple : IndepFun pairDraw tupleDraw ν :=
    hgroup.comp hm (OrderedTupleSampler.measurable_sampleCube p.m_lt_K)
  have hpair : ν (pairDraw ⁻¹' {(PublicDiscreteDraws.downSlot, i)}) =
      ENNReal.ofReal (1 / 4) * ENNReal.ofReal (1 / (((p.m - 1 : ℕ) : ℝ))) := by
    have hij : (PublicDiscreteDraws.DrawIndex.slot : PublicDiscreteDraws.DrawIndex p.m p.K) ≠
        PublicDiscreteDraws.DrawIndex.selectedFollower := by
      intro h
      cases h
    have h := (PublicDiscreteDraws.iIndepFun_drawFamily
      p.two_le_m p.m_lt_K (K_pos p)).indepFun hij
    have hmass := h.measure_inter_preimage_eq_mul
      ({PublicDiscreteDraws.downSlot} : Set PublicDiscreteDraws.Slot)
      ({i} : Set (ActiveRoundActions.Follower p.m))
      (measurableSet_singleton _) (measurableSet_singleton _)
    have hslotEq : PublicDiscreteDraws.drawFamily p.two_le_m p.m_lt_K
        (K_pos p) .slot = PublicDiscreteDraws.slotDraw := rfl
    have hselectedEq : PublicDiscreteDraws.drawFamily p.two_le_m p.m_lt_K
        (K_pos p) .selectedFollower =
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K := rfl
    rw [hslotEq, hselectedEq] at hmass
    change ν (PublicDiscreteDraws.slotDraw ⁻¹' {PublicDiscreteDraws.downSlot} ∩
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i}) =
      ν (PublicDiscreteDraws.slotDraw ⁻¹' {PublicDiscreteDraws.downSlot}) *
        ν (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i}) at hmass
    have hevent : pairDraw ⁻¹' {(PublicDiscreteDraws.downSlot, i)} =
        PublicDiscreteDraws.slotDraw ⁻¹' {PublicDiscreteDraws.downSlot} ∩
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i} := by
      ext x
      simp [pairDraw]
    dsimp only [ν]
    rw [hevent]
    calc
      _ = _ := hmass
      _ = _ := by
        rw [PublicDiscreteDraws.slotDraw_atom (m := p.m) (K := p.K)
            PublicDiscreteDraws.downSlot,
          PublicDiscreteDraws.selectedFollowerDraw_atom p.two_le_m p.m_lt_K i,
          PublicDiscreteDraws.slotMass_down, PublicDiscreteDraws.equalMass]
        norm_num [PublicDiscreteDraws.followerCount]
  have htuple : ν (tupleDraw ⁻¹' tupleSet) =
      ENNReal.ofReal ((S.card : ℝ) / (p.K : ℝ)) := by
    exact DownServiceProbability.orderedTupleReceiver_uniform p.two_le_m p.m_lt_K
      (PublicDiscreteDraws.followerPlayer p.two_le_m i) S
  have hmeasure := hdrawTuple.measure_inter_preimage_eq_mul
    ({(PublicDiscreteDraws.downSlot, i)} :
      Set (PublicDiscreteDraws.Slot × ActiveRoundActions.Follower p.m))
    tupleSet MeasurableSet.of_discrete MeasurableSet.of_discrete
  have hevent : {x : Slice p | PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) ∈ S} =
      pairDraw ⁻¹' {(PublicDiscreteDraws.downSlot, i)} ∩ tupleDraw ⁻¹' tupleSet := by
    ext x
    simp [pairDraw, tupleDraw, tupleSet, and_assoc]
  rw [hevent, hmeasure, hpair, htuple]
  have hnonneg : (0 : ℝ) ≤ (1 / 4) * (1 / (((p.m - 1 : ℕ) : ℝ))) := by positivity
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
    ← ENNReal.ofReal_mul hnonneg]
  congr 1
  field_simp

/-- The actual scalar DOWN/follower/positive-receiver region, followed by a
fixed genuine affine bit, has the public accepted one-round service mass.
The companion variable-word theorem then permits the physical section's word
to be chosen by that same scalar slice. -/
theorem positive_receiver_slice_half_probability (t : Fin p.T)
    (i : Fin (p.m - 1)) :
    let roundedRow : ActiveRoundActions.RewardRow p.K :=
      ⟨fun a => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (rewards t a),
        fun a => RealRewardGridCount.realRewardGridValue_mem_Icc
          (D p) (D_pos p) (rewards t a)⟩
    let serviceSlice : Set (ContinuousLearningRows.Slice p) :=
      {x | PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        0 < roundedRow.val ((OrderedTupleSampler.sample p.two_le_m
          p.m_lt_K x).val (PublicDiscreteDraws.followerPlayer p.two_le_m i))}
    (ContinuousControlSlice.sliceLaw p.m p.K) serviceSlice * ((1 : ENNReal) / 2) =
      ENNReal.ofReal (((DownServiceProbability.positiveArms roundedRow).card : ℝ) /
        (8 * (ContinuousLearningRows.d p : ℝ) * (p.K : ℝ))) := by
  classical
  let roundedRow : ActiveRoundActions.RewardRow p.K :=
    ⟨fun a => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a),
      fun a => RealRewardGridCount.realRewardGridValue_mem_Icc
        (D p) (D_pos p) (rewards t a)⟩
  change (ContinuousControlSlice.sliceLaw p.m p.K)
      {x | PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        0 < roundedRow.val ((OrderedTupleSampler.sample p.two_le_m
          p.m_lt_K x).val (PublicDiscreteDraws.followerPlayer p.two_le_m i))} *
      ((1 : ENNReal) / 2) = _
  have hset : {x : Slice p |
      PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        0 < roundedRow.val ((OrderedTupleSampler.sample p.two_le_m
          p.m_lt_K x).val (PublicDiscreteDraws.followerPlayer p.two_le_m i))} =
      {x | PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) ∈
            DownServiceProbability.positiveArms roundedRow} := by
    ext x
    simp only [DownServiceProbability.positiveArms, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [hset, scalar_service_probability i (DownServiceProbability.positiveArms roundedRow)]
  rw [show (1 : ENNReal) / 2 = ENNReal.ofReal ((1 : ℝ) / 2) by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  dsimp only [ContinuousLearningRows.d]
  ring

/-- One current control has the exact positive-receiver service mass even
when its physical DOWN word was selected as a measurable function of the
same scalar slice. -/
theorem slice_selected_word_positive_receiver_probability (t : Fin p.T)
    (i : Fin (p.m - 1))
    (word : ContinuousLearningRows.Slice p → AffineChannelLaw.Word (B p))
    (hword : Measurable word) :
    (ContinuousLearningRows.timeControlLaw p)
      {control | PublicDiscreteDraws.slotDraw control.1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1 = i ∧
        0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K control.1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))) ∧
        AffineChannelLaw.affineHash (control.2 (DownServiceProbability.downChannel p i))
          (word control.1) = 0} =
      ENNReal.ofReal (((Finset.univ.filter fun a : Fin p.K =>
        0 < (rewards t a).val).card : ℝ) /
          (8 * (ContinuousLearningRows.d p : ℝ) * (p.K : ℝ))) := by
  classical
  let roundedRow : ActiveRoundActions.RewardRow p.K :=
    ⟨fun a => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a),
      fun a => RealRewardGridCount.realRewardGridValue_mem_Icc (D p) (D_pos p) (rewards t a)⟩
  let serviceSlice : Set (ContinuousLearningRows.Slice p) :=
    {x | PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
      0 < roundedRow.val ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))}
  have hslot : Measurable (PublicDiscreteDraws.slotDraw (m := p.m) (K := p.K)) :=
    PublicDiscreteDraws.measurable_slotDraw (m := p.m) (K := p.K)
  have hselected : Measurable (PublicDiscreteDraws.selectedFollowerDraw
      p.two_le_m p.m_lt_K) :=
    PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K
  have htuple : Measurable (fun x : ContinuousLearningRows.Slice p =>
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val) :=
    measurable_subtype_coe.comp
      (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K)
  have hreceiver : Measurable (fun x : ContinuousLearningRows.Slice p =>
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) :=
    (measurable_pi_apply (PublicDiscreteDraws.followerPlayer p.two_le_m i)).comp htuple
  have hrow : Measurable (fun a : Fin p.K => roundedRow.val a) :=
    Measurable.of_discrete
  have hreward : Measurable (fun x : ContinuousLearningRows.Slice p =>
      roundedRow.val ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))) := hrow.comp hreceiver
  have hserviceMeas : MeasurableSet serviceSlice := by
    exact (hslot (measurableSet_singleton PublicDiscreteDraws.downSlot)).inter
      ((hselected (measurableSet_singleton i)).inter (hreward measurableSet_Ioi))
  have hwordLaw := timeControl_variable_word_affine_hash_probability
    (DownServiceProbability.downChannel p i) word hword serviceSlice hserviceMeas
  have hbase := positive_receiver_slice_half_probability rewards t i
  have hcount := positiveArms_card_eq_original_grid_count rewards t
  have hresult := hwordLaw.trans hbase
  have hset :
      {control : ContinuousLearningRows.TimeControl p |
        PublicDiscreteDraws.slotDraw control.1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1 = i ∧
        0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K control.1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))) ∧
        AffineChannelLaw.affineHash
          (control.2 (DownServiceProbability.downChannel p i)) (word control.1) = 0} =
      {control | control.1 ∈ serviceSlice ∧
        AffineChannelLaw.affineHash
          (control.2 (DownServiceProbability.downChannel p i)) (word control.1) = 0} := by
    ext control
    simp only [serviceSlice, Set.mem_ofPred_eq, roundedRow]
    tauto
  rw [hset]
  simpa [roundedRow, ContinuousLearningRows.d] using hresult.trans
    (congrArg (fun card : ℕ => ENNReal.ofReal
      ((card : ℝ) / (8 * (ContinuousLearningRows.d p : ℝ) * (p.K : ℝ)))) hcount)

private theorem prefix_replace (t : Fin p.T) (z : Source p) (u : TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (replaceSourceControl p t z u) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext j
    by_cases hj : j = ActualInitializationPhysicalStep.selectedRowIndex p z
    · subst j
      simp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        replaceSourceControl, sourceCoordinatorIndex_eq_selectedRowIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < t.val
      · have hvt : v ≠ t := fun h => by subst v; omega
        simp only [hv, ite_true, Function.update_of_ne hvt]
      · simp only [hv, ite_false]
    · have hj' : j ≠ ActualInitializationPhysicalStep.selectedRowIndex p
          (replaceSourceControl p t z u) := hj
      rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_otherRow control0 _ _ j hj',
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix_otherRow control0 _ _ j hj]
      exact Function.update_of_ne hj _ _
  · rfl

include control0 in
/-- The actual section survives every replacement of the whole current
control. No selection or payload is frozen by this assertion. -/
theorem E_after_replaceSourceControl (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (i : Fin (p.m - 1))
    (z : Source p) (u : TimeControl p) :
    replaceSourceControl p t z u ∈ E_after rate rewards C_star C_h q s t i ↔
      z ∈ E_after rate rewards C_star C_h q s t i := by
  rw [E_after_sourcePrefix rate rewards C_star C_h control0 q s t hs,
    prefix_replace control0,
    ← E_after_sourcePrefix rate rewards C_star C_h control0 q s t hs]

private theorem actualRecord_fields (t : Fin p.T) (z : Source p)
    (r : Record (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

private theorem record_selection (r : Record (p := p) (rate := rate)) :
    r.output.preparation.coordinator.selection =
      (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection := by
  rw [r.output_eq]
  rfl

include control0 in
/-- Every current replacement has its own actual record and actual selected
payload, including the FIRST installation round. -/
theorem replacement_section_witnesses (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (i : Fin (p.m - 1))
    (z : Source p) (hz : z ∈ E_after rate rewards C_star C_h q s t i)
    (u : TimeControl p) :
    ∃ (r : Record (p := p) (rate := rate)) (selected : Selection (rate := rate) r),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
        (replaceSourceControl p t z u) = some r ∧
      r ∈ firstWindow rate rewards C_star C_h (replaceSourceControl p t z u) ∧
      r.output.preparation.coordinator.selection = some selected ∧
      i ∈ selected.view.pendingAtChoice ∧ After (rate := rate) r selected i ∧
      r.input.row.2 t = u := by
  have hu := (E_after_replaceSourceControl rate rewards C_star C_h control0
    q t s hs i z u).mpr hz
  obtain ⟨_, _, _, _, r, selected, hr, hW, hsel, hi, hb⟩ := hu
  refine ⟨r, selected, hr, hW, hsel, hi, hb, ?_⟩
  obtain ⟨hrows, hJ, _, _⟩ := actualRecord_fields rate rewards C_star C_h t _ r hr
  simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hJ,
    replaceSourceControl, ActualInitializationPhysicalStep.selectedRowIndex,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex, Function.update_self]

private theorem actual_firstLiveState (z : Source p)
    (hz : crossed rate rewards C_star C_h z)
    (r : Record (p := p) (rate := rate))
    (hW : r ∈ firstWindow rate rewards C_star C_h z) :
    ReferenceFirstLiveConfirmationHistory.FirstLiveState r.input.state := by
  let seed := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hz
  have hseed := ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
    rate z rewards C_star C_h hz
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hz
  have hfull := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate z rewards C_star C_h seed hlaunch
  change r ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) at hW
  rw [hfull] at hW
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hW
  have h := ReferenceFirstLiveConfirmationHistory.run_firstLive_carried seed z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards _ _ _ _
    hseed.1 hseed.2.2 ⟨k, hk⟩
  simpa only [heq] using h

private theorem first_selection_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hc : x.state.coordinator = .first) (selected : ReferenceActivePhysicalStep.Selection x)
    (hsel : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected) :
    selected.view.payload = (CoordinatorAssignmentRegisterInstall.installFirst
      (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x))).registers.payload := by
  have h := congrArg Prod.snd (ReferenceActiveTemporalCausality.first_dispatch_readout x hc)
  change (ReferenceActivePhysicalStep.dispatch x).selection = some selected at hsel
  simp only [ReferenceActivePhysicalStep.DispatchCut.downView, hsel, Option.map_some,
    ReferenceActiveTemporalCausality.firstReadout, Option.some.injEq] at h
  exact congrArg (fun v => v.payload) h

private theorem live_selection_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (hc : x.state.coordinator = .live registers owned base)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hsel : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected) :
    selected.view.payload = registers.payload := by
  change (ReferenceActivePhysicalStep.dispatch x).selection = some selected at hsel
  have hd : ReferenceActivePhysicalStep.dispatch x = .live registers owned base
      (CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x registers owned base)) := by
    simp only [ReferenceActivePhysicalStep.dispatch, hc, CoordinatorRoundDispatch.dispatch]
    rfl
  rw [hd] at hsel
  cases hout : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput x registers owned base) <;>
    simp only [hout, ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, dite_true] at hsel
  all_goals first
    | cases hsel
      rfl
    | contradiction

private theorem selection_payload_eq_of_scalar
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (hscalar : (x.row.2 x.time).1 = (y.row.2 y.time).1)
    (hphase : ReferenceFirstLiveConfirmationHistory.FirstLiveState x.state)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (selected' : ReferenceActivePhysicalStep.Selection y)
    (hsel : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected)
    (hsel' : (ReferenceActivePhysicalStep.prepare y).coordinator.selection = some selected') :
    selected.view.payload = selected'.view.payload := by
  cases hc : x.state.coordinator with
  | first =>
      have hc' : y.state.coordinator = .first := hstate ▸ hc
      rw [first_selection_payload rate x hc selected hsel,
        first_selection_payload rate y hc' selected' hsel']
      have hlaunch : CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput x) =
        CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput y) := by
        unfold CoordinatorRoundDispatch.firstLaunchInput ReferenceActivePhysicalStep.firstInput
          LaterAssignmentStartOperation.ownAssignmentVector
        dsimp only
        congr 1
        exact congrArg ContinuousControlSlice.assignmentVector hscalar
      exact congrArg (fun launch =>
        (CoordinatorAssignmentRegisterInstall.installFirst launch).registers.payload) hlaunch
  | live registers owned base =>
      have hc' : y.state.coordinator = .live registers owned base := hstate ▸ hc
      rw [live_selection_payload rate x registers owned base hc selected hsel,
        live_selection_payload rate y registers owned base hc' selected' hsel']
  | collection payload ledger proposal =>
      simp only [ReferenceFirstLiveConfirmationHistory.FirstLiveState, hc] at hphase
  | dagger =>
      change (ReferenceActivePhysicalStep.dispatch x).selection = some selected at hsel
      rw [ReferenceActivePhysicalStep.dispatch_dagger x hc] at hsel
      cases hsel

include control0 in
/-- The actual word may depend on the scalar slice. It does not depend on the
current affine family, since both actual calls share the strict past and the
same current scalar slice. -/
theorem replacement_payload_eq_of_same_slice (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (i : Fin (p.m - 1))
    (z : Source p) (hz : z ∈ E_after rate rewards C_star C_h q s t i)
    (u v : TimeControl p) (huv : u.1 = v.1)
    (r r' : Record (p := p) (rate := rate))
    (selected : Selection (rate := rate) r) (selected' : Selection (rate := rate) r')
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
      (replaceSourceControl p t z u) = some r)
    (hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
      (replaceSourceControl p t z v) = some r')
    (hsel : r.output.preparation.coordinator.selection = some selected)
    (hsel' : r'.output.preparation.coordinator.selection = some selected') :
    selected.view.payload = selected'.view.payload := by
  have hE := (E_after_replaceSourceControl rate rewards C_star C_h control0
    q t s hs i z u).mpr hz
  obtain ⟨_, hcross, _, _, rr, ss, hrr, hW, _, _, _⟩ := hE
  have heq := Option.some.inj (hr.symm.trans hrr)
  subst rr
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
      (replaceSourceControl p t z u) =
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
      (replaceSourceControl p t z v) := by
    rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0,
      ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 t
        (replaceSourceControl p t z v), prefix_replace control0, prefix_replace control0]
  simp only [ReferenceSourcePrefixHistoryFiltration.incoming, hr, hr', Option.map_some,
    Option.some.injEq] at hin
  have hstate := ReferenceActivePhysicalStepMeasurability.encodeState_injective hin
  obtain ⟨hrows, hJ, ht, _⟩ := actualRecord_fields rate rewards C_star C_h t _ r hr
  obtain ⟨hrows', hJ', ht', _⟩ := actualRecord_fields rate rewards C_star C_h t _ r' hr'
  apply selection_payload_eq_of_scalar rate r.input r'.input hstate (ht.trans ht'.symm)
    _ (actual_firstLiveState rate rewards C_star C_h _ hcross r hW) selected selected'
    ((record_selection rate r).symm ▸ hsel) ((record_selection rate r').symm ▸ hsel')
  simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hJ, ht,
    hrows', hJ', ht', replaceSourceControl, ActualInitializationPhysicalStep.selectedRowIndex,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex, Function.update_self]
  exact huv

private theorem observation_iff (t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source p) (r : Record (p := p) (rate := rate))
    (selected : Selection (rate := rate) r)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (hW : r ∈ firstWindow rate rewards C_star C_h z)
    (hsel : r.output.preparation.coordinator.selection = some selected)
    (hi : i ∈ selected.view.pendingAtChoice)
    (ha : After (rate := rate) r selected i) :
    V_after rate rewards C_star C_h i t z ↔
      PublicDiscreteDraws.slotDraw (r.input.row.2 t).1 = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 t).1 = i ∧
      0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
        (r.input.row.2 t).1).val (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val ∧
      CoordinatorLocalArmChoice.currentDownHash selected.view.payload
        (r.input.row.2 t) i = 0 := by
  have ht := (actualRecord_fields rate rewards C_star C_h t z r hr).2.2.1
  constructor
  · rintro ⟨r', selected', hr', hsel', hd, hf, hzero, hp⟩
    have heq := Option.some.inj (hr'.symm.trans hr)
    subst r'
    have hselected := Option.some.inj (hsel'.symm.trans hsel)
    subst selected'
    rw [ht] at hd hf hzero
    exact ⟨hd, hf,
      (actual_after_feedback_positive_iff_grid rate rewards C_star C_h
        z t r hr hW selected hsel i hi hd hf ha hzero).mp hp, hzero⟩
  · rintro ⟨hd, hf, hp, hzero⟩
    exact ⟨r, selected, hr, hsel, ht.symm ▸ hd, ht.symm ▸ hf,
      ht.symm ▸ hzero,
      (actual_after_feedback_positive_iff_grid rate rewards C_star C_h
        z t r hr hW selected hsel i hi hd hf ha hzero).mpr hp⟩

private theorem affine_indicator_integral (i : Fin (d p))
    (word : AffineChannelLaw.Word (B p)) :
    (∫ a : AffineSamples p,
      (if AffineChannelLaw.affineHash (a (0, i)) word = 0 then (1 : ℝ) else 0)
      ∂affineSamplesLaw p) = 1 / 2 := by
  let A : Set (AffineChannelLaw.Sample (B p)) :=
    {sample | AffineChannelLaw.affineHash sample word = 0}
  have hA : MeasurableSet A := MeasurableSet.of_discrete
  have hpre : MeasurableSet {a : AffineSamples p |
      AffineChannelLaw.affineHash (a (0, i)) word = 0} :=
    hA.preimage (measurable_pi_apply (0, i))
  have hmass : (affineSamplesLaw p)
      {a : AffineSamples p | AffineChannelLaw.affineHash (a (0, i)) word = 0} =
      (1 : ℝ≥0∞) / 2 := by
    change (affineSamplesLaw p) ((fun a : AffineSamples p => a (0, i)) ⁻¹' A) = _
    rw [← Measure.map_apply (measurable_pi_apply (0, i)) hA]
    have hmap := (measurePreserving_eval
      (fun _ : Channel p => (AffineChannelLaw.jointLaw (B p)).toMeasure) (0, i)).map_eq
    change (Measure.map _ (Measure.pi _)) A = _
    rw [hmap, ← AffineChannelLaw.eventProbability_eq_measure,
      AffineChannelLaw.affineHash_probability]
  have hint := integral_indicator_one (μ := affineSamplesLaw p) hpre
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply] at hint
  rw [hint, Measure.real, hmass]
  norm_num

/-- Integrability of the genuine whole-current-control replacement test on
every original source, without a positive-mass or section assumption. -/
theorem integrable_replacement_observation (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source p) :
    Integrable (fun u : TimeControl p =>
      if V_after rate rewards C_star C_h i t (replaceSourceControl p t z u)
      then (1 : ℝ) else 0) (timeControlLaw p) := by
  have hB := measurableSet_B_after rate rewards C_star C_h i t
  have hset : MeasurableSet {u : TimeControl p |
      V_after rate rewards C_star C_h i t (replaceSourceControl p t z u)} :=
    hB.preimage (measurable_const.prodMk measurable_id)
  exact (integrable_const (1 : ℝ)).indicator hset

include control0 in
/-- Integrate the actual affine family first, with the actual word held fixed
only for this scalar slice. The word is produced from an actual replacement
call, and its equality at every other affine family is proved above. -/
theorem affine_first_replacement_integral (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (i : Fin (p.m - 1))
    (z : Source p) (hz : z ∈ E_after rate rewards C_star C_h q s t i)
    (x : Slice p) :
    (∫ a : AffineSamples p,
      (if V_after rate rewards C_star C_h i t (replaceSourceControl p t z (x, a))
       then (1 : ℝ) else 0) ∂affineSamplesLaw p) =
      (if PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val
       then (1 : ℝ) else 0) * (1 / 2) := by
  obtain ⟨r0, selected0, hr0, _, hsel0, _, _, _⟩ :=
    replacement_section_witnesses rate rewards C_star C_h control0 q t s hs i z hz
      (x, control0.2)
  let word := CoordinatorLocalArmChoice.storedDownFlatWord selected0.view.payload i
  have heq (a : AffineSamples p) :
      (if V_after rate rewards C_star C_h i t (replaceSourceControl p t z (x, a))
       then (1 : ℝ) else 0) =
      (if PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val
       then (if AffineChannelLaw.affineHash (a (0, i)) word = 0 then 1 else 0)
       else 0) := by
    obtain ⟨r, selected, hr, hW, hsel, hi, hb, hcurrent⟩ :=
      replacement_section_witnesses rate rewards C_star C_h control0 q t s hs i z hz (x, a)
    have hpayload := replacement_payload_eq_of_same_slice rate rewards C_star C_h control0
      q t s hs i z hz (x, a) (x, control0.2) rfl
      r r0 selected selected0 hr hr0 hsel hsel0
    rw [observation_iff rate rewards C_star C_h t i _ r selected hr hW hsel hi hb,
      hcurrent, hpayload]
    by_cases hbit : AffineChannelLaw.affineHash (a (0, i)) word = 0 <;>
      simp only [CoordinatorLocalArmChoice.currentDownHash,
        CoordinatorLocalArmChoice.downChannel, word] at hbit ⊢ <;>
      simp only [hbit, and_true, and_false, ite_true, ite_false, ite_self]
  simp_rw [heq]
  split_ifs with hscalar
  · simpa only [one_mul] using
      affine_indicator_integral (show Fin (d p) from i) word
  · simp only [integral_zero, zero_mul]

include control0 in
/-- Exact original-source replacement-control integral on the literal
accepted-word section. The count uses the original integer reward row. -/
theorem after_replacement_integral (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (i : Fin (p.m - 1))
    (z : Source p) (hz : z ∈ E_after rate rewards C_star C_h q s t i) :
    (∫ u : TimeControl p,
      (if V_after rate rewards C_star C_h i t (replaceSourceControl p t z u)
       then (1 : ℝ) else 0) ∂timeControlLaw p) =
      ((Finset.univ.filter (fun a : Fin p.K => 0 < (rewards t a).val)).card : ℝ) /
        (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ)) := by
  let S := Finset.univ.filter (fun a : Fin p.K => 0 < (rewards t a).val)
  let A : Set (Slice p) := {x |
    PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) ∈ S}
  have hA : MeasurableSet A := by
    exact ((PublicDiscreteDraws.measurable_slotDraw (m := p.m) (K := p.K))
      (measurableSet_singleton _)).inter
      (((PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K)
        (measurableSet_singleton _)).inter
        ((MeasurableSet.of_discrete : MeasurableSet
          {f : OrderedTupleSampler.Tuple p.m p.K |
            f.val (PublicDiscreteDraws.followerPlayer p.two_le_m i) ∈ S}).preimage
          (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K)))
  have hmass : (ContinuousControlSlice.sliceLaw p.m p.K) A =
      ENNReal.ofReal ((S.card : ℝ) / (4 * ((p.m - 1 : ℕ) : ℝ) * p.K)) :=
    scalar_service_probability i S
  have hnonneg : (0 : ℝ) ≤ (S.card : ℝ) / (4 * ((p.m - 1 : ℕ) : ℝ) * p.K) := by positivity
  rw [timeControlLaw, integral_prod _
    (integrable_replacement_observation rate rewards C_star C_h i t z)]
  have hinner (x : Slice p) := affine_first_replacement_integral
    rate rewards C_star C_h control0 q t s hs i z hz x
  simp_rw [hinner]
  have hindicator : (fun x : Slice p =>
      if PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val then (1 : ℝ) else 0) =
      A.indicator 1 := by
    funext x
    simp only [A, S, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  rw [integral_mul_const, hindicator, integral_indicator_one hA, Measure.real, hmass,
    ENNReal.toReal_ofReal hnonneg]
  dsimp only [S]
  ring

/-- P7: the accepted-word service law on the whole original source, at the
fixed original boundary and reward table. This supplies no stopped cost bound. -/
theorem after_service_condExp (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (i : Fin (p.m - 1)) :
    mu[(fun z =>
      (if z ∈ E_after rate rewards C_star C_h q s t i then (1 : ℝ) else 0) *
      (if V_after rate rewards C_star C_h i t z then (1 : ℝ) else 0)) |
      H (t.val + 1)] =ᵐ[mu] fun z =>
        (if z ∈ E_after rate rewards C_star C_h q s t i then (1 : ℝ) else 0) *
        (((Finset.univ.filter (fun a : Fin p.K => 0 < (rewards t a).val)).card : ℝ) /
          (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))) := by
  have hraw := after_confirmation_condExp_integral
    rate rewards C_star C_h control0 q t s hs i
  filter_upwards [hraw] with z hz
  rw [hz]
  by_cases hE : z ∈ E_after rate rewards C_star C_h q s t i
  · rw [ite_eq_left hE, one_mul, one_mul]
    exact after_replacement_integral rate rewards C_star C_h control0 q t s hs i
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
      ((E_after_sourcePrefix rate rewards C_star C_h control0 q s t hs i z).mp hE)
  · simp only [hE, ite_false, zero_mul]

end Context

end Bandits.Support.ReferenceFirstLiveHandoverConfirmationService

end
