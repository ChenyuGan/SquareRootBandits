/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveHandoverBoundaryFactorization
public import Bandits.Support.ReferenceFirstLiveHandoverDownFeedback
public import Bandits.Support.DownServiceProbability

/-!
# Actual first-handover service before DOWN acceptance

The section and observation are the literal `E_before` and `V_before` of
`ReferenceFirstLiveHandoverBoundaryFactorization`. Current controls are replaced
on the original source. In particular, the FIRST installation uses its current
assignment coordinates; its outgoing word is fixed only after fixing the scalar
slice, before integrating the independent affine family.

Sources: ZIP4 `05_binary_transport.tex:253-275`,
`06_interruptions.tex:246-299,431-490`, and
`appendix_a_local_protocol.tex:100-108,141-157`.
These are internal section laws for the later stopped handover consumer.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceFirstLiveHandoverBoundaryFactorization
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open scoped Classical ENNReal

namespace Bandits.Support.ReferenceFirstLiveHandoverBeforeDownService

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)

local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "H" => ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0

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
theorem E_before_replaceSourceControl (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (i : Fin (p.m - 1))
    (z : Source p) (u : TimeControl p) :
    replaceSourceControl p t z u ∈ E_before rate rewards C_star C_h q s t i ↔
      z ∈ E_before rate rewards C_star C_h q s t i := by
  rw [E_before_sourcePrefix rate rewards C_star C_h control0 q s t hs,
    prefix_replace control0,
    ← E_before_sourcePrefix rate rewards C_star C_h control0 q s t hs]

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
    (z : Source p) (hz : z ∈ E_before rate rewards C_star C_h q s t i)
    (u : TimeControl p) :
    ∃ (r : Record (p := p) (rate := rate)) (selected : Selection (rate := rate) r),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
        (replaceSourceControl p t z u) = some r ∧
      r ∈ firstWindow rate rewards C_star C_h (replaceSourceControl p t z u) ∧
      r.output.preparation.coordinator.selection = some selected ∧
      i ∈ selected.view.pendingAtChoice ∧ Before (rate := rate) r i ∧
      r.input.row.2 t = u := by
  have hu := (E_before_replaceSourceControl rate rewards C_star C_h control0
    q t s hs i z u).mpr hz
  obtain ⟨_, _, _, _, r, selected, hr, hW, hsel, hi, hb⟩ := hu
  refine ⟨r, selected, hr, hW, hsel, hi, hb, ?_⟩
  obtain ⟨hrows, hJ, _, _⟩ := actualRecord_fields rate rewards C_star C_h t _ r hr
  simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hJ,
    replaceSourceControl, ActualInitializationPhysicalStep.selectedRowIndex,
    sourceCoordinatorIndex, Function.update_self]

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
    (z : Source p) (hz : z ∈ E_before rate rewards C_star C_h q s t i)
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
  have hE := (E_before_replaceSourceControl rate rewards C_star C_h control0
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
    sourceCoordinatorIndex, Function.update_self]
  exact huv

private theorem observation_iff (t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source p) (r : Record (p := p) (rate := rate))
    (selected : Selection (rate := rate) r)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hW : r ∈ firstWindow rate rewards C_star C_h z)
    (hsel : r.output.preparation.coordinator.selection = some selected)
    (hi : i ∈ selected.view.pendingAtChoice) (hb : Before (rate := rate) r i) :
    V_before rate rewards C_star C_h i t z ↔
      PublicDiscreteDraws.slotDraw (r.input.row.2 t).1 = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 t).1 = i ∧
      0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
        (r.input.row.2 t).1).val (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val ∧
      CoordinatorLocalArmChoice.currentDownHash selected.view.payload (r.input.row.2 t) i = 1 := by
  have ht := (actualRecord_fields rate rewards C_star C_h t z r hr).2.2.1
  have hpos (hd : PublicDiscreteDraws.slotDraw (r.input.row.2 t).1 = PublicDiscreteDraws.downSlot)
      (hf : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 t).1 = i) :
      0 < (r.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val ↔
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (r.input.row.2 t).1).val (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val ∧
        CoordinatorLocalArmChoice.currentDownHash selected.view.payload (r.input.row.2 t) i = 1 := by
    rw [ReferenceFirstLiveHandoverDownFeedback.actual_first_live_before_down_feedback
      rate rewards C_star C_h z t r hr hW selected hsel i hi hd hf hb]
    have hD : (0 : ℝ) < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
    by_cases hbit : CoordinatorLocalArmChoice.currentDownHash selected.view.payload
        (r.input.row.2 t) i = 1 <;>
      simp only [hbit, ite_true, ite_false, RealRewardGridCount.realRewardGridValue,
        div_pos_iff_of_pos_right hD, Nat.cast_pos, and_true, and_false,
        lt_self_iff_false]
  constructor
  · rintro ⟨r', hr', hd, hf, hp⟩
    have heq := Option.some.inj (hr.symm.trans hr')
    subst r'
    rw [ht] at hd hf
    exact ⟨hd, hf, (hpos hd hf).mp hp⟩
  · rintro ⟨hd, hf, hp⟩
    exact ⟨r, hr, ht.symm ▸ hd, ht.symm ▸ hf, (hpos hd hf).mpr hp⟩

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

private theorem affine_indicator_integral (i : Fin (d p))
    (word : AffineChannelLaw.Word (B p)) :
    (∫ a : AffineSamples p,
      (if AffineChannelLaw.affineHash (a (0, i)) word = 1 then (1 : ℝ) else 0)
      ∂affineSamplesLaw p) = 1 / 2 := by
  let A : Set (AffineChannelLaw.Sample (B p)) :=
    {sample | AffineChannelLaw.affineHash sample word = 1}
  have hA : MeasurableSet A := MeasurableSet.of_discrete
  have hpre : MeasurableSet {a : AffineSamples p |
      AffineChannelLaw.affineHash (a (0, i)) word = 1} :=
    hA.preimage (measurable_pi_apply (0, i))
  have hmass : (affineSamplesLaw p)
      {a : AffineSamples p | AffineChannelLaw.affineHash (a (0, i)) word = 1} =
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
      if V_before rate rewards C_star C_h i t (replaceSourceControl p t z u)
      then (1 : ℝ) else 0) (timeControlLaw p) := by
  have hB := measurableSet_B_before rate rewards C_star C_h i t
  have hset : MeasurableSet {u : TimeControl p |
      V_before rate rewards C_star C_h i t (replaceSourceControl p t z u)} :=
    hB.preimage (measurable_const.prodMk measurable_id)
  exact (integrable_const (1 : ℝ)).indicator hset

include control0 in
/-- Integrate the actual affine family first, with the actual word held fixed
only for this scalar slice. The word is produced from an actual replacement
call, and its equality at every other affine family is proved above. -/
theorem affine_first_replacement_integral (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (i : Fin (p.m - 1))
    (z : Source p) (hz : z ∈ E_before rate rewards C_star C_h q s t i)
    (x : Slice p) :
    (∫ a : AffineSamples p,
      (if V_before rate rewards C_star C_h i t (replaceSourceControl p t z (x, a))
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
      (if V_before rate rewards C_star C_h i t (replaceSourceControl p t z (x, a))
       then (1 : ℝ) else 0) =
      (if PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val
       then (if AffineChannelLaw.affineHash (a (0, i)) word = 1 then 1 else 0)
       else 0) := by
    obtain ⟨r, selected, hr, hW, hsel, hi, hb, hcurrent⟩ :=
      replacement_section_witnesses rate rewards C_star C_h control0 q t s hs i z hz (x, a)
    have hpayload := replacement_payload_eq_of_same_slice rate rewards C_star C_h control0
      q t s hs i z hz (x, a) (x, control0.2) rfl
      r r0 selected selected0 hr hr0 hsel hsel0
    rw [observation_iff rate rewards C_star C_h t i _ r selected hr hW hsel hi hb,
      hcurrent, hpayload]
    by_cases hbit : AffineChannelLaw.affineHash (a (0, i)) word = 1 <;>
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
pre-acceptance section. The count uses the original integer reward row. -/
theorem before_replacement_integral (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (i : Fin (p.m - 1))
    (z : Source p) (hz : z ∈ E_before rate rewards C_star C_h q s t i) :
    (∫ u : TimeControl p,
      (if V_before rate rewards C_star C_h i t (replaceSourceControl p t z u)
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

/-- Integrability of the literal physical pre-acceptance observation on the
whole original source. Absent and failed records retain value zero. -/
theorem integrable_before_observation (i : Fin (p.m - 1)) (t : Fin p.T) :
    Integrable (fun z : Source p =>
      if V_before rate rewards C_star C_h i t z then (1 : ℝ) else 0) mu := by
  exact (integrable_const (1 : ℝ)).indicator
    (measurableSet_V_before rate rewards C_star C_h i t)

include control0 in
/-- Integrability of the actual section observation, on the unnormalized
original probability space, including sections of mass zero. -/
theorem integrable_before_section_observation (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (i : Fin (p.m - 1)) :
    Integrable (fun z : Source p =>
      (if z ∈ E_before rate rewards C_star C_h q s t i then (1 : ℝ) else 0) *
      (if V_before rate rewards C_star C_h i t z then (1 : ℝ) else 0)) mu := by
  have hE : MeasurableSet (E_before rate rewards C_star C_h q s t i) :=
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (t.val + 1)) _
      (measurableSet_E_before rate rewards C_star C_h control0 q s t hs i)
  have hint := (integrable_before_observation rate rewards C_star C_h i t).indicator hE
  convert hint using 1
  funext z
  by_cases hz : z ∈ E_before rate rewards C_star C_h q s t i <;>
    simp only [Set.indicator_apply, hz, ite_true, ite_false, one_mul, zero_mul]

/-- P6: the exact before-acceptance service law on the whole original source.
The adapted literal section indicator is pulled through conditional
expectation using F, and the current integral is evaluated affine first.
No stopped-support, quota, waiting-cost, or manuscript-history claim is made. -/
theorem before_service_condExp (q : Fin (M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (i : Fin (p.m - 1)) :
    mu[(fun z =>
      (if z ∈ E_before rate rewards C_star C_h q s t i then (1 : ℝ) else 0) *
      (if V_before rate rewards C_star C_h i t z then (1 : ℝ) else 0)) |
      H (t.val + 1)] =ᵐ[mu] fun z =>
        (if z ∈ E_before rate rewards C_star C_h q s t i then (1 : ℝ) else 0) *
        (((Finset.univ.filter (fun a : Fin p.K => 0 < (rewards t a).val)).card : ℝ) /
          (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))) := by
  have hE := measurableSet_E_before rate rewards C_star C_h control0 q s t hs i
  have hmeas : StronglyMeasurable[H (t.val + 1)] (fun z : Source p =>
      if z ∈ E_before rate rewards C_star C_h q s t i then (1 : ℝ) else 0) :=
    (measurable_const.indicator hE).stronglyMeasurable
  have hpull := condExp_mul_of_stronglyMeasurable_left hmeas
    (integrable_before_section_observation rate rewards C_star C_h control0 q t s hs i)
    (integrable_before_observation rate rewards C_star C_h i t)
  have hraw := V_before_condExp rate rewards C_star C_h control0 i t
  filter_upwards [hpull, hraw] with z hp hr
  change mu[(fun w =>
      (if w ∈ E_before rate rewards C_star C_h q s t i then (1 : ℝ) else 0) *
      (if V_before rate rewards C_star C_h i t w then (1 : ℝ) else 0)) |
      H (t.val + 1)] z =
    (if z ∈ E_before rate rewards C_star C_h q s t i then (1 : ℝ) else 0) *
    mu[(fun w => if V_before rate rewards C_star C_h i t w then (1 : ℝ) else 0) |
      H (t.val + 1)] z at hp
  rw [hp, hr]
  by_cases hz : z ∈ E_before rate rewards C_star C_h q s t i
  · rw [ite_eq_left hz, one_mul, one_mul]
    exact before_replacement_integral rate rewards C_star C_h control0 q t s hs i
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
      ((E_before_sourcePrefix rate rewards C_star C_h control0 q s t hs i z).mp hz)
  · simp only [hz, ite_false, zero_mul]

end Bandits.Support.ReferenceFirstLiveHandoverBeforeDownService

end
