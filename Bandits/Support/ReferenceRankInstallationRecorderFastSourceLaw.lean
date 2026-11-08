/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceRankInstallationRecorderFastLaw

/-!
# Original-source history and recorder/FAST cylinder at rank installation

The optional recorder and reserved FAST readouts are evaluated on the original
source reconstructed from the complete physical history, its entire current
assignment vector, and the original control remainder. The event cylinder is
proved under the original source-input law.

Source evidence: ZIP4 `06_interruptions.tex:381-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceRankInstallationRecorderFoundation

namespace Bandits.Support.ReferenceRankInstallationRecorderFastSourceLaw

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

attribute [local instance]
  ReferenceRankInstallationRecorderFoundation.sourceInputMeasurableSpace
  ReferenceRankInstallationRecorderFoundation.optionMeasurableSpace
  ReferenceRankInstallationRecorderFoundation.optionSingleton
  ReferenceRankInstallationRecorderFoundation.outcomeMeasurableSpace
  ReferenceRankInstallationRecorderFoundation.outcomeDiscreteMeasurableSpace
  ReferenceRankInstallationRecorderFoundation.outcomeOptionMeasurableSpace
  ReferenceRankInstallationRecorderFastLaw.reservedMarkerMeasurableSpace

local instance outputSingleton : MeasurableSingletonClass
    (Option (Option (Fin p.K)) × Option (Fin p.K)) := by
  constructor
  intro q
  have hleft : MeasurableSet ({q.1} : Set (Option (Option (Fin p.K)))) :=
    measurableSet_singleton q.1
  have hright : MeasurableSet ({q.2} : Set (Option (Fin p.K))) :=
    measurableSet_singleton q.2
  have heq : ({q} : Set (Option (Option (Fin p.K)) × Option (Fin p.K))) =
      {q.1} ×ˢ {q.2} := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_prod, Prod.ext_iff]
  rw [heq]
  exact hleft.prod hright

abbrev OriginalSource (p : ConstructorDimensions.Parameters) :=
  ReferenceRankInstallationRecorderFoundation.SourceInput p
abbrev InstallationHistory (p : ConstructorDimensions.Parameters) :=
  ReferenceRankInstallationRecorderFoundation.History p
abbrev CurrentAssignmentVector (p : ConstructorDimensions.Parameters) :=
  ReferenceRankInstallationRecorderFoundation.AssignmentVector p
abbrev OriginalControlRemainder (p : ConstructorDimensions.Parameters) :=
  ReferenceLaterOptionalControlResampling.ControlRemainder p
abbrev RecorderFastOutput (p : ConstructorDimensions.Parameters) :=
  Option (Option (Fin p.K)) × Option (Fin p.K)
local notation "installEvent" =>
  ReferenceRankInstallationRecorderFoundation.installationEvent rate rewards C_star C_h
local notation "historyAt" =>
  ReferenceRankInstallationRecorderFoundation.history rate rewards C_star C_h
local notation "currentControl" =>
  ReferenceSourceCurrentControlFreshness.u_t p
local notation "actualPair" =>
  ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast rate rewards C_star C_h

/-- Restore the literal source prefix and the whole current assignment vector,
with every original non-assignment scalar and affine coordinate supplied by
the unreduced control remainder. -/
def sourceFromHistoryRemainder (t : Fin p.T) (h : InstallationHistory p)
    (d : OriginalControlRemainder p) : OriginalSource p :=
  ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t h.1
    ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
      (h.2.2, d))

/-- The original optional recorder/reserved-FAST pair evaluated on the
reconstructed original source. -/
def actualPairFromHistoryRemainder (t : Fin p.T) (h : InstallationHistory p)
    (d : OriginalControlRemainder p) : RecorderFastOutput p :=
  ReferenceRankInstallationRecorderFastLaw.actualMarkerReservedFast
    rate rewards C_star C_h t (sourceFromHistoryRemainder t h d)

/-- The actual finite output coefficient is the original remainder-law mass of
one literal reconstructed pair outcome. -/
def sourceLawCoefficient (t : Fin p.T) (h : InstallationHistory p)
    (y : RecorderFastOutput p) : ENNReal :=
  ∫⁻ d, if actualPairFromHistoryRemainder rate rewards C_star C_h t h d = y
    then 1 else 0 ∂(ReferenceLaterOptionalControlResampling.controlRemainderLaw p)

theorem measurable_sourceFromHistoryRemainder (t : Fin p.T) :
    Measurable (fun q : InstallationHistory p × OriginalControlRemainder p =>
      sourceFromHistoryRemainder t q.1 q.2) := by
  have hc : Measurable (fun q : InstallationHistory p × OriginalControlRemainder p =>
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
        (q.1.2.2, q.2)) :=
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm.measurable.comp
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  exact (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
    ((measurable_fst.comp measurable_fst).prodMk hc)

theorem measurable_actualPairFromHistoryRemainder (t : Fin p.T) :
    Measurable (fun q : InstallationHistory p × OriginalControlRemainder p =>
      actualPairFromHistoryRemainder rate rewards C_star C_h t q.1 q.2) :=
  (ReferenceRankInstallationRecorderFastLaw.measurable_actualMarkerReservedFast
    rate rewards C_star C_h t).comp
      (measurable_sourceFromHistoryRemainder t)

theorem measurable_sourceLawCoefficient (t : Fin p.T) (y : RecorderFastOutput p) :
    Measurable (fun h : InstallationHistory p =>
      sourceLawCoefficient rate rewards C_star C_h t h y) := by
  let f : InstallationHistory p × OriginalControlRemainder p → ENNReal := fun q =>
    if actualPairFromHistoryRemainder rate rewards C_star C_h t q.1 q.2 = y
    then 1 else 0
  have heq : MeasurableSet {q : InstallationHistory p × OriginalControlRemainder p |
      actualPairFromHistoryRemainder rate rewards C_star C_h t q.1 q.2 = y} := by
    apply measurableSet_eq_fun
    exact measurable_actualPairFromHistoryRemainder rate rewards C_star C_h t
    exact measurable_const
  have hf : Measurable f := Measurable.ite heq measurable_const measurable_const
  change Measurable (fun h : InstallationHistory p =>
    ∫⁻ d, f (h, d) ∂(ReferenceLaterOptionalControlResampling.controlRemainderLaw p))
  exact hf.lintegral_prod_right'

theorem sourceLawCoefficient_nonneg (t : Fin p.T) (h : InstallationHistory p)
    (y : RecorderFastOutput p) :
    0 ≤ sourceLawCoefficient rate rewards C_star C_h t h y :=
  bot_le

theorem sourceLawCoefficient_le_one (t : Fin p.T) (h : InstallationHistory p)
    (y : RecorderFastOutput p) :
    sourceLawCoefficient rate rewards C_star C_h t h y ≤ 1 := by
  unfold sourceLawCoefficient
  calc
    _ ≤ ∫⁻ _ : OriginalControlRemainder p, (1 : ENNReal)
        ∂(ReferenceLaterOptionalControlResampling.controlRemainderLaw p) :=
      lintegral_mono fun _ => by split_ifs <;> norm_num
    _ = 1 := by simp [measure_univ]

theorem sourceLawCoefficient_ne_top (t : Fin p.T) (h : InstallationHistory p)
    (y : RecorderFastOutput p) :
    sourceLawCoefficient rate rewards C_star C_h t h y ≠ ⊤ := by
  exact ne_of_lt (lt_of_le_of_lt
    (sourceLawCoefficient_le_one rate rewards C_star C_h t h y)
    (by norm_num : (1 : ENNReal) < ⊤))

/-- The requested history paired with the complete remainder of the original
current control. -/
def historyRemainderMap (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : OriginalSource p) : InstallationHistory p × OriginalControlRemainder p :=
  (historyAt control0 k t z,
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
      (currentControl t z)).2)

theorem measurable_historyRemainderMap (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) :
    Measurable (historyRemainderMap rate rewards C_star C_h control0 k t) := by
  exact (ReferenceRankInstallationRecorderFoundation.measurable_history
      rate rewards C_star C_h control0 k t).prodMk
    (measurable_snd.comp
      ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).measurable.comp
        (ReferenceSourceCurrentControlFreshness.measurable_u_t t)))

/-- Reconstruct the history/remainder product using the public installation
cylinder and history factorization. The strict source prefix and complete
assignment vector remain in the history, and all other remainder factors are
retained. -/
theorem installationEvent_history_remainder_product (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) :
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)).map
        (historyRemainderMap rate rewards C_star C_h control0 k t) =
      (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)).map
        (historyAt control0 k t)).prod
          (ReferenceLaterOptionalControlResampling.controlRemainderLaw p) := by
  let E := installEvent k t
  let μ := (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict E
  let P := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
  let U := fun z : OriginalSource p =>
    LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p (currentControl t z)
  let F := fun z : OriginalSource p => (P z, U z)
  let V := ContinuousControlSlice.assignmentLaw p.K
  let R := ReferenceLaterOptionalControlResampling.controlRemainderLaw p
  let H := historyAt control0 k t
  let h := ReferenceRankInstallationRecorderFoundation.prefixVectorHistory
    rate rewards C_star C_h control0 t
  let G := fun q : OriginalSource p ×
      (CurrentAssignmentVector p × OriginalControlRemainder p) =>
    (h (q.1, q.2.1), q.2.2)
  have hp : Measurable P :=
    ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 t.val
  have hu : Measurable U :=
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).measurable.comp
    (ReferenceSourceCurrentControlFreshness.measurable_u_t t)
  have hf : Measurable F := hp.prodMk hu
  have hh : Measurable h :=
    ReferenceRankInstallationRecorderFoundation.measurable_prefixVectorHistory
      rate rewards C_star C_h control0 t
  have hg : Measurable G := (hh.comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have hH : Measurable H :=
    ReferenceRankInstallationRecorderFoundation.measurable_history
      rate rewards C_star C_h control0 k t
  have hsplit : μ.map F = (μ.map P).prod (V.prod R) := by
    apply Measure.ext_prod
    intro A C hA hC
    rw [Measure.map_apply hf (hA.prod hC), Measure.prod_prod,
      Measure.map_apply hp hA,
      Measure.restrict_apply ((hA.prod hC).preimage hf),
      Measure.restrict_apply (hA.preimage hp)]
    have hpast : MeasurableSet[
        ReferenceSourceCurrentControlFreshness.m_t p control0 t] (P ⁻¹' A) := by
      have hct : ReferenceSourceCurrentControlFreshness.c_t p control0 t = P :=
        funext (ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t)
      change MeasurableSet[(inferInstance : MeasurableSpace (OriginalSource p)).comap
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t)] (P ⁻¹' A)
      rw [hct]
      exact hA.preimage (comap_measurable P)
    have hs := ReferenceRankInstallationRecorderFoundation.installation_controlSplit_cylinder
      rate rewards C_star C_h control0 k t (P ⁻¹' A) hpast C hC
    have he1 : F ⁻¹' (A ×ˢ C) ∩ E =
        {z | z ∈ E ∧ z ∈ P ⁻¹' A} ∩ U ⁻¹' C := by
      ext z
      change ((P z ∈ A ∧ U z ∈ C) ∧ z ∈ E) ↔
        ((z ∈ E ∧ P z ∈ A) ∧ U z ∈ C)
      exact ⟨fun ⟨⟨ha, hc⟩, he⟩ => ⟨⟨he, ha⟩, hc⟩,
        fun ⟨⟨he, ha⟩, hc⟩ => ⟨⟨ha, hc⟩, he⟩⟩
    have he2 : P ⁻¹' A ∩ E = {z | z ∈ E ∧ z ∈ P ⁻¹' A} := by
      ext z
      exact and_comm
    rw [he1, he2]
    exact hs
  have hgraph : μ.map (fun z => (H z, (U z).2)) =
      (((μ.map P).prod V).map h).prod R := by
    calc
      _ = (μ.map F).map G := by
        rw [Measure.map_map hg hf]
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem
          (ReferenceRankInstallationRecorderFoundation.measurableSet_installationEvent
            rate rewards C_star C_h control0 k t)] with z hz
        exact congrArg (fun x => (x, (U z).2))
          (ReferenceRankInstallationRecorderFoundation.history_eq_prefixVectorHistory_of_installation
            rate rewards C_star C_h control0 k t z hz)
      _ = _ := by
        rw [hsplit, ← (measurePreserving_prodAssoc (μ.map P) V R).map_eq,
          Measure.map_map hg (measurePreserving_prodAssoc (μ.map P) V R).measurable]
        change (((μ.map P).prod V).prod R).map (Prod.map h id) = _
        rw [← Measure.map_prod_map _ _ hh measurable_id, Measure.map_id]
  have hmarg := congrArg (Measure.map Prod.fst) hgraph
  rw [Measure.map_map measurable_fst
      (show Measurable (fun z => (H z, (U z).2)) from
        hH.prodMk (measurable_snd.comp hu)),
    Measure.map_fst_prod, measure_univ, one_smul] at hmarg
  change μ.map H = ((μ.map P).prod V).map h at hmarg
  rw [← hmarg] at hgraph
  change μ.map (fun z => (H z, (U z).2)) = (μ.map H).prod R
  exact hgraph

/-- On the literal invocation event, restoring the history prefix, complete
assignment vector, and actual current remainder reproduces the original
optional recorder/FAST pair. -/
theorem actualPair_eq_historyRemainder_of_installation (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : OriginalSource p)
    (hz : z ∈ installEvent k t) :
    actualPair t z = actualPairFromHistoryRemainder rate rewards C_star C_h t
      (historyAt control0 k t z)
      ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        (currentControl t z)).2) := by
  let vector := ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z
  let remainder :=
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p (currentControl t z)).2
  let c := (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
    (vector, remainder)
  have hsplit : LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
      (currentControl t z) = (vector, remainder) := by
    apply Prod.ext
    · rfl
    · rfl
  have hc : c = currentControl t z := by
    apply (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).injective
    dsimp only [c]
    rw [(LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).apply_symm_apply]
    exact hsplit.symm
  have hvector : ContinuousControlSlice.assignmentVector c.1 = vector := by
    rw [hc]
    rfl
  have hreplace :=
    ReferenceRankInstallationRecorderFastLaw.installationEvent_remainder_view_invariant
      rate rewards C_star C_h control0 k t z hz c hvector
  have hsource :
      sourceFromHistoryRemainder t (historyAt control0 k t z) remainder =
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
          (currentControl t z) := by
    change ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (historyAt control0 k t z).1
        ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
          ((historyAt control0 k t z).2.2, remainder)) = _
    rw [show (historyAt control0 k t z).1 =
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z by rfl,
      show (historyAt control0 k t z).2.2 = vector by rfl]
    rw [← hsplit]
    exact congrArg
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z))
      ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm_apply_apply
        (currentControl t z))
  obtain ⟨v, valid, hv, _, _, _⟩ :=
    ReferenceRankInstallationRecorderFastLaw.installationEvent_actualReservedFast_pair
      rate rewards C_star C_h control0 k t z hz
  have hv' : ReferenceRankInstallationRecorderFoundation.actualInstallationView
      rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
          (currentControl t z)) = some v := by
    rw [← hc]
    exact hreplace.2.trans hv
  have hcurrent : currentControl t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
        (currentControl t z)) = currentControl t z := by
    simp only [ReferenceSourceCurrentControlFreshness.u_t,
      ActualInitializationPhysicalStep.selectedRowIndex,
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_private]
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected]
    simp only [ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
  have hfast : ReferenceRankInstallationRecorderFastLaw.actualReservedFast
      rate rewards C_star C_h t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
        (currentControl t z)) =
      ReferenceRankInstallationRecorderFastLaw.actualReservedFast
        rate rewards C_star C_h t z := by
    rw [ReferenceRankInstallationRecorderFastLaw.actualReservedFast_eq_of_view
        rate rewards C_star C_h t z v hv valid,
      ReferenceRankInstallationRecorderFastLaw.actualReservedFast_eq_of_view
        rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
          (currentControl t z)) v hv'
        (ReferenceRankInstallationRecorderFastLaw.actualInstallationView_valid
          rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
            (currentControl t z)) v hv'), hcurrent]
  change actualPair t z = actualPair t
    (sourceFromHistoryRemainder t (historyAt control0 k t z) remainder)
  rw [hsource]
  apply Prod.ext
  · exact (ReferenceRankInstallationRecorderFoundation.actualMarker_restore_of_installation
      rate rewards C_star C_h control0 k t z hz).symm
  · exact hfast.symm

/-- The history together with the original optional recorder/reserved-FAST
readout. -/
def historyPairMap (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : OriginalSource p) : InstallationHistory p × RecorderFastOutput p :=
  (historyAt control0 k t z, actualPair t z)

/-- The pair read from a history and the unreduced original control remainder. -/
def historyRemainderPairMap (t : Fin p.T)
    (q : InstallationHistory p × OriginalControlRemainder p) :
    InstallationHistory p × RecorderFastOutput p :=
  (q.1, actualPairFromHistoryRemainder rate rewards C_star C_h t q.1 q.2)

theorem measurable_historyRemainderPairMap (t : Fin p.T) :
    Measurable (historyRemainderPairMap rate rewards C_star C_h t) :=
  measurable_fst.prodMk
    (measurable_actualPairFromHistoryRemainder rate rewards C_star C_h t)

/-- The original-source history/pair map is exactly the pushforward of the
public history/remainder product under the literal reconstructed pair map. -/
theorem installationEvent_historyPair_joint_pushforward (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) :
    ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
      (installEvent k t)).map (historyPairMap rate rewards C_star C_h control0 k t) =
      (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (installEvent k t)).map (historyAt control0 k t) |>.prod
        (ReferenceLaterOptionalControlResampling.controlRemainderLaw p)).map
          (historyRemainderPairMap rate rewards C_star C_h t) := by
  let μ := (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (installEvent k t)
  let W := historyRemainderMap rate rewards C_star C_h control0 k t
  let G := historyRemainderPairMap rate rewards C_star C_h t
  have hW : Measurable W := measurable_historyRemainderMap rate rewards C_star C_h control0 k t
  have hG : Measurable G := measurable_historyRemainderPairMap rate rewards C_star C_h t
  calc
    μ.map (historyPairMap rate rewards C_star C_h control0 k t) =
        μ.map (fun z => G (W z)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem
        (ReferenceRankInstallationRecorderFoundation.measurableSet_installationEvent
          rate rewards C_star C_h control0 k t)] with z hz
      change (historyAt control0 k t z, actualPair t z) =
        (historyAt control0 k t z,
          actualPairFromHistoryRemainder rate rewards C_star C_h t
            (historyAt control0 k t z)
            ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
              (currentControl t z)).2))
      exact congrArg (Prod.mk (historyAt control0 k t z))
        (actualPair_eq_historyRemainder_of_installation rate rewards C_star C_h
          control0 k t z hz)
    _ = (μ.map W).map G := by
      change μ.map (G ∘ W) = _
      rw [Measure.map_map hG hW]
    _ = _ := by
      rw [installationEvent_history_remainder_product rate rewards C_star C_h control0 k t]

/-- The finite-output test coefficient is computed by integrating the literal
original optional pair over the complete original control-remainder law. -/
def sourceLawTestCoefficient (t : Fin p.T) (h : InstallationHistory p)
    (B : Set (RecorderFastOutput p)) : ENNReal := by
  classical
  exact ∫⁻ d, if actualPairFromHistoryRemainder rate rewards C_star C_h t h d ∈ B
    then 1 else 0 ∂(ReferenceLaterOptionalControlResampling.controlRemainderLaw p)

theorem measurable_sourceLawTestCoefficient (t : Fin p.T)
    (B : Set (RecorderFastOutput p)) (hB : MeasurableSet B) :
    Measurable (fun h : InstallationHistory p =>
      sourceLawTestCoefficient rate rewards C_star C_h t h B) := by
  classical
  let f : InstallationHistory p × OriginalControlRemainder p → ENNReal := fun q =>
    if actualPairFromHistoryRemainder rate rewards C_star C_h t q.1 q.2 ∈ B
    then 1 else 0
  have hpre : MeasurableSet {q : InstallationHistory p × OriginalControlRemainder p |
      actualPairFromHistoryRemainder rate rewards C_star C_h t q.1 q.2 ∈ B} :=
    hB.preimage (measurable_actualPairFromHistoryRemainder rate rewards C_star C_h t)
  have hf : Measurable f := Measurable.ite hpre measurable_const measurable_const
  change Measurable (fun h : InstallationHistory p =>
    ∫⁻ d, f (h, d) ∂(ReferenceLaterOptionalControlResampling.controlRemainderLaw p))
  exact hf.lintegral_prod_right'

theorem sourceLawTestCoefficient_nonneg (t : Fin p.T)
    (h : InstallationHistory p) (B : Set (RecorderFastOutput p)) :
    0 ≤ sourceLawTestCoefficient rate rewards C_star C_h t h B := bot_le

theorem sourceLawTestCoefficient_le_one (t : Fin p.T)
    (h : InstallationHistory p) (B : Set (RecorderFastOutput p)) :
    sourceLawTestCoefficient rate rewards C_star C_h t h B ≤ 1 := by
  unfold sourceLawTestCoefficient
  calc
    _ ≤ ∫⁻ _ : OriginalControlRemainder p, (1 : ENNReal)
        ∂(ReferenceLaterOptionalControlResampling.controlRemainderLaw p) :=
      lintegral_mono fun _ => by split_ifs <;> norm_num
    _ = 1 := by simp [measure_univ]

theorem sourceLawTestCoefficient_ne_top (t : Fin p.T)
    (h : InstallationHistory p) (B : Set (RecorderFastOutput p)) :
    sourceLawTestCoefficient rate rewards C_star C_h t h B ≠ ⊤ := by
  exact ne_of_lt (lt_of_le_of_lt
    (sourceLawTestCoefficient_le_one rate rewards C_star C_h t h B)
    (by norm_num : (1 : ENNReal) < ⊤))

/-- Arbitrary Borel history tests and finite recorder/FAST output tests obey
the original installation-event cylinder under the same numerical source law.
No success, history, output-law, or coupling premise is assumed. -/
theorem installationEvent_history_output_cylinder (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (A : Set (InstallationHistory p))
    (B : Set (RecorderFastOutput p)) (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
      (installEvent k t)).map
      (historyPairMap rate rewards C_star C_h control0 k t)) (A ×ˢ B) =
      ∫⁻ h in A, sourceLawTestCoefficient rate rewards C_star C_h t h B ∂
        (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
          (installEvent k t)).map (historyAt control0 k t)) := by
  classical
  let ν := ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
    (installEvent k t)).map (historyAt control0 k t)
  let R := ReferenceLaterOptionalControlResampling.controlRemainderLaw p
  let G := historyRemainderPairMap rate rewards C_star C_h t
  have hG : Measurable G := measurable_historyRemainderPairMap rate rewards C_star C_h t
  have hAB : MeasurableSet (A ×ˢ B) := hA.prod hB
  have hpre : MeasurableSet (G ⁻¹' (A ×ˢ B)) := hAB.preimage hG
  let f : InstallationHistory p × OriginalControlRemainder p → ENNReal := fun q =>
    if q ∈ G ⁻¹' (A ×ˢ B) then (1 : ENNReal) else 0
  have hf : Measurable f := Measurable.ite hpre measurable_const measurable_const
  calc
    _ = (ν.prod R) (G ⁻¹' (A ×ˢ B)) := by
      rw [installationEvent_historyPair_joint_pushforward rate rewards C_star C_h
        control0 k t, Measure.map_apply hG hAB]
    _ = ∫⁻ q, f q ∂(ν.prod R) := by
      simpa [f, Set.indicator_apply] using (lintegral_indicator_one hpre).symm
    _ = ∫⁻ h, ∫⁻ d, f (h, d) ∂R ∂ν :=
      lintegral_prod f hf.aemeasurable
    _ = ∫⁻ h, if h ∈ A then sourceLawTestCoefficient rate rewards C_star C_h t h B
          else 0 ∂ν := by
      apply lintegral_congr
      intro h
      by_cases ha : h ∈ A
      · simp [f, G, historyRemainderPairMap, ha, sourceLawTestCoefficient, R]
      · simp [f, G, historyRemainderPairMap, ha]
    _ = ∫⁻ h in A, sourceLawTestCoefficient rate rewards C_star C_h t h B ∂ν := by
      rw [← lintegral_indicator hA]
      apply lintegral_congr
      intro h
      by_cases ha : h ∈ A <;> simp [ha]

/-- The actual optional pair on the invocation event has a present outer
marker and a present reserved FAST arm. The inner marker option is retained,
so a present bottom marker remains distinct from outer absence. -/
theorem installationEvent_actual_optional_pair_shape (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : OriginalSource p)
    (hz : z ∈ installEvent k t) :
    ∃ (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
      (valid : CoordinatorLocalArmChoice.ChoiceInputsValid
        v.payload v.cutoff t v.complementWeights),
      ReferenceRankInstallationRecorderFoundation.actualInstallationView
        rate rewards C_star C_h t z = some v ∧
      actualPair t z =
        (some (ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
          rate t v valid ((currentControl t z).1)).1,
         some (ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
          rate t v valid ((currentControl t z).1)).2) :=
  ReferenceRankInstallationRecorderFastLaw.installationEvent_actualMarkerReservedFast
    rate rewards C_star C_h control0 k t z hz

/-- On the actual invocation event, outer marker absence and reserved-FAST
absence are each impossible, without conditioning on a later output. -/
theorem installationEvent_actual_optional_pair_outer_presence (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : OriginalSource p)
    (hz : z ∈ installEvent k t) :
    (actualPair t z).1 ≠ none ∧ (actualPair t z).2 ≠ none := by
  obtain ⟨v, valid, hview, hpair⟩ :=
    installationEvent_actual_optional_pair_shape rate rewards C_star C_h control0 k t z hz
  constructor
  · rw [hpair]
    exact Option.some_ne_none _
  · rw [hpair]
    exact Option.some_ne_none _

/-- If the same-slice recorder outcome is bottom, the source output is the
present-bottom marker `some none`, not outer marker absence. -/
theorem installationEvent_present_bottom_marker (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : OriginalSource p)
    (hz : z ∈ installEvent k t) :
    ∃ v : ReferenceDownReception.ChoiceTimeView p rate.eta,
      ∃ valid : CoordinatorLocalArmChoice.ChoiceInputsValid
        v.payload v.cutoff t v.complementWeights,
      ReferenceRankInstallationRecorderFoundation.actualInstallationView
        rate rewards C_star C_h t z = some v ∧
      ((ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
          rate t v valid ((currentControl t z).1)).1 = none →
        (actualPair t z).1 = some none) := by
  obtain ⟨v, valid, hview, hpair⟩ :=
    installationEvent_actual_optional_pair_shape rate rewards C_star C_h control0 k t z hz
  refine ⟨v, valid, hview, ?_⟩
  intro hbottom
  rw [hpair, hbottom]

/-- At an actual installation, the unreduced remainder gives the correlated
same-slice recorder/reserved-FAST kernel. -/
theorem installationEvent_original_remainder_joint_kernel (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : OriginalSource p)
    (hz : z ∈ installEvent k t) :
    ∃ v : ReferenceDownReception.ChoiceTimeView p rate.eta,
      ∃ valid : CoordinatorLocalArmChoice.ChoiceInputsValid
        v.payload v.cutoff t v.complementWeights,
      ReferenceRankInstallationRecorderFoundation.actualInstallationView
        rate rewards C_star C_h t z = some v ∧
      ReferenceRankInstallationRecorderFoundation.viewFromHistory
        rate rewards C_star C_h control0 t
        (ReferenceRankInstallationRecorderFoundation.history
          rate rewards C_star C_h control0 k t z) = some v ∧
      (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
        (fun d => ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
          rate t v valid
          ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm
            (ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z, d.1))) =
      (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val
        rate.eta.property rate.sourceCap v.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights)
        v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
          v.complementWeights v.cutoff t valid)
        v.payload.assignment
        (ReferenceRankInstallationRecorderFoundation.installationSnapshot
          v.payload.assignment)).map (fun q => (q.1, q.2.1)) :=
  ReferenceRankInstallationRecorderFastLaw.installationEvent_actualRemainder_joint_pushforward
    rate rewards C_star C_h control0 k t z hz

/-- The reserved FAST marginal on the actual fast complement is the original
numerical `qGamma` marginal, with all replay weights and local validity
derived from the actual installation record. -/
theorem installationEvent_original_remainder_qGamma (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : OriginalSource p)
    (hz : z ∈ installEvent k t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length) (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
      (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
        v.complementWeights),
      (∀ j : CanonicalFastSampling.FastArm v.payload.slowSet,
        v.complementWeights j = AssignmentScoreReconstruction.sourceWeightBase p ^
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L j.1 b.val).1) ∧
      (∀ hweights : ∀ j : CanonicalFastSampling.FastArm v.payload.slowSet,
        v.complementWeights j = AssignmentScoreReconstruction.sourceWeightBase p ^
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L j.1 b.val).1,
       ∀ j : CanonicalFastSampling.FastArm v.payload.slowSet,
        CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property
            valid.learning_rate_le_source_cap v.payload.anchor
            (ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights)
            v.payload.anchor_pos
            (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
              v.complementWeights v.cutoff t valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
              v.complementWeights v.cutoff t valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
              v.complementWeights v.cutoff t valid) v.payload.slowSet j =
          FastComplementLocality.localFastLaw p rate.eta.val rate.eta.property
            valid.learning_rate_le_source_cap v.payload.anchor v.payload.slowSet
            (fun j => AssignmentScoreReconstruction.sourceWeightBase p ^
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L
                j.1 b.val).1)
            v.payload.anchor_pos
            (fun j => by rw [← hweights j]; exact valid.current_weight_pos j)
            (fun j => by rw [← hweights j]; exact valid.anchor_le_current j)
            (fun j => by rw [← hweights j]; exact valid.current_le_twice_anchor j)
            j) :=
  ReferenceRankInstallationRecorderFastLaw.installationEvent_originalComplement_qGamma_eq_localFastLaw
    rate rewards C_star C_h control0 k t z hz

/-- The original numerical complement weights also give the accepted qGamma
pushforward for the same actual reserved FAST readout on a continuous slice. -/
theorem installationEvent_original_numerical_FAST_marginal (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : OriginalSource p)
    (hz : z ∈ installEvent k t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length)
      (v : ReferenceDownReception.ChoiceTimeView p rate.eta)
      (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
        v.complementWeights),
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h p.T z = some L ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val] ∧
      ReferenceRankInstallationRecorderFoundation.actualInstallationView
        rate rewards C_star C_h t z = some v ∧
      (ContinuousControlSlice.sliceLaw p.m p.K).map
        (ReferenceRankInstallationRecorderFastLaw.reservedFastAtView rate t v valid) =
        (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property
          rate.sourceCap v.payload.anchor
          (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
            v.complementWeights)
          v.payload.anchor_pos
          (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
            v.complementWeights v.cutoff t valid) v.payload.slowSet).toMeasure ∧
      ∀ j : CanonicalFastSampling.FastArm v.payload.slowSet,
        ReferenceFirstWindowNumericalStream.sourceWeights v.payload
          v.complementWeights j.1 = AssignmentScoreReconstruction.sourceWeightBase p ^
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L
              j.1 b.val).1 :=
  ReferenceRankInstallationRecorderFastLaw.installationEvent_originalNumericalFastMarginal
    rate rewards C_star C_h control0 k t z hz

end Bandits.Support.ReferenceRankInstallationRecorderFastSourceLaw

end
