/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionEmptyStreamSuffix
public import Bandits.Support.ReferenceFirstCollectionStagedConditionalService

/-!
# Empty-tail observation for the actual first collection

The physical suffix theorem identifies actual first-collection dates after
the empty stream boundary. At those dates the original global OLD and FORMED
supports are absent and the original staged observation vanishes. The
conditional service result keeps the same dispatch witness and its existing
cutoff and continuing outputs while adding this finite tail.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionEmptyTailObservation

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem not_cutoff_old_of_actual_collection_phase
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hRecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r)
    (hPhase : ReferenceCollectionPhaseHistory.CollectionPhase r.input.state.coordinator) :
    source ∉ ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t := by
  have hNotLive :
      ∀ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
        (base : Fin (p.m - 1) → ℕ),
        r.input.state.coordinator ≠ .live registers owned base := by
    intro registers owned base hLive
    rcases hPhase with hDagger | ⟨payload, ledger, saved, hCollection⟩
    · rw [hDagger] at hLive
      cases hLive
    · rw [hCollection] at hLive
      cases hLive
  intro hSupport
  change source ∈
    ⋃ wD : ReferenceFirstCutoffStageConditionalService.DownWord p,
      ReferenceCutoffStageSupportMeasurability.cutoffDownStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t wD at hSupport
  obtain ⟨wD, hWord⟩ := Set.mem_iUnion.mp hSupport
  change source ∈
    ReferenceCutoffStageSupportMeasurability.cutoffDownStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t wD at hWord
  rcases hWord with ⟨r', hActual, hRest⟩
  rcases hRest with ⟨registers, owned, base, hLive, _⟩
  have hSame : r' = r := Option.some.inj (hActual.symm.trans hRecord)
  rw [hSame] at hLive
  exact hNotLive registers owned base hLive

private theorem not_cutoff_formed_of_actual_collection_phase
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hRecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r)
    (hPhase : ReferenceCollectionPhaseHistory.CollectionPhase r.input.state.coordinator) :
    source ∉ ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t := by
  have hNotLive :
      ∀ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
        (base : Fin (p.m - 1) → ℕ),
        r.input.state.coordinator ≠ .live registers owned base := by
    intro registers owned base hLive
    rcases hPhase with hDagger | ⟨payload, ledger, saved, hCollection⟩
    · rw [hDagger] at hLive
      cases hLive
    · rw [hCollection] at hLive
      cases hLive
  intro hSupport
  change source ∈
    ⋃ U : ReferenceFirstCutoffStageConditionalService.UpRecord p rate,
      ReferenceCutoffStageSupportMeasurability.cutoffUpStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t U at hSupport
  obtain ⟨U, hWord⟩ := Set.mem_iUnion.mp hSupport
  change source ∈
    ReferenceCutoffStageSupportMeasurability.cutoffUpStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t U at hWord
  rcases hWord with ⟨r', hActual, hRest⟩
  rcases hRest with ⟨registers, owned, base, hLive, _⟩
  have hSame : r' = r := Option.some.inj (hActual.symm.trans hRecord)
  rw [hSame] at hLive
  exact hNotLive registers owned base hLive

private theorem not_continuing_down_ready_of_empty_actual_pending
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hRecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r)
    (hEndpoint : ∀ (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool)),
      r.input.state.coordinator = .collection payload ledger saved →
        ledger.pending = ∅) :
    source ∉ ⋃ wD : AffineChannelLaw.Word (AffineBatchDecoder.width p),
      ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport
        (p := p) (rate := rate) rewards C_star C_h i t wD := by
  intro hSupport
  obtain ⟨wD, hDown⟩ := Set.mem_iUnion.mp hSupport
  change ∃ r',
    ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r' ∧
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool))
      (old : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        r'.input payload ledger saved ∧
      i ∈ ledger.pending ∧
      r'.input.state.followers i = .ordinary old memory ∧
      old.lastDown = none ∧
      CoordinatorLocalArmChoice.storedDownFlatWord payload i = wD ∧
      ∀ j : Fin (p.m - 1), r'.input.state.followers j ≠ .dagger at hDown
  rcases hDown with ⟨r', hActual, hRest⟩
  rcases hRest with ⟨payload, ledger, saved, old, memory, hReady, hPending, _⟩
  have hSame : r' = r := Option.some.inj (hActual.symm.trans hRecord)
  rw [hSame] at hReady
  have hCoordinator : r.input.state.coordinator = .collection payload ledger saved :=
    hReady.1
  have hEmpty := hEndpoint payload ledger saved hCoordinator
  rw [hEmpty] at hPending
  simp at hPending

private theorem not_continuing_up_ready_of_empty_actual_pending
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hRecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r)
    (hEndpoint : ∀ (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool)),
      r.input.state.coordinator = .collection payload ledger saved →
        ledger.pending = ∅) :
    source ∉ ⋃ U : ReferenceFirstCollectionStagedConditionalService.UpRecord p rate,
      ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
        (p := p) (rate := rate) rewards C_star C_h i t U := by
  intro hSupport
  obtain ⟨U, hUp⟩ := Set.mem_iUnion.mp hSupport
  change ∃ r',
    ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r' ∧
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool))
      (old : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        r'.input payload ledger saved ∧
      i ∈ ledger.pending ∧
      r'.input.state.followers i = .ordinary old memory ∧
      1 ≤ ReferencePrelaunchFollower.acceptedStart old ∧
      ActiveFollowerQueueOperation.upOfferFields old = U.val ∧
      ∀ j : Fin (p.m - 1), r'.input.state.followers j ≠ .dagger at hUp
  rcases hUp with ⟨r', hActual, hRest⟩
  rcases hRest with ⟨payload, ledger, saved, old, memory, hReady, hPending, _⟩
  have hSame : r' = r := Option.some.inj (hActual.symm.trans hRecord)
  rw [hSame] at hReady
  have hCoordinator : r.input.state.coordinator = .collection payload ledger saved :=
    hReady.1
  have hEmpty := hEndpoint payload ledger saved hCoordinator
  rw [hEmpty] at hPending
  simp at hPending

/-- At each actual physical collection-tail input after the same dispatch's
first empty stream boundary, both original whole-source supports are absent.
This uses the actual suffix record, its CollectionPhase classification, and
the constructor-specific pending-empty conclusion. -/
theorem actual_first_collection_empty_tail_observation
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput
          source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
    let out := d.stream
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ (k : Fin B.length), out.ell ≤ k.val → ∀ i : Fin (p.m - 1),
      source ∉ ReferenceFirstCollectionStagedConditionalService.OLD
        (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time ∧
      source ∉ ReferenceFirstCollectionStagedConditionalService.FORMED
        (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time ∧
      ReferenceFirstCollectionStagedConditionalService.X
        (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time source = 0 := by
  classical
  have hSuffix :=
    ReferenceFirstCollectionEmptyStreamSuffix.actual_first_collection_empty_stream_suffix
      rate source rewards C_star C_h count hcross hspan hshort d
  dsimp only at hSuffix
  obtain ⟨_, _, _, _, _, _, _, _, hTail⟩ := hSuffix
  intro out E w B k hkTail i
  specialize hTail k hkTail
  rcases hTail with ⟨_, _, _, _, _, _, _, hActual, hPhase, hEndpoint⟩

  have hNotCutoffOld := not_cutoff_old_of_actual_collection_phase
    (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time
    (source := source) (r := B[k.val]) hActual hPhase
  have hNotCutoffFormed := not_cutoff_formed_of_actual_collection_phase
    (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time
    (source := source) (r := B[k.val]) hActual hPhase
  have hNotDownReady := not_continuing_down_ready_of_empty_actual_pending
    (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time
    (source := source) (r := B[k.val]) hActual
    (fun payload ledger saved hCoordinator =>
      (hEndpoint payload ledger saved hCoordinator).1)
  have hNotUpReady := not_continuing_up_ready_of_empty_actual_pending
    (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time
    (source := source) (r := B[k.val]) hActual
    (fun payload ledger saved hCoordinator =>
      (hEndpoint payload ledger saved hCoordinator).1)

  have hNotOld :
      source ∉ ReferenceFirstCollectionStagedConditionalService.OLD
        (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time := by
    change source ∉
      ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
        (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time ∪
      ⋃ wD : AffineChannelLaw.Word (AffineBatchDecoder.width p),
        ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport
          (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time wD
    intro hSupport
    rcases hSupport with hCutoff | hDown
    · exact hNotCutoffOld hCutoff
    · exact hNotDownReady hDown

  have hNotFormed :
      source ∉ ReferenceFirstCollectionStagedConditionalService.FORMED
        (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time := by
    change source ∉
      ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
        (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time ∪
      ⋃ U : ReferenceFirstCollectionStagedConditionalService.UpRecord p rate,
        ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
          (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time U
    intro hSupport
    rcases hSupport with hCutoff | hUp
    · exact hNotCutoffFormed hCutoff
    · exact hNotUpReady hUp

  have hXZero :
      ReferenceFirstCollectionStagedConditionalService.X
        (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time source = 0 := by
    simp [ReferenceFirstCollectionStagedConditionalService.X,
      Set.indicator_of_notMem hNotOld, Set.indicator_of_notMem hNotFormed]
  exact ⟨hNotOld, hNotFormed, hXZero⟩

/-- The staged-service result on the original source law, extended over the
physical tail of its own dispatch. The existing cutoff, pending, numerical,
classification, and nonpending outputs are retained verbatim. -/
theorem actual_initialized_first_collection_whole_window_service
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ᵐ source ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      ∀ (count : ℕ)
        (hcross : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
        (hspan : ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
        (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length < count),
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
          (rate := rate) source rewards C_star C_h count hcross hspan hshort,
        let out := d.stream
        let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan
        let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
        let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
        out.window = B ∧
        (∀ i : Fin (p.m - 1),
          ReferenceFirstCollectionStagedConditionalService.X
              (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time source =
            ReferenceFirstCutoffStageConditionalService.stagedReadout
              (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time source ∧
          (BootstrapPrivateRoundStreams.sourceInputLaw p)[
            ReferenceFirstCollectionStagedConditionalService.X
              (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time |
              ReferenceSourceCurrentControlFreshness.m_t p control0
                out.cutoff.cut.input.time] source =
            (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
              rewards out.cutoff.cut.input.time : ℝ) /
              (8 * (p.m - 1 : ℝ) * p.K)) ∧
        (∀ (n : Fin out.ell), 0 < n.val →
          ∀ i : Fin (p.m - 1),
            i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
            ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
              (incoming : ReferenceActivePhysicalStep.Ledger rate)
              (old : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
              out.window[n.val]? = some r ∧
              r.input.time.val + 1 =
                ReferenceInitializationRun.elapsed p
                  (ReferenceInitializationRun.output
                    (ActualReferenceInitializationBlock.referenceInput
                      source rewards C_star C_h rate)).completed + w + 1 + n.val ∧
              r.input.rows = source.1.2 ∧
              r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
              r.input.rewards = rewards ∧
              incoming = out.ledgers ⟨n.val - 1, by omega⟩ ∧
              i ∈ incoming.pending ∧
              ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                r.input out.payload incoming out.saved ∧
              r.input.state.followers i = .ordinary old memory ∧
              old.status = .unoccupied ∧
              ActiveFollowerLifecycle.localStateDomainValid old ∧
              ((old.lastDown = none ∧ old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0) ∨
                old.lastDown = some (out.payload.downRecord i)) ∧
              (old.lastDown = some (out.payload.downRecord i) →
                ∃ U : ReferenceFirstCollectionStagedConditionalService.UpRecord p rate,
                  U.val = ActiveFollowerQueueOperation.upOfferFields old ∧
                  1 ≤ U.val.sigma) ∧
              (source ∈ ReferenceFirstCollectionStagedConditionalService.OLD
                  (p := p) (rate := rate) rewards C_star C_h i r.input.time ↔
                old.lastDown = none) ∧
              (source ∈ ReferenceFirstCollectionStagedConditionalService.FORMED
                  (p := p) (rate := rate) rewards C_star C_h i r.input.time ↔
                old.lastDown ≠ none) ∧
              (old.lastDown = none →
                ReferenceFirstCollectionStagedConditionalService.X
                    (p := p) (rate := rate) rewards C_star C_h i r.input.time source =
                  if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                      (r.input.row.2 r.input.time).1 =
                        ReferenceFirstCollectionUpConditionalService.followerIndex i ∧
                    ReferenceActiveAffinePositiveTest.downPositive r.input = true then 1 else 0) ∧
              (old.lastDown ≠ none →
                ReferenceFirstCollectionStagedConditionalService.X
                    (p := p) (rate := rate) rewards C_star C_h i r.input.time source =
                  if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                      (r.input.row.2 r.input.time).1 =
                        ReferenceFirstCollectionUpConditionalService.followerIndex i ∧
                    ReferenceActiveAffinePositiveTest.upPositive r.input = true then 1 else 0) ∧
              (BootstrapPrivateRoundStreams.sourceInputLaw p)[
                ReferenceFirstCollectionStagedConditionalService.X
                    (p := p) (rate := rate) rewards C_star C_h i r.input.time |
                  ReferenceSourceCurrentControlFreshness.m_t p control0 r.input.time] source =
                (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
                  rewards r.input.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K)) ∧
        (∀ (n : Fin out.ell), 0 < n.val →
          ∀ i : Fin (p.m - 1),
            i ∉ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
            ReferenceFirstCollectionStagedConditionalService.X
              (p := p) (rate := rate) rewards C_star C_h i
              (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.time source = 0) ∧
        (∀ (k : Fin B.length), out.ell ≤ k.val →
          ∀ i : Fin (p.m - 1),
            source ∉ ReferenceFirstCollectionStagedConditionalService.OLD
              (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time ∧
            source ∉ ReferenceFirstCollectionStagedConditionalService.FORMED
              (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time ∧
            ReferenceFirstCollectionStagedConditionalService.X
              (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time source = 0 ∧
            (BootstrapPrivateRoundStreams.sourceInputLaw p)[
              ReferenceFirstCollectionStagedConditionalService.X
                (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time |
                ReferenceSourceCurrentControlFreshness.m_t p control0
                  B[k.val].input.time] source = 0) := by
  classical
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  have hService :=
    ReferenceFirstCollectionStagedConditionalService.actual_initialized_first_collection_staged_service
      (rate := rate) rewards C_star C_h control0
  have hXCE : ∀ᵐ source ∂μ, ∀ i : Fin (p.m - 1), ∀ t : Fin p.T,
      μ[ReferenceFirstCollectionStagedConditionalService.X
          (p := p) (rate := rate) rewards C_star C_h i t |
        ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
        (ReferenceFirstCollectionStagedConditionalService.OLD
            (p := p) (rate := rate) rewards C_star C_h i t).indicator
          (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
            (rate := rate) rewards C_star C_h control0 i t) source +
        (ReferenceFirstCollectionStagedConditionalService.FORMED
            (p := p) (rate := rate) rewards C_star C_h i t).indicator
          (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
            (rate := rate) rewards C_star C_h control0 i t) source :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun t =>
      ReferenceFirstCollectionStagedConditionalService.X_condExp
        (rate := rate) rewards C_star C_h control0 i t
  filter_upwards [hService, hXCE] with source hService hXCE
  intro count hcross hspan hshort
  obtain ⟨d, hRoot⟩ := hService count hcross hspan hshort
  dsimp only at hRoot
  rcases hRoot with ⟨hWindow, hCutoff, hContinuing, hNonpending⟩
  refine ⟨d, hWindow, hCutoff, hContinuing, hNonpending, ?_⟩
  let out := d.stream
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  intro k hkTail i
  have hObservation :=
    actual_first_collection_empty_tail_observation
      (rate := rate) source rewards C_star C_h count hcross hspan hshort d k hkTail i
  rcases hObservation with ⟨hOld, hFormed, hXZero⟩
  have hConditional :=
    hXCE i B[k.val].input.time
  have hConditionalZero :
      μ[ReferenceFirstCollectionStagedConditionalService.X
          (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time |
        ReferenceSourceCurrentControlFreshness.m_t p control0 B[k.val].input.time] source = 0 := by
    have hOldIndicator :
        (ReferenceFirstCollectionStagedConditionalService.OLD
          (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time).indicator
          (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
          (rate := rate) rewards C_star C_h control0 i B[k.val].input.time) source = 0 :=
      Set.indicator_of_notMem hOld
        (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
          (rate := rate) rewards C_star C_h control0 i B[k.val].input.time)
    have hFormedIndicator :
        (ReferenceFirstCollectionStagedConditionalService.FORMED
          (p := p) (rate := rate) rewards C_star C_h i B[k.val].input.time).indicator
          (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
          (rate := rate) rewards C_star C_h control0 i B[k.val].input.time) source = 0 :=
      Set.indicator_of_notMem hFormed
        (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
          (rate := rate) rewards C_star C_h control0 i B[k.val].input.time)
    simpa only [hOldIndicator, hFormedIndicator, zero_add] using hConditional
  exact ⟨hOld, hFormed, hXZero, hConditionalZero⟩

end Bandits.Support.ReferenceFirstCollectionEmptyTailObservation

end
