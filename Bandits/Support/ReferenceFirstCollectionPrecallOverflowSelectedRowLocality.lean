/-
Copyright (c) 2026 Bandits Lean formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPrecallOverflowBound
public import Bandits.Support.ReferenceCompleteSelectedRowLocality

/-!
# Selected-row locality of the original pre-call overflow prefix

The actual first invocation, generated physical suffix, optional numerical
prefix, and its stopped-queue projections are compared on the original
coordinator-index cell. The comparison keeps the complete private source
coordinates and uses the admitted same-length physical evidence projection.

Sources: `sources/zip4/manuscript/07_public_setup.tex:123-164`,
`08_main_theorem.tex:26-43,78-115`, `04_slow_fast_learner.tex:140-215,245-290,329-390`,
and `06_interruptions.tex:35-100,355-426`. The next consumers are the
original-index private expectation and public whole-row concentration for
this literal pre-call error component. These internal locality results do
not assert the full queue error event or a manuscript theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceInitializationRun

namespace Bandits.Support.ReferenceFirstCollectionPrecallOverflowSelectedRowLocality

variable
  (p : ReferenceCompletePhysicalRewards.Parameters)
  (rate : ReferenceCompletePhysicalRewards.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)
  (ids : IDArray p)
  (R S : CompleteRows p)
  (q : ReferenceInitializationIndexMixture.PrivateResidual p)
  (s t : ContinuousCategorical.Scalar)
  (j : Fin (ConstructorDimensions.M p))
  (hs : PrivateSourceStreams.coordinatorIndex p s = j)
  (ht : PrivateSourceStreams.coordinatorIndex p t = j)
  (hrow : R j = S j)

def sourceLeft : BootstrapPrivateRoundStreams.SourceInput p :=
  ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q))

def sourceRight : BootstrapPrivateRoundStreams.SourceInput p :=
  ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q))

private theorem selectedRowIndex_left
    (hindex : PrivateSourceStreams.coordinatorIndex p s = j) :
    ActualInitializationPhysicalStep.selectedRowIndex p (sourceLeft p ids R q s) = j := by
  simp [sourceLeft, ActualInitializationPhysicalStep.selectedRowIndex,
    ReferenceInitializationIndexMixture.insertScalarResidual, hindex]

private theorem selectedRowIndex_right
    (hindex : PrivateSourceStreams.coordinatorIndex p t = j) :
    ActualInitializationPhysicalStep.selectedRowIndex p
      (sourceRight p ids S q t) = j := by
  simp [sourceRight, ActualInitializationPhysicalStep.selectedRowIndex,
    ReferenceInitializationIndexMixture.insertScalarResidual, hindex]

include j hs ht hrow in
private theorem evidence_eq :
    ReferenceCompletePhysicalHistory.completeSuffixEvidence rate
      (sourceLeft p ids R q s)
      rewards C_star C_h =
    ReferenceCompletePhysicalHistory.completeSuffixEvidence rate
      (sourceRight p ids S q t)
      rewards C_star C_h := by
  change ReferenceCompletePhysicalHistory.completeSuffixEvidence rate
      ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q))
      rewards C_star C_h =
    ReferenceCompletePhysicalHistory.completeSuffixEvidence rate
      ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q))
      rewards C_star C_h
  exact ReferenceCompleteSelectedRowLocality.completeSuffixEvidence_eq
    p rate rewards C_star C_h ids R S q s t j hs ht hrow

include j hs ht hrow in
private theorem launch_eq :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate
      (sourceLeft p ids R q s)
      rewards C_star C_h =
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate
      (sourceRight p ids S q t)
      rewards C_star C_h := by
  change ReferenceCorrectedInitializationLaunch.correctedLaunch rate
      ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q))
      rewards C_star C_h =
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate
      ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q))
      rewards C_star C_h
  exact ReferenceCompleteSelectedRowLocality.correctedLaunch_eq
    p rate rewards C_star C_h ids R S q s t j hs ht hrow

include j hs ht hrow in
private theorem physicalStart_eq :
    ReferenceCompletePhysicalHistory.physicalStart rate
      (sourceLeft p ids R q s)
      rewards C_star C_h =
    ReferenceCompletePhysicalHistory.physicalStart rate
      (sourceRight p ids S q t)
      rewards C_star C_h := by
  change ReferenceInitializationRun.elapsed p
      (ReferenceCompletePhysicalHistory.generatedBoundary rate
        (sourceLeft p ids R q s)
        rewards C_star C_h).completed =
    ReferenceInitializationRun.elapsed p
      (ReferenceCompletePhysicalHistory.generatedBoundary rate
        (sourceRight p ids S q t)
        rewards C_star C_h).completed
  exact congrArg (fun b => ReferenceInitializationRun.elapsed p b.completed)
    (ReferenceCompleteSelectedRowLocality.generatedBoundary_eq
      p rate rewards C_star C_h ids R S q s t j hs ht hrow)

include j hs ht hrow in
/-- The literal first invocation option agrees, including absence and later
checked-sampler failures. -/
theorem firstCollectionCall_eq :
    ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h
      (sourceLeft p ids R q s) =
    ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h
      (sourceRight p ids S q t) := by
  unfold ReferenceFirstCollectionSamplerCall.firstCollectionCall
  exact congrArg (fun calendar : List (ReferenceFirstCollectionSamplerCall.CalendarCell p) => calendar.findSome?
    ReferenceFirstCollectionSamplerCall.callInCell)
    (ReferenceFirstCollectionSamplerCall.collectionCallCalendar_eq_of_evidence_eq
      (rate := rate) rewards C_star C_h
      (sourceLeft p ids R q s)
      (sourceRight p ids S q t)
      (evidence_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow))

include j hs ht hrow in
/-- The actual calendar boundary is invariant; absence still selects `T`. -/
theorem firstCallBoundary_eq :
    ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
        rate rewards C_star C_h
        (sourceLeft p ids R q s) =
    ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
        rate rewards C_star C_h
        (sourceRight p ids S q t) := by
  unfold ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
  rw [firstCollectionCall_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow]

include j hs ht hrow in
/-- The real generated physical start is fixed by the original selected row.
-/
theorem physicalStart_eq_of_selected_row :
    ReferenceCompletePhysicalHistory.physicalStart rate
      (sourceLeft p ids R q s)
      rewards C_star C_h =
    ReferenceCompletePhysicalHistory.physicalStart rate
      (sourceRight p ids S q t)
      rewards C_star C_h :=
  physicalStart_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow

include j hs ht hrow in
/-- The actual optional launch predicate agrees at every calendar boundary.
-/
theorem actualLaunchBy_iff (n : ℕ) :
    ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h n
        (sourceLeft p ids R q s) ↔
    ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h n
        (sourceRight p ids S q t) := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
  have hstartRaw : ReferenceCompletePhysicalHistory.physicalStart rate
      ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q))
      rewards C_star C_h =
    ReferenceCompletePhysicalHistory.physicalStart rate
      ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q))
      rewards C_star C_h := by
    simpa [sourceLeft, sourceRight] using
      physicalStart_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow
  change
    ((ReferenceCompletePhysicalHistory.generatedBoundary rate
        ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q))
        rewards C_star C_h).crossing.isSome = true ∧
      ReferenceCompletePhysicalHistory.physicalStart rate
        ((ids, R), ReferenceInitializationIndexMixture.insertScalarResidual (s, q))
        rewards C_star C_h ≤ n) ↔
    ((ReferenceCompletePhysicalHistory.generatedBoundary rate
        ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q))
        rewards C_star C_h).crossing.isSome = true ∧
      ReferenceCompletePhysicalHistory.physicalStart rate
        ((ids, S), ReferenceInitializationIndexMixture.insertScalarResidual (t, q))
        rewards C_star C_h ≤ n)
  rw [ReferenceCompleteSelectedRowLocality.generatedBoundary_eq
      p rate rewards C_star C_h ids R S q s t j hs ht hrow, hstartRaw]

include hrow in
/-- Exact observation-code equality for corresponding actual suffix records.
The round input keeps the original row family; equality is proved from the
retained evidence and the common selected whole row, without equating raw
records. -/
theorem roundRecordCode_eq_of_temporal_reads
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hevidence : left.evidence = right.evidence)
    (hrowsL : left.input.rows = R) (hselectedL : left.input.selected = j)
    (hrewardsL : left.input.rewards = rewards)
    (hrowsR : right.input.rows = S) (hselectedR : right.input.selected = j)
    (hrewardsR : right.input.rewards = rewards) :
    ReferenceActiveHorizonMeasurability.roundRecordCode left =
      ReferenceActiveHorizonMeasurability.roundRecordCode right := by
  have hstate : left.input.state = right.input.state :=
    congrArg ReferenceActivePhysicalHorizon.RoundEvidence.before hevidence
  have htime : left.input.time = right.input.time :=
    congrArg ReferenceActivePhysicalHorizon.RoundEvidence.time hevidence
  have hcurrent : left.input.row.2 left.input.time = right.input.row.2 right.input.time := by
    change (left.input.rows left.input.selected).2 left.input.time =
      (right.input.rows right.input.selected).2 right.input.time
    rw [hrowsL, hselectedL, hrowsR, hselectedR, ← htime]
    exact congrArg (fun row : CompletePublicTable.CompleteRow p => row.2 left.input.time) hrow
  have hpast : ∀ v : Fin p.T, v.val < left.input.time.val →
      (left.input.row.2 v).1 ContinuousControlSlice.Label.prop =
        (right.input.row.2 v).1 ContinuousControlSlice.Label.prop := by
    intro v _
    change ((left.input.rows left.input.selected).2 v).1 ContinuousControlSlice.Label.prop =
      ((right.input.rows right.input.selected).2 v).1 ContinuousControlSlice.Label.prop
    rw [hrowsL, hselectedL, hrowsR, hselectedR, hrow]
  exact ReferenceInspectedPastRoundObservations.roundRecordCode_eq_of_temporal_reads
    left.input right.input hstate (hselectedL.trans hselectedR.symm) htime
    (hrewardsL.trans hrewardsR.symm) hcurrent hpast

private theorem collection_guard_iff
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (htime : x.time = y.time)
    (hselected : x.row = y.row) :
    ReferenceLaterCollectionReadoutDomain.observableReadoutGuard rate 0 x ↔
      ReferenceLaterCollectionReadoutDomain.observableReadoutGuard rate 0 y := by
  have hlive : ReferenceLaterCollectionReadoutDomain.actualLiveOutcomeData rate x =
      ReferenceLaterCollectionReadoutDomain.actualLiveOutcomeData rate y := by
    unfold ReferenceLaterCollectionReadoutDomain.actualLiveOutcomeData
    rw [hstate]
    exact congrArg (fun z : Fin p.T × CompleteRow p =>
      match ReferenceActivePhysicalStepMeasurability.encodeCoordinator y.state.coordinator with
      | .inl _ => none
      | .inr (.inl (payload, live)) =>
          some (ReferenceLiveDispatchOutputMeasurability.outcomeData
            (CoordinatorRoundDispatch.dispatchLive
              (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates
                (payload, (live, z)))), payload.sigma)
      | .inr (.inr _) => none) (show (x.time, x.row) = (y.time, y.row) from Prod.ext htime hselected)
  simp only [ReferenceLaterCollectionReadoutDomain.observableReadoutGuard,
    ReferenceLaterCollectionReadoutDomain.preparedFollowerTag,
    ReferenceActivePhysicalStepMeasurability.preparedFollowerCode,
    ReferenceLaterCollectionReadoutDomain.canonicalCollectionTag,
    ReferenceCollectionOutcomeMeasurability.canonicalCollectionFullObservation,
    hlive, hstate, htime, hselected]

private theorem prepared_configuration_eq
    (left right : RoundRecord (p := p) (rate := rate))
    (hstate : left.input.state = right.input.state)
    (htime : left.input.time = right.input.time)
    (hselected : left.input.row = right.input.row) (i : Fin (p.m - 1)) :
    (left.output.preparation.followers.followers i).configuration =
      (right.output.preparation.followers.followers i).configuration := by
  rw [left.output_eq, right.output_eq]
  change (DeclaredFollowerLocalRound.prepare rate i left.input.row
    (left.input.state.activations i) left.input.time (left.input.active i)
    (left.input.state.followers i)).configuration =
      (DeclaredFollowerLocalRound.prepare rate i right.input.row
        (right.input.state.activations i) right.input.time (right.input.active i)
        (right.input.state.followers i)).configuration
  simp only [hstate, htime, hselected]

private theorem sourceCell_eq_of_view
    (left right : RoundRecord (p := p) (rate := rate))
    (lv rv : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (hv : lv = rv)
    (ls rs : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (hstates : ls = rs)
    (lc : CoordinatorLocalArmChoice.ChoiceInputsValid lv.payload lv.cutoff
      left.input.time lv.complementWeights)
    (rc : CoordinatorLocalArmChoice.ChoiceInputsValid rv.payload rv.cutoff
      right.input.time rv.complementWeights)
    (htime : left.input.time = right.input.time)
    (hselected : left.input.row = right.input.row)
    (hrewards : left.input.rewards = right.input.rewards) :
    ReferenceFirstWindowNumericalStream.sourceCell left lv.payload lv.pendingAtChoice
        ls lv.complementWeights lv.cutoff lc =
      ReferenceFirstWindowNumericalStream.sourceCell right rv.payload rv.pendingAtChoice
        rs rv.complementWeights rv.cutoff rc := by
  cases hv
  cases hstates
  simp only [ReferenceFirstWindowNumericalStream.sourceCell,
    ReferenceFirstWindowNumericalStream.sourceArm, htime, hselected, hrewards]

private theorem live_readout_eq
    (left right : RoundRecord (p := p) (rate := rate))
    (hstate : left.input.state = right.input.state)
    (htime : left.input.time = right.input.time)
    (hselected : left.input.row = right.input.row)
    (hrewards : left.input.rewards = right.input.rewards)
    (hcode : ReferenceActiveHorizonMeasurability.roundRecordCode left =
      ReferenceActiveHorizonMeasurability.roundRecordCode right) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 left =
      ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 right := by
  have hview : left.output.preparation.coordinator.downView =
      right.output.preparation.coordinator.downView := by
    rw [left.output.preparation.coordinator_eq, right.output.preparation.coordinator_eq]
    rw [← (ReferenceActiveHorizonMeasurability.roundRecordCode_front left).2.1,
      ← (ReferenceActiveHorizonMeasurability.roundRecordCode_front right).2.1, hcode]
  have hprepared := prepared_configuration_eq p rate left right hstate htime hselected
  have ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary left ↔
      ReferenceLaterLiveNumericalReadout.preparedOrdinary right := by
    simp only [ReferenceLaterLiveNumericalReadout.preparedOrdinary, hprepared]
  unfold ReferenceActivePhysicalStep.DispatchCut.downView at hview
  unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
  cases hl : left.output.preparation.coordinator.selection with
  | none =>
      cases hr : right.output.preparation.coordinator.selection with
      | none => rfl
      | some selected => simp only [hl, hr, Option.map_none, Option.map_some,
          reduceCtorEq] at hview
  | some l =>
      cases hr : right.output.preparation.coordinator.selection with
      | none => simp only [hl, hr, Option.map_none, Option.map_some,
          reduceCtorEq] at hview
      | some r =>
          have hv : l.view = r.view := by
            simpa only [hl, hr, Option.map_some, Option.some.injEq] using hview
          have hc : (0 < l.view.payload.sigma.val ∧
              CoordinatorLocalArmChoice.assignmentIsLive l.view.payload
                l.view.cutoff left.input.time) ↔
              (0 < r.view.payload.sigma.val ∧
              CoordinatorLocalArmChoice.assignmentIsLive r.view.payload
                r.view.cutoff right.input.time) := by rw [hv, htime]
          dsimp only
          by_cases hcl : 0 < l.view.payload.sigma.val ∧
              CoordinatorLocalArmChoice.assignmentIsLive l.view.payload l.view.cutoff left.input.time
          · have hcr := hc.mp hcl
            simp only [ite_eq_left hcl, ite_eq_left hcr]
            by_cases hol : ReferenceLaterLiveNumericalReadout.preparedOrdinary left
            · have hor := ho.mp hol
              simp only [dite_eq_left hol, dite_eq_left hor]
              congr 1
              apply sourceCell_eq_of_view p rate left right l.view r.view hv
                _ _ _ _ _ htime hselected hrewards
              funext i
              have hordinary :=
                (ReferenceLaterLiveNumericalReadout.prepared_configuration left hol i).symm.trans
                  ((hprepared i).trans
                    (ReferenceLaterLiveNumericalReadout.prepared_configuration right hor i))
              exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hordinary).1
            · have hor : ¬ ReferenceLaterLiveNumericalReadout.preparedOrdinary right :=
                fun h => hol (ho.mpr h)
              simp only [dite_eq_right hol, dite_eq_right hor]
          · have hcr : ¬ (0 < r.view.payload.sigma.val ∧
                CoordinatorLocalArmChoice.assignmentIsLive r.view.payload r.view.cutoff right.input.time) :=
              fun h => hcl (hc.mpr h)
            simp only [ite_eq_right hcl, ite_eq_right hcr]

private theorem numericalCoordinates_injective :
    Function.Injective
      (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
        (p := p)) := by
  intro a b h
  rcases a with ⟨ae, aa, aw, ar, _, _, _⟩
  rcases b with ⟨be, ba, bw, br, _, _, _⟩
  simp only [ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates,
    Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  rfl

private theorem collection_readout_eq
    (left right : RoundRecord (p := p) (rate := rate))
    (hstate : left.input.state = right.input.state)
    (htime : left.input.time = right.input.time)
    (hselected : left.input.row = right.input.row)
    (hrewards : left.input.rewards = right.input.rewards)
    (hcode : ReferenceActiveHorizonMeasurability.roundRecordCode left =
      ReferenceActiveHorizonMeasurability.roundRecordCode right) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 left =
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 right := by
  have hg : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 left).isSome = true ↔
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 right).isSome = true := by
    rw [ReferenceLaterCollectionReadoutDomain.readout_isSome_iff,
      ReferenceLaterCollectionReadoutDomain.readout_isSome_iff]
    exact collection_guard_iff p rate left.input right.input hstate htime hselected
  apply Option.map_injective (numericalCoordinates_injective p)
  rw [ReferenceLaterCollectionSourceReadoutMeasurability.readout_numerical_factorization,
    ReferenceLaterCollectionSourceReadoutMeasurability.readout_numerical_factorization,
    hcode, hrewards, htime]
  exact if_congr hg rfl rfl

include hrow in
/-- The actual optional numerical cell agrees on corresponding source records.
Only temporal input provenance and the retained physical evidence are required. -/
theorem cell0_eq_of_temporal_reads
    (left right : RoundRecord (p := p) (rate := rate))
    (hevidence : left.evidence = right.evidence)
    (hrowsL : left.input.rows = R) (hselectedL : left.input.selected = j)
    (hrewardsL : left.input.rewards = rewards)
    (hrowsR : right.input.rows = S) (hselectedR : right.input.selected = j)
    (hrewardsR : right.input.rewards = rewards) :
    ReferenceFirstCollectionCurrentRetainedGate.cell0 rate left =
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate right := by
  have hstate : left.input.state = right.input.state :=
    congrArg RoundEvidence.before hevidence
  have htime : left.input.time = right.input.time :=
    congrArg RoundEvidence.time hevidence
  have hselected : left.input.row = right.input.row := by
    change left.input.rows left.input.selected = right.input.rows right.input.selected
    rw [hrowsL, hselectedL, hrowsR, hselectedR, hrow]
  have hrewards := hrewardsL.trans hrewardsR.symm
  have hcode := roundRecordCode_eq_of_temporal_reads p rate rewards R S j hrow
    left right hevidence hrowsL hselectedL hrewardsL hrowsR hselectedR hrewardsR
  unfold ReferenceFirstCollectionCurrentRetainedGate.cell0
  rw [live_readout_eq p rate left right hstate htime hselected hrewards hcode,
    collection_readout_eq p rate left right hstate htime hselected hrewards hcode]

private theorem suffix_inputs
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (record : RoundRecord (p := p) (rate := rate))
    (hr : record ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) :
    record.input.rows = z.1.2 ∧
      record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      record.input.rewards = rewards := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none => simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords,
      hl, dite_true, List.not_mem_nil] at hr
  | some active =>
      rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate z rewards C_star C_h active hl] at hr
      exact ReferenceActivePhysicalHorizon.run_record_inputs active z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        _ _ record hr

include j hs ht hrow in
private theorem suffix_slots_eq :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate
      (sourceLeft p ids R q s) rewards C_star C_h).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate
      (sourceRight p ids S q t) rewards C_star C_h).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) := by
  let left := ReferenceCompletePhysicalHistory.completeSuffixRecords rate
    (sourceLeft p ids R q s) rewards C_star C_h
  let right := ReferenceCompletePhysicalHistory.completeSuffixRecords rate
    (sourceRight p ids S q t) rewards C_star C_h
  have he : left.map RoundRecord.evidence = right.map RoundRecord.evidence :=
    evidence_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow
  have hleft : ∀ r ∈ left, r.input.rows = R ∧ r.input.selected = j ∧
      r.input.rewards = rewards := by
    intro r hr
    obtain ⟨hr, hj, hw⟩ :=
      suffix_inputs p rate rewards C_star C_h (sourceLeft p ids R q s) r hr
    exact ⟨hr, hj.trans (selectedRowIndex_left p ids R q s j hs), hw⟩
  have hright : ∀ r ∈ right, r.input.rows = S ∧ r.input.selected = j ∧
      r.input.rewards = rewards := by
    intro r hr
    obtain ⟨hr, hj, hw⟩ :=
      suffix_inputs p rate rewards C_star C_h (sourceRight p ids S q t) r hr
    exact ⟨hr, hj.trans (selectedRowIndex_right p ids S q t j ht), hw⟩
  change left.map _ = right.map _
  have hlen : left.length = right.length := by
    simpa only [List.length_map] using congrArg List.length he
  apply List.ext_getElem
  · simpa only [List.length_map] using hlen
  · intro k hkL hkR
    have hkLeft : k < left.length := by simpa only [List.length_map] using hkL
    have hkRight : k < right.length := by simpa only [List.length_map] using hkR
    have hre : left[k].evidence = right[k].evidence := by
      have hg := congrArg (fun l : List (RoundEvidence (p := p) (rate := rate)) => l[k]?) he
      simpa only [List.getElem?_map, List.getElem?_eq_getElem hkLeft,
        List.getElem?_eq_getElem hkRight, Option.map_some, Option.some.injEq] using hg
    obtain ⟨hrL, hjL, hwL⟩ := hleft left[k] (List.getElem_mem hkLeft)
    obtain ⟨hrR, hjR, hwR⟩ := hright right[k] (List.getElem_mem hkRight)
    simpa only [List.getElem_map] using cell0_eq_of_temporal_reads
      p rate rewards R S j hrow left[k] right[k] hre hrL hjL hwL hrR hjR hwR

include j hs ht hrow in
/-- The original strict-past cutoff agrees at every natural calendar boundary. -/
theorem cutBoundary_eq (n : ℕ) :
    ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary rate rewards C_star C_h n
        (sourceLeft p ids R q s) =
      ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary rate rewards C_star C_h n
        (sourceRight p ids S q t) := by
  unfold ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
  rw [firstCallBoundary_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow]

include j hs ht hrow in
/-- Every dated optional slot is identical, including absent numerical cells. -/
theorem precallSlots_eq (n : ℕ) :
    ReferenceFirstCollectionPrecallCalendarSupport.precallSlots rate rewards C_star C_h n
        (sourceLeft p ids R q s) =
      ReferenceFirstCollectionPrecallCalendarSupport.precallSlots rate rewards C_star C_h n
        (sourceRight p ids S q t) := by
  unfold ReferenceFirstCollectionPrecallCalendarSupport.precallSlots
  rw [cutBoundary_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow n,
    physicalStart_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow]
  apply List.map_congr_left
  intro k _
  have hg := congrArg (fun L : List (Option (RecordedQueueRun.RoundInput p.K)) =>
    (L[k]?).bind id) (suffix_slots_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow)
  simpa only [List.getElem?_map, Option.bind_map, Function.comp_def, id_eq] using hg

include j hs ht hrow in
/-- Exact original optional numerical-prefix invariance, in particular for
all `n ≤ T`. No successful-prefix or queue premise is supplied. -/
theorem precallCells_eq (n : ℕ) :
    ReferenceFirstCollectionPrecallCalendarSupport.precallCells? rate rewards C_star C_h n
        (sourceLeft p ids R q s) =
      ReferenceFirstCollectionPrecallCalendarSupport.precallCells? rate rewards C_star C_h n
        (sourceRight p ids S q t) := by
  classical
  unfold ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
  rw [precallSlots_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow n,
    cutBoundary_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow n]
  apply if_congr
  · exact actualLaunchBy_iff p rate rewards C_star C_h ids R S q s t j hs ht hrow _
  · rfl
  · rfl

include j hs ht hrow in
/-- The actual stopped-run readout agrees, including the terminal boundary. -/
theorem precallReadout_eq (n : ℕ) :
    ReferenceFirstCollectionPrecallCalendarSupport.precallReadout? rate rewards C_star C_h n
        (sourceLeft p ids R q s) =
      ReferenceFirstCollectionPrecallCalendarSupport.precallReadout? rate rewards C_star C_h n
        (sourceRight p ids S q t) := by
  unfold ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?
  rw [precallCells_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow n]

include j hs ht hrow in
/-- The literal normalized backlog agrees at every boundary and on every arm. -/
theorem precallBacklog_eq (n : ℕ) (a : Fin p.K) :
    ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog rate rewards C_star C_h n a
        (sourceLeft p ids R q s) =
      ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog rate rewards C_star C_h n a
        (sourceRight p ids S q t) := by
  unfold ReferenceFirstCollectionPrecallCalendarSupport.precallBacklog
  rw [precallCells_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow n]

include j hs ht hrow in
/-- Selected-WHOLE-row locality for membership in the literal pre-call overflow
component. The first detecting update is retained by the unchanged event. -/
theorem mem_precallOverflow_iff :
    sourceLeft p ids R q s ∈
        ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h ↔
      sourceRight p ids S q t ∈
        ReferenceFirstCollectionPrecallOverflowBound.precallOverflow rate rewards C_star C_h := by
  simp only [ReferenceFirstCollectionPrecallOverflowBound.precallOverflow,
    Set.mem_ofPred_eq,
    precallCells_eq p rate rewards C_star C_h ids R S q s t j hs ht hrow]

end Bandits.Support.ReferenceFirstCollectionPrecallOverflowSelectedRowLocality

end
