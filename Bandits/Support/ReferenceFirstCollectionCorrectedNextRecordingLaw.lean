/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedNextRetainedGate

/-!
# Original-source corrected successor optional recording law

The literal corrected first-call event localizes the actual successor marker
law on the original source probability space. The proof integrates the entire
current TimeControl using its physical snapshot and assignment, preserving
absent, disabled, enabled no-marker, and recorded-arm outcomes.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:352-431`,
`04_slow_fast_learner.tex:140-188,245-278`, and
`06_interruptions.tex:31-100,355-426`.

This is an internal recording law. Conditional arrival estimates and retained
exponential bounds belong to a later consumer; no manuscript closure is claimed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ContinuousLearningRows (TimeControl)
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
  (sourcePrefix sourcePrefix_sourcePrefix sourcePrefixFiltration)
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCorrectedNextRecordingLaw

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p

variable (control0 : TimeControl p) (u t : Fin p.T)

local notation "C" => Set.ofPred (fun x : X =>
  x ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t ∧
    ∃ g, ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
      rate rewards C_star C_h t x = some g ∧ t.val + 1 < g)

/-- The literal actual kernel on the corrected first-call branch.  The
snapshot, choice validity, rate bounds, and live/collection status code are
produced by the physical constructor on this same original source. -/
theorem corrected_firstCell_successor_physical_kernel
    (control0 : TimeControl p) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ C) :
    match ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextRecordingView
        rate rewards C_star C_h t hq x with
    | none =>
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
          rate rewards C_star C_h t hq x = none
    | some (parameters, view, code) =>
        ∃ (enabled : Bool)
          (snapshot : Option
            (ActiveRoundActions.Snapshot view.payload.assignment))
          (valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload
            view.cutoff ⟨t.val + 1, hq⟩ view.complementWeights),
          parameters = some (enabled, view.payload.rate) ∧
          code = snapshot.map (fun z => (z.missing, fun i => some
            (FollowerDownMeasurability.followerStatusCode (z.status i)))) ∧
          ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
              rate rewards C_star C_h t hq x =
            some (SnapshotRecordingKernel.recordingMap p
              (snapshot.elim .collection
                (fun z => .live view.payload.assignment z)) enabled
              rate.eta.val rate.eta.property rate.sourceCap view.payload.anchor
              (ReferenceFirstWindowNumericalStream.sourceWeights view.payload
                view.complementWeights)
              view.payload.anchor_pos
              (ReferenceFirstWindowNumericalStream.sourceWeights_pos
                _ _ _ _ valid)
              (ReferenceFirstWindowNumericalStream.sourceWeights_lower
                _ _ _ _ valid)
              (ReferenceFirstWindowNumericalStream.sourceWeights_upper
                _ _ _ _ valid)
              (ContinuousLearningRows.sliceAt ⟨t.val + 1, hq⟩
                (x.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x)).2)) := by
  rcases hx with ⟨hx, g, hg, hlt⟩
  exact ReferenceFirstCollectionCorrectedNextPhysicalReadout.corrected_next_physical_kernel
    rate rewards C_star C_h control0 u t hq x hx g hg hlt

private theorem snapshot_code_injective
    (assignment : ActiveRoundActions.Assignment p.m p.K) :
    Function.Injective (fun snapshot : Option (ActiveRoundActions.Snapshot assignment) =>
      snapshot.map (fun s => (s.missing, fun i => some
        (FollowerDownMeasurability.followerStatusCode (s.status i))))) := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases h
  | some a => cases b with
    | none => cases h
    | some b =>
      have he := Option.some.inj h
      have hm := congrArg Prod.fst he
      have hs : a.status = b.status := by
        funext i
        have hi := Option.some.inj (congrFun (congrArg Prod.snd he) i)
        have hd := congrArg FollowerDownMeasurability.followerStatusOfCode hi
        simpa only [FollowerDownMeasurability.followerStatusOfCode_code] using hd
      cases a
      cases b
      cases hm
      cases hs
      rfl

/-- On every whole current-control replacement, the original predecessor
still fixes the same parameters, sender view, snapshot, and status code.
The remaining randomized argument is exactly that replacement's slice. -/
theorem corrected_firstCell_successor_marker_section
    (control0 : TimeControl p) (hq : t.val + 1 < p.T) (x : X)
    (hx : x ∈ C) :
    match ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextRecordingView
        rate rewards C_star C_h t hq x with
    | none => ∀ control : TimeControl p,
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
          rate rewards C_star C_h t hq
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
              ⟨t.val + 1, hq⟩ x control) = none
    | some (parameters, view, code) =>
        ∃ (enabled : Bool)
          (snapshot : Option
            (ActiveRoundActions.Snapshot view.payload.assignment))
          (valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload
            view.cutoff ⟨t.val + 1, hq⟩ view.complementWeights),
          parameters = some (enabled, view.payload.rate) ∧
          code = snapshot.map (fun z => (z.missing, fun i => some
            (FollowerDownMeasurability.followerStatusCode (z.status i)))) ∧
          ∀ control : TimeControl p,
            ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
                rate rewards C_star C_h t hq
                  (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
                    ⟨t.val + 1, hq⟩ x control) =
              some (SnapshotRecordingKernel.recordingMap p
                (snapshot.elim .collection
                  (fun z => .live view.payload.assignment z)) enabled
                rate.eta.val rate.eta.property rate.sourceCap view.payload.anchor
                (ReferenceFirstWindowNumericalStream.sourceWeights view.payload
                  view.complementWeights)
                view.payload.anchor_pos
                (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
                (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
                (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid)
                (ContinuousLearningRows.sliceAt ⟨t.val + 1, hq⟩
                  ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
                    ⟨t.val + 1, hq⟩ x control).1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p
                      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
                        ⟨t.val + 1, hq⟩ x control))).2)) := by
  rcases hx with ⟨hx, g, hg, hlt⟩
  have hbase := corrected_firstCell_successor_physical_kernel
    rate rewards C_star C_h u t control0 hq x ⟨hx, g, hg, hlt⟩
  cases hv : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextRecordingView
      rate rewards C_star C_h t hq x with
  | none =>
      rw [hv] at hbase
      intro control
      let y := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
        ⟨t.val + 1, hq⟩ x control
      have hbranch := ReferenceFirstCollectionCorrectedNextPhysicalReadout.corrected_branch_replaceControl
        rate rewards C_star C_h control0 u t hq x hx g hg hlt control
      have hprior := ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_prior_replaceControl
        rate rewards C_star C_h control0 u t hq x hx control
      have hy : y ∈ C := ⟨hbranch.1, g, hbranch.2.1, hbranch.2.2⟩
      have hk := corrected_firstCell_successor_physical_kernel
        rate rewards C_star C_h u t control0 hq y hy
      have hview : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextRecordingView
          rate rewards C_star C_h t hq y = none := by
        rw [← hprior.2, hv]
      rw [hview] at hk
      exact hk
  | some result =>
      rcases result with ⟨parameters, view, code⟩
      rw [hv] at hbase
      obtain ⟨enabled, snapshot, valid, hparameters, hcode, _hmarker⟩ := hbase
      refine ⟨enabled, snapshot, valid, hparameters, hcode, ?_⟩
      intro control
      let y := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
        ⟨t.val + 1, hq⟩ x control
      have hbranch := ReferenceFirstCollectionCorrectedNextPhysicalReadout.corrected_branch_replaceControl
        rate rewards C_star C_h control0 u t hq x hx g hg hlt control
      have hprior := ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_prior_replaceControl
        rate rewards C_star C_h control0 u t hq x hx control
      have hy : y ∈ C := ⟨hbranch.1, g, hbranch.2.1, hbranch.2.2⟩
      have hk := corrected_firstCell_successor_physical_kernel
        rate rewards C_star C_h u t control0 hq y hy
      have hview : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextRecordingView
          rate rewards C_star C_h t hq y = some (parameters, view, code) := by
        rw [← hprior.2, hv]
      rw [hview] at hk
      obtain ⟨enabled', snapshot', valid', hparameters', hcode', hmarker'⟩ := hk
      have henabled : enabled' = enabled := by
        exact congrArg Prod.fst (Option.some.inj (hparameters'.symm.trans hparameters))
      have hsnapshot : snapshot' = snapshot :=
        snapshot_code_injective view.payload.assignment (hcode'.symm.trans hcode)
      subst enabled'
      subst snapshot'
      simpa only using hmarker'

private theorem measurable_variable_observation {B : Type*}
    [MeasurableSpace B]
    (f : X → List B) (hf : Measurable f) (j : X → ℕ) (hj : Measurable j) :
    Measurable (fun x => ReferenceActiveHorizonMeasurability.listObservationAt
      (f x) (j x)) := by
  have ho := measurable_snd.comp
    (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hf)
  have he : Measurable
      (fun v : (ℕ → Unit ⊕ B) × ℕ => v.1 v.2) :=
    measurable_from_prod_countable_left (fun n => measurable_pi_apply n)
  exact he.comp (ho.prodMk hj)

private theorem measurable_marker_observation_read :
    Measurable (fun e : Unit ⊕ (Fin p.T × Option
      (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)) =>
        Sum.elim (fun _ => (none : Option (Option (Fin p.K))))
          (fun entry => entry.2.map (fun code => code.2.1)) e) := by
  let Code := ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p
  have hcode : Measurable (fun e : Fin p.T × Option Code =>
      Equiv.optionEquivSumPUnit Code e.2) :=
    (comap_measurable _).comp measurable_snd
  have hmarker : Measurable (fun code : Code => code.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_id)
  have hread : Measurable (fun e : Code ⊕ PUnit =>
      Sum.elim (fun code : Code => some code.2.1) (fun _ => none) e) := by
    exact ((measurable_of_countable
      (fun a : Option (Fin p.K) => some a)).comp hmarker).sumElim
        measurable_const
  have hentry : Measurable (fun e : Fin p.T × Option Code =>
      e.2.map (fun code => code.2.1)) := by
    convert hread.comp hcode using 1
    funext e
    rcases e with ⟨_, code⟩
    cases code <;> rfl
  exact measurable_const.sumElim hentry

/-- The actual arm-or-bottom marker on the original source is Borel.  The
proof reads both existing branch decoders at the physical successor index;
it preserves the original record's optional cell and the full source. -/
theorem corrected_nextMarker_measurable (hq : t.val + 1 < p.T) :
    Measurable (ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
      rate rewards C_star C_h t hq) := by
  let q : Fin p.T := ⟨t.val + 1, hq⟩
  let observation := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
    rate rewards C_star C_h
  have hobs : Measurable observation :=
    ReferenceCompleteNumericalBranchObservation.measurable_completeBranchObservation
      rate rewards C_star C_h
  have hlive : Measurable (fun x : X =>
      ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder rate
        (observation x)) :=
    (ReferenceCompleteFirstPhaseObservationRecovery.measurable_rawLiveNumericalDecoder
      rate).comp hobs
  have hcollection : Measurable (fun x : X =>
      ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder rate
        (observation x)) :=
    (ReferenceCompleteFirstPhaseObservationRecovery.measurable_rawCollectionNumericalDecoder
      rate).comp hobs
  have hstart : Measurable (fun x : X =>
      ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h) :=
    ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h
  let H : Set X := {x | ReferenceCompletePhysicalHistory.physicalStart
    rate x rewards C_star C_h ≤ q.val}
  have hH : MeasurableSet H := measurableSet_le hstart measurable_const
  let index := fun x : X => if x ∈ H then q.val -
    ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h else p.T
  have hindex : Measurable index := by
    apply Measurable.ite hH
    · exact (measurable_of_countable (fun s : ℕ => q.val - s)).comp hstart
    · exact measurable_const
  let read := fun e : Unit ⊕ (Fin p.T × Option
      (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)) =>
        Sum.elim (fun _ => (none : Option (Option (Fin p.K))))
          (fun entry => entry.2.map (fun code => code.2.1)) e
  have hread := measurable_marker_observation_read (p := p)
  let liveAt := fun x : X => read (ReferenceActiveHorizonMeasurability.listObservationAt
    (ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder rate
      (observation x)) (index x))
  let collectionAt := fun x : X => read (ReferenceActiveHorizonMeasurability.listObservationAt
    (ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder rate
      (observation x)) (index x))
  have hliveAt : Measurable liveAt := by
    exact hread.comp (measurable_variable_observation
      (fun x : X => ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder
        rate (observation x))
      hlive index hindex)
  have hcollectionAt : Measurable collectionAt := by
    exact hread.comp (measurable_variable_observation
      (fun x : X => ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder
        rate (observation x))
      hcollection index hindex)
  have hor : Measurable (fun z : Option (Option (Fin p.K)) ×
      Option (Option (Fin p.K)) => z.1.or z.2) := measurable_of_countable _
  have hjoined : Measurable (fun x : X => liveAt x |>.or (collectionAt x)) :=
    hor.comp (hliveAt.prodMk hcollectionAt)
  let localized := fun x : X => if x ∈ H then liveAt x |>.or (collectionAt x)
    else (none : Option (Option (Fin p.K)))
  have hlocalized : Measurable localized := Measurable.ite hH hjoined measurable_const
  have heq (x : X) :
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
          rate rewards C_star C_h t hq x = localized x := by
    by_cases hs : x ∈ H
    · have hstart_le : ReferenceCompletePhysicalHistory.physicalStart
          rate x rewards C_star C_h ≤ q.val := hs
      let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate x rewards C_star C_h
      have hlen : records.length = p.T -
          ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h := by
        simpa only [records] using
          ReferenceCompletePhysicalHistory.completeSuffixRecords_length
            rate x rewards C_star C_h
      have hindex_lt : q.val - ReferenceCompletePhysicalHistory.physicalStart
          rate x rewards C_star C_h < records.length := by
        rw [hlen]
        omega
      let k : Fin records.length :=
        ⟨q.val - ReferenceCompletePhysicalHistory.physicalStart rate x rewards C_star C_h,
          hindex_lt⟩
      let record := records.get k
      have hget : records[k.val]? = some record :=
        List.getElem?_eq_getElem k.isLt
      have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h q x = some record := by
        rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hstart_le]
        simpa only [records, k, record] using hget
      have hrawLive :=
        ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder_completeSuffixRecords
          rate rewards C_star C_h x
      have hrawCollection :=
        ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder_completeSuffixRecords
          rate rewards C_star C_h x
      have hliveGet :
          (ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder
            rate (observation x))[k.val]? = some (record.input.time,
              (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record).map
                ReferenceCompleteNumericalBranchObservation.encodeNumerical) := by
        rw [hrawLive, List.getElem?_map, hget]
        simp only [Option.map_some]
      have hcollectionGet :
          (ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder
            rate (observation x))[k.val]? = some (record.input.time,
              (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).map
                ReferenceCompleteNumericalBranchObservation.encodeNumerical) := by
        rw [hrawCollection, List.getElem?_map, hget]
        simp only [Option.map_some]
      have hliveObs : ReferenceActiveHorizonMeasurability.listObservationAt
          (ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder
            rate (observation x)) k.val = Sum.inr (record.input.time,
              (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record).map
                ReferenceCompleteNumericalBranchObservation.encodeNumerical) := by
        simp only [ReferenceActiveHorizonMeasurability.listObservationAt, hliveGet]
      have hcollectionObs : ReferenceActiveHorizonMeasurability.listObservationAt
          (ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder
            rate (observation x)) k.val = Sum.inr (record.input.time,
              (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).map
                ReferenceCompleteNumericalBranchObservation.encodeNumerical) := by
        simp only [ReferenceActiveHorizonMeasurability.listObservationAt, hcollectionGet]
      have hindex_value : index x = k.val := by
        dsimp only [index]
        rw [ite_eq_left hs]
      have hliveMarker : liveAt x =
          (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record).map
            (fun c => c.recordedArm) := by
        change read (ReferenceActiveHorizonMeasurability.listObservationAt
          (ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder rate
            (observation x)) (index x)) = _
        rw [hindex_value, hliveObs]
        simp [read, ReferenceCompleteNumericalBranchObservation.encodeNumerical,
          ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates,
          Option.map_map, Function.comp_def]
      have hcollectionMarker : collectionAt x =
          (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).map
            (fun c => c.recordedArm) := by
        change read (ReferenceActiveHorizonMeasurability.listObservationAt
          (ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder rate
            (observation x)) (index x)) = _
        rw [hindex_value, hcollectionObs]
        simp [read, ReferenceCompleteNumericalBranchObservation.encodeNumerical,
          ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates,
          Option.map_map, Function.comp_def]
      rw [ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker,
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextCell, hactual]
      simp only [Option.bind_some, ReferenceFirstCollectionCurrentRetainedGate.cell0]
      change Option.map (fun c => c.recordedArm)
          ((ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record).or
            (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record)) =
        (if x ∈ H then liveAt x |>.or (collectionAt x)
          else (none : Option (Option (Fin p.K))))
      simp only [hs, ite_true]
      have hMap :
          Option.map (fun c => c.recordedArm)
              ((ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record).or
                (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record)) =
            (Option.map (fun c => c.recordedArm)
                (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record)).or
              (Option.map (fun c => c.recordedArm)
                (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record)) := by
        cases ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record <;>
          cases ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record <;>
          rfl
      rw [hMap, ← hliveMarker, ← hcollectionMarker]
    · have hstart_lt : ¬ ReferenceCompletePhysicalHistory.physicalStart
          rate x rewards C_star C_h ≤ q.val := hs
      have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h q x = none := by
        rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_right hstart_lt]
      have hactual' : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h ⟨t.val + 1, hq⟩ x = none := by
        change ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h q x = none
        exact hactual
      rw [ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker,
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextCell, hactual']
      simp [localized, hs]
  rw [show ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
      rate rewards C_star C_h t hq = localized by funext x; exact heq x]
  exact hlocalized

private theorem replacement_slice (hq : t.val + 1 < p.T)
    (x : X) (control : TimeControl p) :
    ContinuousLearningRows.sliceAt ⟨t.val + 1, hq⟩
      ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
        ⟨t.val + 1, hq⟩ x control).1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
            ⟨t.val + 1, hq⟩ x control))).2 = control.1 := by
  simp only [ContinuousLearningRows.sliceAt,
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ActualInitializationPhysicalStep.selectedRowIndex,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    Function.update_self]

/-- Equal actual prior views and equal current slices determine the marker.
All physical witnesses are produced on the two original source points. -/
private theorem corrected_nextMarker_congr (hq : t.val + 1 < p.T) (x y : X)
    (hx : x ∈ C)
    (hprefix : sourcePrefix control0 (t.val + 1) x =
      sourcePrefix control0 (t.val + 1) y)
    (hslice : ContinuousLearningRows.sliceAt ⟨t.val + 1, hq⟩
        (x.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x)).2 =
      ContinuousLearningRows.sliceAt ⟨t.val + 1, hq⟩
        (y.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p y)).2) :
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq x =
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq y := by
  obtain ⟨hcell, g, hg, hlt⟩ := hx
  have hy := ReferenceFirstCollectionCorrectedNextPhysicalReadout.corrected_branch_prefix_congr
    rate rewards C_star C_h control0 u t x y hprefix hcell g hg hlt
  have hview := (ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_next_prior_congr
    rate rewards C_star C_h control0 u t hq x y hcell hprefix).2.2.2
  have hkx := corrected_firstCell_successor_physical_kernel
    rate rewards C_star C_h u t control0 hq x ⟨hcell, g, hg, hlt⟩
  have hky := corrected_firstCell_successor_physical_kernel
    rate rewards C_star C_h u t control0 hq y ⟨hy.1, g, hy.2.1, hy.2.2⟩
  rw [← hview] at hky
  cases hv : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextRecordingView
      rate rewards C_star C_h t hq x with
  | none =>
      rw [hv] at hkx hky
      exact hkx.trans hky.symm
  | some v =>
      rcases v with ⟨parameters, view, code⟩
      rw [hv] at hkx hky
      obtain ⟨enabled, snapshot, valid, hp, hc, hm⟩ := hkx
      obtain ⟨enabled', snapshot', valid', hp', hc', hm'⟩ := hky
      have he : enabled' = enabled :=
        congrArg Prod.fst (Option.some.inj (hp'.symm.trans hp))
      have hs : snapshot' = snapshot :=
        snapshot_code_injective view.payload.assignment (hc'.symm.trans hc)
      subst enabled'
      subst snapshot'
      rw [hm, hm', hslice]

/-- Restoring the complete current control in the strict prefix recovers the
actual optional marker on the literal corrected event. -/
private theorem corrected_nextMarker_reconstruct (hq : t.val + 1 < p.T)
    (x : X) (hx : x ∈ C) :
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq x =
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
          ⟨t.val + 1, hq⟩
          (ReferenceSourceCurrentControlFreshness.c_t p control0 ⟨t.val + 1, hq⟩ x)
          (ReferenceSourceCurrentControlFreshness.u_t p ⟨t.val + 1, hq⟩ x)) := by
  apply corrected_nextMarker_congr rate rewards C_star C_h control0 u t hq x _ hx
  · rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix,
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.sourcePrefix_replaceControl,
      sourcePrefix_sourcePrefix control0 _ _ le_rfl]
  · rw [replacement_slice]
    rfl

private theorem recordingView_parameters (hq : t.val + 1 < p.T) (x : X)
    (parameters : Option (Bool × (Fin p.K → ℝ)))
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (code : Option (Finset (Fin (p.m - 1)) × (Fin (p.m - 1) → Option (Fin 3))))
    (hv : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextRecordingView
      rate rewards C_star C_h t hq x = some (parameters, view, code)) :
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
      rate rewards C_star C_h t hq x = parameters := by
  unfold ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextRecordingView at hv
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h ⟨t.val + 1, hq⟩ x with
  | none => simp only [hr, Option.bind_none, reduceCtorEq] at hv
  | some r =>
      simp only [hr, Option.bind_some,
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.recordRecordingView] at hv
      cases hd : r.output.preparation.coordinator.downView with
      | none => simp only [hd, Option.map_none, reduceCtorEq] at hv
      | some v =>
          simp only [hd, Option.map_some, Option.some.injEq] at hv
          have hp := congrArg Prod.fst hv
          simpa only [ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters,
            ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextCell,
            hr, Option.bind_some] using hp

private theorem recording_control_mass
    (regime : SnapshotRecordingKernel.Regime p) (enabled : Bool)
    (anchor weights : Fin p.K → ℝ) (ha : ∀ j, 0 < anchor j)
    (hw : ∀ j, 0 < weights j) (hal : ∀ j, anchor j ≤ weights j)
    (hau : ∀ j, weights j ≤ 2 * anchor j) (o : Option (Option (Fin p.K))) :
    (ContinuousLearningRows.timeControlLaw p)
      {c | some (SnapshotRecordingKernel.recordingMap p regime enabled
        rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau c.1) = o} =
      ENNReal.ofReal (ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
        (some (enabled, CanonicalRecordingRates.xi p rate.eta.val anchor))) := by
  let f := SnapshotRecordingKernel.recordingMap p regime enabled
    rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau
  have hf : Measurable f := SnapshotRecordingKernel.measurable_recordingMap
    p regime rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau enabled
  have hm (a : Option (Fin p.K)) :
      (ContinuousLearningRows.timeControlLaw p) {c | f c.1 = a} =
      (ContinuousControlSlice.sliceLaw p.m p.K) {x | f x = a} := by
    rw [← ContinuousLearningRows.map_slice p,
      Measure.map_apply measurable_fst
        (show MeasurableSet {x | f x = a} from (measurableSet_singleton a).preimage hf)]
    rfl
  cases o with
  | none => simp only [reduceCtorEq, Set.ofPred_false, measure_empty,
      ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters,
      ENNReal.ofReal_zero]
  | some a =>
    simp only [Option.some.injEq]
    rw [show {c : TimeControl p | _ = a} = {c | f c.1 = a} from rfl, hm]
    cases enabled with
    | false =>
        cases a <;> simp only [f, SnapshotRecordingKernel.recordingMap_disabled,
          ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters,
          Set.ofPred_true, measure_univ, ENNReal.ofReal_one,
          reduceCtorEq, Set.ofPred_false, measure_empty, ENNReal.ofReal_zero]
    | true =>
        have hmap := SnapshotRecordingKernel.map_recordingMap
          p regime rate.eta.val rate.eta.property rate.sourceCap anchor weights ha hw hal hau
        have hsingle := congrArg (fun μ : Measure (Option (Fin p.K)) => μ {a}) hmap
        rw [Measure.map_apply hf (measurableSet_singleton a),
          PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a)] at hsingle
        cases a with
        | none => simpa only [Set.preimage, Set.mem_singleton_iff,
            RecordedRoundMoments.recordingOutcomePMF_none,
            SnapshotRecordingKernel.recordingRates,
            ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters] using hsingle
        | some j => simpa only [Set.preimage, Set.mem_singleton_iff,
            RecordedRoundMoments.recordingOutcomePMF_some,
            SnapshotRecordingKernel.recordingRates,
            ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters] using hsingle

/-- Exact unnormalized whole-control marker mass on every corrected source
point, with the absent and disabled tags kept separate. -/
theorem corrected_nextMarker_control_mass (control0 : TimeControl p) (hq : t.val + 1 < p.T)
    (x : X) (hx : x ∈ C) (o : Option (Option (Fin p.K))) :
    (ContinuousLearningRows.timeControlLaw p)
      {control | ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
          ⟨t.val + 1, hq⟩ x control) = o} =
      ENNReal.ofReal (ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
        (ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
          rate rewards C_star C_h t hq x)) := by
  have hk := corrected_firstCell_successor_marker_section
    rate rewards C_star C_h u t control0 hq x hx
  cases hv : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextRecordingView
      rate rewards C_star C_h t hq x with
  | none =>
      rw [hv] at hk
      have hn := corrected_firstCell_successor_physical_kernel
        rate rewards C_star C_h u t control0 hq x hx
      rw [hv] at hn
      have hp : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
          rate rewards C_star C_h t hq x = none := by
        unfold ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker at hn
        unfold ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
        cases hc : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextCell
            rate rewards C_star C_h t hq x with
        | none => rfl
        | some c => simp only [hc, Option.map_some, reduceCtorEq] at hn
      simp only [hk, hp]
      rcases o with _ | (_ | j) <;> simp only [
        ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters,
        Set.ofPred_true, measure_univ, ENNReal.ofReal_one, reduceCtorEq,
        Set.ofPred_false, measure_empty, ENNReal.ofReal_zero]
  | some v =>
      rcases v with ⟨parameters, view, code⟩
      rw [hv] at hk
      obtain ⟨enabled, snapshot, valid, hp, _hc, hm⟩ := hk
      have hparameters := recordingView_parameters rate rewards C_star C_h t hq x
        parameters view code hv
      have hcanonical : view.payload.rate = CanonicalRecordingRates.xi p rate.eta.val
          view.payload.anchor := funext view.payload.rate_eq_canonical
      simp only [hm, replacement_slice, hparameters, hp, hcanonical]
      exact recording_control_mass rate _ enabled _ _ view.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid) o

private theorem branch_prefix_iff (x y : X)
    (hp : sourcePrefix control0 (t.val + 1) x =
      sourcePrefix control0 (t.val + 1) y) : x ∈ C ↔ y ∈ C := by
  constructor
  · rintro ⟨hx, g, hg, hlt⟩
    have h := ReferenceFirstCollectionCorrectedNextPhysicalReadout.corrected_branch_prefix_congr
      rate rewards C_star C_h control0 u t x y hp hx g hg hlt
    exact ⟨h.1, g, h.2.1, h.2.2⟩
  · rintro ⟨hy, g, hg, hlt⟩
    have h := ReferenceFirstCollectionCorrectedNextPhysicalReadout.corrected_branch_prefix_congr
      rate rewards C_star C_h control0 u t y x hp.symm hy g hg hlt
    exact ⟨h.1, g, h.2.1, h.2.2⟩

private theorem coefficient_bounds (hq : t.val + 1 < p.T)
    (x : X) (hx : x ∈ C) (o : Option (Option (Fin p.K))) :
    0 ≤ ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
        (ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
          rate rewards C_star C_h t hq x) ∧
      ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
        (ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
          rate rewards C_star C_h t hq x) ≤ 1 := by
  cases hp : ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
      rate rewards C_star C_h t hq x with
  | none =>
      rcases o with _ | (_ | j) <;>
        simp only [ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters,
          le_refl, zero_le_one, and_self]
  | some parameters =>
      rcases parameters with ⟨enabled, xi⟩
      obtain ⟨view, _hv, hxi, _hb, hsum⟩ :=
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_nextParameters_bounds
          rate rewards C_star C_h u t hq x hx.1 enabled xi hp
      have hpos (j) : 0 ≤ xi j := by
        rw [hxi, view.payload.rate_eq_canonical]
        exact (CanonicalRecordingRates.xi_pos p rate.eta.property _ j).le
      have hn : 0 ≤ ∑ j, xi j := Finset.sum_nonneg (fun j _ => hpos j)
      have hu (j) : xi j ≤ 1 :=
        (Finset.single_le_sum (fun a _ => hpos a) (Finset.mem_univ j)).trans hsum
      rcases o with _ | (_ | j) <;> cases enabled <;>
        simp only [ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters]
      all_goals first
        | exact ⟨zero_le_one, le_refl 1⟩
        | exact ⟨le_refl 0, zero_le_one⟩
        | exact ⟨sub_nonneg.mpr hsum, sub_le_self 1 hn⟩
        | exact ⟨hpos j, hu j⟩

/-- Joint Borel measurability of the actual marker after replacing the whole
successor control, on the original source product. -/
theorem corrected_nextMarker_replaceControl_measurable (hq : t.val + 1 < p.T) :
    Measurable (fun v : X × TimeControl p =>
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
          ⟨t.val + 1, hq⟩ v.1 v.2)) :=
  (corrected_nextMarker_measurable rate rewards C_star C_h t hq).comp
    (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl
      p ⟨t.val + 1, hq⟩)

/-- The literal corrected-event marker test is integrable under the original
unrestricted source probability law, including empty and null cells. -/
theorem corrected_markerTest_integrable (control0 : TimeControl p) (hq : t.val + 1 < p.T)
    (o : Option (Option (Fin p.K))) :
    Integrable ((C).indicator (fun x =>
      if ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq x = o then (1 : ℝ) else 0))
      (sourceInputLaw p) := by
  have hC : MeasurableSet C :=
    ((sourcePrefixFiltration control0).le' (t.val + 2)) _
      (ReferenceFirstCollectionCorrectedNextRetainedGate.firstCell_successorBranch_measurable
        rate rewards C_star C_h control0 u t)
  have hM : MeasurableSet {x : X |
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq x = o} :=
    (measurableSet_singleton o).preimage
      (corrected_nextMarker_measurable rate rewards C_star C_h t hq)
  have hm : Measurable (fun x : X => if
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq x = o then (1 : ℝ) else 0) :=
    measurable_const.ite hM measurable_const
  have hi : Integrable (fun x : X => if
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq x = o then (1 : ℝ) else 0) (sourceInputLaw p) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards [] with x
    split_ifs <;> norm_num
  exact hi.indicator hC

private theorem branch_baseline_iff (hq : t.val + 1 < p.T) (x : X) :
    ReferenceSourceCurrentControlFreshness.c_t p control0 ⟨t.val + 1, hq⟩ x ∈ C ↔
      x ∈ C := by
  apply branch_prefix_iff rate rewards C_star C_h control0 u t
  rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix,
    sourcePrefix_sourcePrefix control0 _ _ le_rfl]

private theorem parameters_baseline (hq : t.val + 1 < p.T)
    (x : X) (hx : x ∈ C) :
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
        rate rewards C_star C_h t hq
        (ReferenceSourceCurrentControlFreshness.c_t p control0 ⟨t.val + 1, hq⟩ x) =
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
        rate rewards C_star C_h t hq x := by
  symm
  apply (ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCell_next_prior_congr
    rate rewards C_star C_h control0 u t hq x _ hx.1 ?_).2.2.1
  rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix,
    sourcePrefix_sourcePrefix control0 _ _ le_rfl]

private theorem integral_test_eq_of_mass {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass B] [DecidableEq B]
    (μ : Measure A) (f : A → B) (hf : Measurable f) (o : B)
    (c : ℝ) (hc : 0 ≤ c) (hmass : μ {a | f a = o} = ENNReal.ofReal c) :
    (∫ a, if f a = o then (1 : ℝ) else 0 ∂μ) = c := by
  have heq : (fun a => if f a = o then (1 : ℝ) else 0) =
      {a | f a = o}.indicator (fun _ => (1 : ℝ)) := by
    funext a
    by_cases h : f a = o <;> simp [Set.indicator, h]
  have hs : MeasurableSet {a | f a = o} := (measurableSet_singleton o).preimage hf
  rw [heq, integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one,
    measureReal_def, hmass, ENNReal.toReal_ofReal hc]

/-- Integrating the complete replacement control gives the actual optional
parameter coefficient, without normalizing any source event. -/
theorem corrected_nextMarker_control_integral (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (x : X) (hx : x ∈ C)
    (o : Option (Option (Fin p.K))) :
    (∫ control, (if ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
          ⟨t.val + 1, hq⟩ x control) = o then (1 : ℝ) else 0)
        ∂ContinuousLearningRows.timeControlLaw p) =
      ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
        (ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
          rate rewards C_star C_h t hq x) := by
  have hpair : Measurable (fun control : TimeControl p => (x, control)) :=
    measurable_const.prodMk measurable_id
  have hm := (corrected_nextMarker_replaceControl_measurable
    rate rewards C_star C_h t hq).comp hpair
  dsimp only [Function.comp_def] at hm
  exact integral_test_eq_of_mass (ContinuousLearningRows.timeControlLaw p)
    (fun control : TimeControl p =>
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
          ⟨t.val + 1, hq⟩ x control)) hm o _
    (coefficient_bounds rate rewards C_star C_h u t hq x hx o).1
    (corrected_nextMarker_control_mass rate rewards C_star C_h u t control0 hq x hx o)

private def markerTestSet (hq : t.val + 1 < p.T)
    (o : Option (Option (Fin p.K))) : Set (X × TimeControl p) :=
  {v | v.1 ∈ C ∧ ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
    rate rewards C_star C_h t hq
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
      ⟨t.val + 1, hq⟩ v.1 v.2) = o}

private theorem markerTestSet_measurable (control0 : TimeControl p) (hq : t.val + 1 < p.T)
    (o : Option (Option (Fin p.K))) :
    MeasurableSet (markerTestSet rate rewards C_star C_h u t hq o) := by
  have hC : MeasurableSet C :=
    ((sourcePrefixFiltration control0).le' (t.val + 2)) _
      (ReferenceFirstCollectionCorrectedNextRetainedGate.firstCell_successorBranch_measurable
        rate rewards C_star C_h control0 u t)
  exact (hC.preimage measurable_fst).inter ((measurableSet_singleton o).preimage
    (corrected_nextMarker_replaceControl_measurable rate rewards C_star C_h t hq))

private theorem marker_sourceControlTest (hq : t.val + 1 < p.T)
    (o : Option (Option (Fin p.K))) :
    ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 ⟨t.val + 1, hq⟩
      (markerTestSet rate rewards C_star C_h u t hq o) =
      (C).indicator (fun x => if
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
          rate rewards C_star C_h t hq x = o then (1 : ℝ) else 0) := by
  funext x
  rw [ReferenceSourceCurrentControlFreshness.sourceControlTest, Set.indicator_apply]
  rw [show (ReferenceSourceCurrentControlFreshness.c_t p control0 ⟨t.val + 1, hq⟩ x,
      ReferenceSourceCurrentControlFreshness.u_t p ⟨t.val + 1, hq⟩ x) ∈
      markerTestSet rate rewards C_star C_h u t hq o ↔
      ReferenceSourceCurrentControlFreshness.c_t p control0 ⟨t.val + 1, hq⟩ x ∈ C ∧
      ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p ⟨t.val + 1, hq⟩
          (ReferenceSourceCurrentControlFreshness.c_t p control0 ⟨t.val + 1, hq⟩ x)
          (ReferenceSourceCurrentControlFreshness.u_t p ⟨t.val + 1, hq⟩ x)) = o from Iff.rfl]
  rw [branch_baseline_iff rate rewards C_star C_h control0 u t hq x]
  by_cases hx : x ∈ C
  · rw [← corrected_nextMarker_reconstruct rate rewards C_star C_h control0 u t hq x hx]
    simp only [hx, true_and, Set.indicator_of_mem hx]
  · simp only [hx, false_and, ite_false, Set.indicator_of_notMem hx]

private theorem marker_sourceControlSection (hq : t.val + 1 < p.T)
    (o : Option (Option (Fin p.K))) (x : X) :
    (∫ control, (markerTestSet rate rewards C_star C_h u t hq o).indicator
      (fun _ => (1 : ℝ))
      (ReferenceSourceCurrentControlFreshness.c_t p control0 ⟨t.val + 1, hq⟩ x, control)
      ∂ContinuousLearningRows.timeControlLaw p) =
    (C).indicator (fun x =>
      ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
        (ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
          rate rewards C_star C_h t hq x)) x := by
  have heq : (fun control =>
      (markerTestSet rate rewards C_star C_h u t hq o).indicator (fun _ => (1 : ℝ))
        (ReferenceSourceCurrentControlFreshness.c_t p control0 ⟨t.val + 1, hq⟩ x, control)) =
    fun control => if x ∈ C then
      (if ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p ⟨t.val + 1, hq⟩
          (ReferenceSourceCurrentControlFreshness.c_t p control0 ⟨t.val + 1, hq⟩ x)
          control) = o then (1 : ℝ) else 0) else 0 := by
    funext control
    rw [Set.indicator_apply]
    rw [show (ReferenceSourceCurrentControlFreshness.c_t p control0 ⟨t.val + 1, hq⟩ x,
        control) ∈ markerTestSet rate rewards C_star C_h u t hq o ↔
        ReferenceSourceCurrentControlFreshness.c_t p control0 ⟨t.val + 1, hq⟩ x ∈ C ∧
        ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
          rate rewards C_star C_h t hq
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p ⟨t.val + 1, hq⟩
            (ReferenceSourceCurrentControlFreshness.c_t p control0 ⟨t.val + 1, hq⟩ x)
            control) = o from Iff.rfl]
    rw [branch_baseline_iff rate rewards C_star C_h control0 u t hq x]
    by_cases hx : x ∈ C <;> simp only [hx, true_and, false_and, ite_true, ite_false]
  rw [heq]
  by_cases hx : x ∈ C
  · simp only [hx, ite_true, Set.indicator_of_mem hx]
    rw [corrected_nextMarker_control_integral rate rewards C_star C_h u t control0 hq _
      ((branch_baseline_iff rate rewards C_star C_h control0 u t hq x).mpr hx) o,
      parameters_baseline rate rewards C_star C_h control0 u t hq x hx]
  · simp only [hx, ite_false, integral_zero, Set.indicator_of_notMem hx]

/-- Original-source optional recording law at the strict successor field.
The event is unnormalized, and no physical-success or positive-mass premise
is used. Both absent tags and enabled zero-arrival outcomes are retained. -/
theorem corrected_nextMarker_condExp (hq : t.val + 1 < p.T)
    (o : Option (Option (Fin p.K))) :
    (sourceInputLaw p)[(C).indicator (fun x =>
      if ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextMarker
        rate rewards C_star C_h t hq x = o then (1 : ℝ) else 0) |
      sourcePrefixFiltration control0 (t.val + 2)] =ᵐ[sourceInputLaw p]
      (C).indicator (fun x =>
        ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
          (ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
            rate rewards C_star C_h t hq x)) := by
  have h := ReferenceSourceCurrentControlFreshness.source_control_test_condExp
    control0 ⟨t.val + 1, hq⟩ (markerTestSet rate rewards C_star C_h u t hq o)
    (markerTestSet_measurable rate rewards C_star C_h u t control0 hq o)
  rw [marker_sourceControlTest rate rewards C_star C_h control0 u t hq o] at h
  have hf : sourcePrefixFiltration control0 (t.val + 2) =
      ReferenceSourceCurrentControlFreshness.m_t p control0 ⟨t.val + 1, hq⟩ :=
    ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t control0 ⟨t.val + 1, hq⟩
  rw [← hf] at h
  filter_upwards [h] with x hx
  exact hx.trans (marker_sourceControlSection rate rewards C_star C_h control0 u t hq o x)

/-- The localized coefficient is predictable in the actual successor field;
no value of the current control is exposed. -/
theorem corrected_coefficient_measurable (hq : t.val + 1 < p.T)
    (o : Option (Option (Fin p.K))) :
    Measurable[sourcePrefixFiltration control0 (t.val + 2)]
      ((C).indicator (fun x =>
        ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
          (ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
            rate rewards C_star C_h t hq x))) := by
  have hc := (ReferenceFirstCollectionRenewalNextRecordingLaw.measurable_coefficientOfParameters o).comp
    (ReferenceFirstCollectionCorrectedNextPhysicalReadout.firstCellParameters_measurable
      rate rewards C_star C_h control0 u t hq)
  have hi := hc.indicator
    (ReferenceFirstCollectionCorrectedNextRetainedGate.firstCell_successorBranch_measurable
        rate rewards C_star C_h control0 u t)
  convert hi using 1
  funext x
  by_cases hx : x ∈ C
  · simp only [Function.comp_def, Set.indicator_of_mem hx, hx.1, ite_true]
  · simp only [Set.indicator_of_notMem hx]

/-- All optional marker coefficients are integrable on the original source,
with the null and empty corrected-event cases included. -/
theorem corrected_coefficient_integrable (control0 : TimeControl p) (hq : t.val + 1 < p.T)
    (o : Option (Option (Fin p.K))) :
    Integrable ((C).indicator (fun x =>
      ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
        (ReferenceFirstCollectionCorrectedNextPhysicalReadout.nextParameters
          rate rewards C_star C_h t hq x))) (sourceInputLaw p) := by
  have hm := (corrected_coefficient_measurable rate rewards C_star C_h control0 u t hq o).mono
    ((sourcePrefixFiltration control0).le' (t.val + 2)) le_rfl
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : x ∈ C
  · rw [Set.indicator_of_mem hx, Real.norm_eq_abs,
      abs_of_nonneg (coefficient_bounds rate rewards C_star C_h u t hq x hx o).1]
    exact (coefficient_bounds rate rewards C_star C_h u t hq x hx o).2
  · simp only [Set.indicator_of_notMem hx, norm_zero, zero_le_one]

end Bandits.Support.ReferenceFirstCollectionCorrectedNextRecordingLaw
