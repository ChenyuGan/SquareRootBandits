/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalConditionalWeightedDrift
public import Bandits.Support.ReferenceFirstCollectionRenewalFutureExponentialQueueStep

import Mathlib.Tactic

/-!
# Numerical weights at future dates of the first renewal

This module connects the original optional numerical prefix with the actual
first-replacement recording view at a supported future date. The inherited
numerical replay starts before the birth cell, includes that cell once and retains every accepted suffix record. The installed grid bounds
its length and gives the numerical anchor envelope and canonical rate sum on
the original unnormalized renewal-source law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical MeasureTheory

namespace Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalWeightEnvelope

open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceFirstCollectionRenewalFutureControlLaw
open ReferenceFirstCollectionRenewalFutureExponentialIncrement
open ReferenceFirstCollectionRenewalFutureFirstReplacementView
open ReferenceFirstCollectionRenewalFutureRecordingLaw
open ReferenceFirstCollectionRenewalFutureRetainedMoments
open ReferenceFirstCollectionRenewalFutureNumericalPrefix

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" =>
  ReferenceFirstCollectionRenewalFutureControlLaw.Source rate rewards C_star C_h u t
local notation "B" =>
  ReferenceFirstCollectionRenewalControlFactor.Pair rate rewards C_star C_h u t
local notation "μ" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t
local notation "O_q" =>
  ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
    rate rewards C_star C_h u t
local notation "G_q" =>
  ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t

/-- On the unchanged pair law, the actual selected whole-cell payload is the
successful first-renewal installation, whose anchor is the existing renewal
weight. This short projection keeps the physical payload and source cell in
the witness; it does not replace them by a reconstructed sampling parameter. -/
theorem ae_wholeCell_payload_anchor :
    ∀ᵐ b : B ∂μ,
      ∃ selected : ReferenceActivePhysicalStep.Selection
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
            rate rewards C_star C_h u t b.2).input,
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
          rate rewards C_star C_h u t b.2).output.preparation.coordinator.selection =
            some selected ∧
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
            rate rewards C_star C_h u t b.2).output.preparation.coordinator.downView.map
              (fun view => view.payload) = some selected.view.payload ∧
          selected.view.payload.anchor =
            ReferenceFirstCollectionRenewalComplementMoments.v
              rate rewards C_star C_h u t b := by
  classical
  filter_upwards [
      ReferenceFirstCollectionRenewalRecordingFeedback.ae_pairLaw_actual_recording_feedback
        rate rewards C_star C_h u t,
      ReferenceFirstCollectionRenewalInstallationCoupling.ae_pairLaw_chronological_support
        rate rewards C_star C_h u t] with b hb hc
  dsimp only at hb hc
  rcases hb with ⟨d, consistent, output, hlocal, clockData, installed, selection,
    recording, serviced, _hstart, hvector, hreconstruction, hsample, hslow,
    hpayloadSlow, _hclock, hinstalled, hanchor, _hdispatch, hprep, hcut,
    _hcoord, _hrun, _hservice, _hrecording, states, memories, hstates,
    _hlive, hpending, _hunone, _hsigma, _⟩
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, hparameter, _⟩
  have hw : (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
      rate rewards C_star C_h u t b.1.1).2 =
      AssignmentScoreReconstruction.currentWeight d.out :=
    (congrArg Prod.snd hparameter).trans
      ((congrArg Prod.snd d.parameter_eq).trans
        (LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
          d.old _ d.instruction d.out d.reconstruction_eq d.renewal).1)
  have hread := ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_readout
    rate rewards C_star C_h u t b.2
  have hrecord := ReferenceFirstCollectionRenewalIncomingQueuePrefix.actual_call_record_eq
    rate rewards C_star C_h u t b.2 d
  rw [← hrecord] at hread
  obtain ⟨selected, ho, hs, _, _, _⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some _ _ _ hread
  have hview : selected.view =
      { payload := installed.registers.payload,
        pendingAtChoice := d.started.pending,
        cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u,
        complementWeights := installed.registers.complementWeights } := by
    rw [hprep, hcut] at hs
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, d.instruction_time] at hs
    rw [← hs]
  rw [← hrecord]
  refine ⟨selected, hs, ?_, ?_⟩
  · have hdown : d.record.output.preparation.coordinator.downView =
        some selected.view := by
      change d.record.output.preparation.coordinator.selection.map
        ReferenceActivePhysicalStep.Selection.view = some selected.view
      rw [hs]
      rfl
    change d.record.output.preparation.coordinator.downView.map
      (fun view => view.payload) = some selected.view.payload
    rw [hdown]
    rfl
  · rw [hview, hanchor, ← hw]
    rfl

/-- The actual numerical prefix and first-replacement view both exist on the
literal enabled, prior-clear future gate.  The returned cell is the actual
future numerical cell; its rate is the installed payload rate, which is the
canonical rate at that payload's anchor. -/
theorem Gfuture_actual_readouts (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (z : Z) (hz : z ∈ G_q q hfuture) :
    ∃ (r : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))
      (data : ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate)
      (xi : Fin p.K → ℝ) (cell : RecordedQueueRun.RoundInput p.K),
    O_q q.val z = some r ∧ r.2.1 = false ∧
        ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
          rate rewards C_star C_h u t z q hfuture = some data ∧
        ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
          rate rewards C_star C_h u t z q hfuture = some (true, xi) ∧
        data.1 = some (true, xi) ∧
        ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
          rate rewards C_star C_h u t z q hfuture = some cell ∧
        cell.enabled = true ∧ cell.rate = xi ∧
        (∀ j : Fin p.K,
          xi j = CanonicalRecordingRates.xi p rate.eta.val
            data.2.1.payload.anchor j) := by
  rcases hz with ⟨xi, hparameters, hclear⟩
  unfold ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
    ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout at hclear
  cases hread : O_q q.val z with
  | none =>
      rw [hread] at hclear
      simp at hclear
  | some r =>
      rw [hread] at hclear
      have hflag : r.2.1 = false := by
        cases r with
        | mk registers tail =>
            cases tail with
            | mk flag histories =>
                cases flag with
                | false => rfl
                | true => simp at hclear
      cases hview : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
          rate rewards C_star C_h u t z q hfuture with
      | none =>
          simp [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters,
            hview] at hparameters
      | some viewData =>
          rcases viewData with ⟨parameters, viewData⟩
          rcases viewData with ⟨view, code⟩
          have hviewParameters : parameters = some (true, xi) := by
            simpa [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters,
              hview] using hparameters
          have hactual :=
            ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
              rate rewards C_star C_h u t z q hfuture
          rw [hview] at hactual
          rcases hactual with
            ⟨cell, snapshot, valid, hcell, hparametersCell, hrate, _, _, _⟩
          have hcellParameters : (cell.enabled, cell.rate) = (true, xi) :=
            Option.some.inj (hparametersCell.symm.trans hviewParameters)
          have henabled : cell.enabled = true := congrArg Prod.fst hcellParameters
          have hrateXi : cell.rate = xi := congrArg Prod.snd hcellParameters
          have hpayloadRate : view.payload.rate = xi := hrate.symm.trans hrateXi
          refine ⟨r, (parameters, (view, code)), xi, cell, ?_⟩
          constructor
          · rfl
          constructor
          · exact hflag
          constructor
          · rfl
          constructor
          · simpa [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters,
              hview] using hviewParameters
          constructor
          · exact hviewParameters
          constructor
          · exact hcell
          constructor
          · exact henabled
          constructor
          · exact hrateXi
          · intro j
            calc
              xi j = view.payload.rate j := congrFun hpayloadRate.symm j
              _ = CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor j :=
                view.payload.rate_eq_canonical j

private theorem futureRecordingView_actual_downView (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (z : Z)
    (data : ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate)
    (hdata : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture = some data) :
    ∃ view : ReferenceDownReception.ChoiceTimeView p rate.eta,
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureDownView
        rate rewards C_star C_h u t z q hfuture = some view ∧ data.2.1 = view := by
  cases hbranch : ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      simp [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView,
        hbranch] at hdata
  | some branch =>
      have hdata' := hdata
      simp only [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView,
        hbranch, Option.elim_some,
        ReferenceFirstCollectionRenewalFutureFirstReplacementView.viewOnBranch] at hdata'
      cases hdown : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureDownView
          rate rewards C_star C_h u t z q hfuture with
      | none => simp [hdown] at hdata'
      | some view =>
          simp only [hdown, Option.map_some] at hdata'
          have hpair : (ReferenceFirstCollectionRenewalNextRecordingPriorView.parametersOfTag
              rate q
                (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureTag
                  rate rewards C_star C_h u t z q hfuture) (some view), view,
              if branch then none else some (view.pendingAtChoice,
                ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureStatuses
                  rate rewards C_star C_h u t z q hfuture)) = data := by
            exact Option.some.inj hdata'
          exact ⟨view, rfl, (congrArg (fun d :
            ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate => d.2.1)
            hpair).symm⟩

/-- The future recording view's payload is the one in the literal DOWN
projection of the source renewal call. The continuing and first-cutoff
branches use their respective actual recorder readouts. -/
theorem futureView_payload_eq_callDownView (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (z : Z)
    (data : ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate)
    (hdata : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture = some data) :
    (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
      rate rewards C_star C_h u t z).output.preparation.coordinator.downView.map
        (fun view => view.payload) = some data.2.1.payload := by
  obtain ⟨view, hview, hdataView⟩ :=
    futureRecordingView_actual_downView rate rewards C_star C_h u t q hfuture z data hdata
  cases hbranch : ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
      rate rewards C_star C_h u t z q hfuture with
  | none => simp [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView,
      hbranch] at hdata
  | some branch =>
      cases branch with
      | false =>
          have hgeometry := ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch_geometry
            rate rewards C_star C_h u t z q hfuture false hbranch
          obtain ⟨cell, _, _, _, _, _, _, _, hinstalled⟩ :=
            ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_live_readout
              rate rewards C_star C_h u t z q hfuture (hgeometry.1 rfl)
          have hfutureView :
              ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureDownView
                rate rewards C_star C_h u t z q hfuture = some cell.selected.view := by
            simp only [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureDownView,
              ReferenceActivePhysicalStep.DispatchCut.downView, cell.selection_actual,
              Option.map_some]
          have hsame : view = cell.selected.view :=
            Option.some.inj (hview.symm.trans hfutureView)
          have hdataCell : data.2.1 = cell.selected.view := hdataView.trans hsame
          rw [hdataCell]
          exact hinstalled.2
      | true =>
          have hgeometry := ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch_geometry
            rate rewards C_star C_h u t z q hfuture true hbranch
          have hcutPrepared :=
            ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_cutoff_prepared
              rate rewards C_star C_h u t z q hfuture (hgeometry.2 rfl)
          have hlen : q.val - (t.val + 1) ≤
              (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
                rate rewards C_star C_h u t z).length := by
            rw [hgeometry.2 rfl]
          have htag := hbranch
          simp only [ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch,
            ite_eq_left hlen,
            ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureTag_eq] at htag
          cases hcoord : (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
              rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator with
          | live registers owned base outcome =>
              simp only [hcoord] at htag
              cases outcome with
              | cutoffChosen dispatched _ _ _ _ _ _ _ _ selected =>
                  simp only [hcoord] at hcutPrepared
                  obtain ⟨_, _, _, _, hcallPayload⟩ := hcutPrepared
                  have hcutReadout :=
                    ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_cutoff_readout
                      rate rewards C_star C_h u t z q hfuture (hgeometry.2 rfl)
                  simp only [hcoord] at hcutReadout
                  have hactualEndpoint : ∃ c : RecordedQueueRun.RoundInput p.K,
                      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
                        (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
                          rate rewards C_star C_h u t z q hfuture) = some c ∧
                      c.rate = registers.payload.rate := by
                    obtain ⟨c, _, hzero, _, hrate, _, _, _⟩ := hcutReadout
                    exact ⟨c, hzero, hrate⟩
                  obtain ⟨actualCell, hactualCell, hactualRate⟩ := hactualEndpoint
                  have hpayload : view.payload = registers.payload := by
                    have hviewPayload :
                        (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureDownView
                          rate rewards C_star C_h u t z q hfuture).map
                          (fun v => v.payload) = some registers.payload := by
                      simp only [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureDownView,
                        hcoord, ReferenceActivePhysicalStep.DispatchCut.downView,
                        ReferenceActivePhysicalStep.DispatchCut.selection,
                        ReferenceActivePhysicalStep.selectionAt, dite_true, Option.map_some]
                    have hproj := congrArg (Option.map (fun v :
                      ReferenceDownReception.ChoiceTimeView p rate.eta => v.payload) ) hview
                    rw [hviewPayload] at hproj
                    simp only [Option.map_some] at hproj
                    exact (Option.some.inj hproj).symm
                  rw [hdataView, hpayload]
                  exact hcallPayload
              | continuingChosen _ _ _ _ =>
                  simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
                    ReferenceLiveDispatchOutputMeasurability.outcomeData] at htag
                  simp at htag
              | _ =>
                  simp only [ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
                    ReferenceLiveDispatchOutputMeasurability.outcomeData] at htag
                  simp at htag
          | _ => simp [hcoord] at htag

private theorem calendarCells_add (n m : ℕ) (z : Z)
    (hstart : ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
        rate rewards C_star C_h u t z ≤ n) :
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t (n + m) z =
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t n z ++
        (((ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
          rate rewards C_star C_h u t z).drop
            (n - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
              rate rewards C_star C_h u t z)).take m).map
                (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate) := by
  unfold ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
  have hsub : n + m - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
      rate rewards C_star C_h u t z =
        (n - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z) + m := by omega
  rw [hsub, List.take_add, List.map_append]

private theorem execute_overflow_false_implies {K : ℕ}
    (qp : RecordedQueueRun.Parameters)
    (rounds : List (RecordedQueueRun.RoundInput K))
    (state : RecordedQueueRun.RunState K)
    (h : (RecordedQueueRun.execute qp rounds state).overflow = false) :
    state.overflow = false := by
  induction rounds generalizing state with
  | nil => simpa [RecordedQueueRun.execute] using h
  | cons round rounds ih =>
      have hstep : (RecordedQueueRun.step qp state round).overflow = false :=
        ih (RecordedQueueRun.step qp state round) h
      cases hs : state.overflow <;>
        simp [RecordedQueueRun.step, hs] at hstep ⊢

private theorem execute_append {K : ℕ}
    (qp : RecordedQueueRun.Parameters)
    (left right : List (RecordedQueueRun.RoundInput K))
    (state : RecordedQueueRun.RunState K) :
    RecordedQueueRun.execute qp (left ++ right) state =
      RecordedQueueRun.execute qp right (RecordedQueueRun.execute qp left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons cell left ih =>
      simp only [List.cons_append, RecordedQueueRun.execute]
      exact ih _

private theorem run_append_execute {K : ℕ}
    (qp : RecordedQueueRun.Parameters)
    (pre suffix : List (RecordedQueueRun.RoundInput K)) :
    RecordedQueueRun.run qp (pre ++ suffix) =
      RecordedQueueRun.execute qp suffix (RecordedQueueRun.run qp pre) := by
  unfold RecordedQueueRun.run
  exact execute_append qp pre suffix (RecordedQueueRun.initialState K)

/-- A clear actual future prefix forces the literal inherited whole post to
have been clear already. The proof splits the actual optional calendar cells
at `t+1`; the whole birth cell occurs once in the inherited prefix, and later
cells are only executed as its suffix. -/
theorem Gfuture_implies_wholePost_clear (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (z : Z)
    (hz : z ∈ G_q q hfuture) :
    (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
      rate rewards C_star C_h u t z).2.1 = false := by
  obtain ⟨r, data, xi, cell, hO, hflag, hview, hparameters,
    hdataParameters, hcell, henabled, hrate, hcanonical⟩ :=
      Gfuture_actual_readouts rate rewards C_star C_h u t q hfuture z hz
  let current := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
    rate rewards C_star C_h u t z
  obtain ⟨inputs, hcellsQ, hrunQ⟩ : ∃ inputs,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t q.val z) =
        some inputs ∧
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputs) = r := by
    change ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout rate
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t q.val z) = some r at hO
    unfold ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout at hO
    cases hx : ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t q.val z) with
    | none => simp [hx] at hO
    | some inputs =>
        simp only [hx, Option.map_some, Option.some.injEq] at hO
        exact ⟨inputs, rfl, hO⟩
  have hsplitCells :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t q.val z =
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t (t.val + 1) z ++
        (((ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
          rate rewards C_star C_h u t z).drop
          (t.val + 1 - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
            rate rewards C_star C_h u t z)).take
            (q.val - (t.val + 1))).map
              (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate) := by
    have hstart := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
      rate rewards C_star C_h u t z
    have hadd : q.val = (t.val + 1) + (q.val - (t.val + 1)) := by omega
    have hsub : (t.val + 1) + (q.val - (t.val + 1)) - (t.val + 1) =
        q.val - (t.val + 1) := by omega
    rw [hadd]
    rw [hsub]
    exact calendarCells_add rate rewards C_star C_h u t (t.val + 1)
      (q.val - (t.val + 1)) z (by omega)
  let tailCells := (((ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
    rate rewards C_star C_h u t z).drop
      (t.val + 1 - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
        rate rewards C_star C_h u t z)).take
          (q.val - (t.val + 1))).map
            (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate)
  have htail : ∃ suffix,
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells tailCells =
        some suffix ∧ inputs = current ++ suffix := by
    rw [hsplitCells] at hcellsQ
    change List.mapM id
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t (t.val + 1) z ++ tailCells) =
        some inputs at hcellsQ
    have hprefixMap : List.mapM id
        (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
          rate rewards C_star C_h u t (t.val + 1) z) = some current := by
      change ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
          (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
            rate rewards C_star C_h u t (t.val + 1) z) = some current
      exact ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells_current_mapM
        rate rewards C_star C_h u t z
    simp only [List.mapM_append, hprefixMap] at hcellsQ
    cases hs : List.mapM id tailCells with
    | none => simp [hs] at hcellsQ
    | some suffix =>
        refine ⟨suffix, ?_, ?_⟩
        · change List.mapM id tailCells = some suffix
          exact hs
        · have hx : some (current ++ suffix) = some inputs := by
            simpa [hs] using hcellsQ
          exact (Option.some.inj hx).symm
  obtain ⟨suffix, htailMap, hall⟩ := htail
  have hstate : r = ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (current ++ suffix)) := by
    rw [hall] at hrunQ
    exact hrunQ.symm
  have hfinal : (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (current ++ suffix)).overflow = false := by
    have hproj := congrArg
      (fun s : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))) => s.2.1)
      hstate
    change r.2.1 =
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (current ++ suffix)).overflow at hproj
    rw [hflag] at hproj
    exact hproj.symm
  have hcurrent : (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      current).overflow = false := by
    have hfinal' := hfinal
    rw [run_append_execute] at hfinal'
    exact execute_overflow_false_implies _ _ _ hfinal'
  have hwhole : (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      current).overflow =
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
          rate rewards C_star C_h u t z).2.1 := by
    have hfull := ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout_fullPrefix
      rate rewards C_star C_h u t z
    exact (congrArg (fun x :
      (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))) => x.2.1)
      (by simpa [current,
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells]
        using hfull)).symm
  rw [hwhole] at hcurrent
  exact hcurrent

/-- The same clear future prefix also proves that the pre-birth incoming run
was clear: the actual renewal cell is an enabled update, and overflow is
absorbing under the recorded run. -/
theorem Gfuture_implies_incoming_clear (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (z : Z)
    (hz : z ∈ G_q q hfuture) :
    (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t z).overflow = false := by
  have hpost := Gfuture_implies_wholePost_clear rate rewards C_star C_h u t q hfuture z hz
  rw [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout_projections] at hpost
  cases hin : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t z).overflow <;>
    simp [RecordedQueueRun.step, hin] at hpost ⊢

/-- The literal future prior-clear event forces the retained incoming
no-overflow event almost everywhere on the unchanged pair law. This obtains
the event from the full numerical prefix; it is not an extra feasibility
premise. -/
theorem ae_Gfuture_implies_G_R (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    ∀ᵐ b : B ∂μ,
      b.2 ∈ G_q q hfuture →
        b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
          rate rewards C_star C_h u t control0 := by
  filter_upwards [ReferenceFirstCollectionRenewalIncomingQueuePrefix.ae_actual_incoming_factor
    rate rewards C_star C_h u t control0] with b hfactor
  intro hgate
  change (ReferenceFirstCollectionRenewalIncomingQueuePrefix.retainedIncoming
    rate rewards C_star C_h u t control0 b).overflow = false
  rw [← hfactor.2.1]
  exact Gfuture_implies_incoming_clear rate rewards C_star C_h u t q hfuture b.2 hgate

/-- On the same pair law and literal future gate, the actual incoming
numerical weight equals the anchor of the payload selected by the genuine
whole renewal cell. -/
theorem ae_Gfuture_incoming_weight_eq_wholeCell_anchor
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    ∀ᵐ b : B ∂μ,
      b.2 ∈ G_q q hfuture →
        ∃ selected : ReferenceActivePhysicalStep.Selection
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
            rate rewards C_star C_h u t b.2).input,
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
            rate rewards C_star C_h u t b.2).output.preparation.coordinator.selection =
              some selected ∧
          ∀ j : Fin p.K,
            ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
              rate rewards C_star C_h u t control0 j b = selected.view.payload.anchor j := by
  filter_upwards [
      ae_Gfuture_implies_G_R rate rewards C_star C_h u t control0 q hfuture,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.ae_wMinus_eq_renewalAnchor
        rate rewards C_star C_h u t control0,
      ae_wholeCell_payload_anchor rate rewards C_star C_h u t] with b hGR hweight hpayload
  intro hgate
  have hG : b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
      rate rewards C_star C_h u t control0 := hGR hgate
  obtain ⟨selected, hselected, hdown, hanchor⟩ := hpayload
  refine ⟨selected, hselected, ?_⟩
  intro j
  calc
    ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
        rate rewards C_star C_h u t control0 j b =
      ReferenceFirstCollectionRenewalComplementMoments.v
        rate rewards C_star C_h u t b j := hweight hG j
    _ = selected.view.payload.anchor j := (congrFun hanchor j).symm

/-- On the same original pair law, the literal future gate retains the actual
numerical prefix, actual future view/cell, and actual whole-cell selection;
the future view's installed anchor is the same anchor selected at renewal. -/
theorem ae_Gfuture_futureView_anchor_eq_wholeCell_anchor
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    ∀ᵐ b : B ∂μ,
      b.2 ∈ G_q q hfuture →
        ∃ (r : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))
          (data : ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate)
          (xi : Fin p.K → ℝ) (cell : RecordedQueueRun.RoundInput p.K)
          (selected : ReferenceActivePhysicalStep.Selection
            (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
              rate rewards C_star C_h u t b.2).input),
          O_q q.val b.2 = some r ∧ r.2.1 = false ∧
          ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
            rate rewards C_star C_h u t b.2 q hfuture = some data ∧
          ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
            rate rewards C_star C_h u t b.2 q hfuture = some (true, xi) ∧
          data.1 = some (true, xi) ∧
          ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
            rate rewards C_star C_h u t b.2 q hfuture = some cell ∧
          cell.enabled = true ∧ cell.rate = xi ∧
          (∀ j : Fin p.K, xi j = CanonicalRecordingRates.xi p rate.eta.val
            data.2.1.payload.anchor j) ∧
          (∀ j : Fin p.K,
            ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
              rate rewards C_star C_h u t control0 j b = data.2.1.payload.anchor j) ∧
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
            rate rewards C_star C_h u t b.2).output.preparation.coordinator.selection =
              some selected ∧
          (∀ j : Fin p.K,
            data.2.1.payload.anchor j = selected.view.payload.anchor j) := by
  filter_upwards [
      ae_wholeCell_payload_anchor rate rewards C_star C_h u t,
      ae_Gfuture_incoming_weight_eq_wholeCell_anchor rate rewards C_star C_h u t
        control0 q hfuture] with b hpayload hweight
  intro hgate
  obtain ⟨r, data, xi, cell, hO, hflag, hdata, hparams, hdataParams,
    hcell, henabled, hrate, hcanonical⟩ :=
      Gfuture_actual_readouts rate rewards C_star C_h u t q hfuture b.2 hgate
  have hviewPayload := futureView_payload_eq_callDownView rate rewards C_star C_h u t
    q hfuture b.2 data hdata
  obtain ⟨selected, hselected, hdown, hanchor⟩ := hpayload
  obtain ⟨selectedWeight, hselectedWeight, hweightAnchor⟩ := hweight hgate
  have hselectedEq : selectedWeight = selected := by
    rw [hselectedWeight] at hselected
    exact Option.some.inj hselected
  have hsame : data.2.1.payload = selected.view.payload :=
    Option.some.inj (hviewPayload.symm.trans hdown)
  refine ⟨r, data, xi, cell, selected, hO, hflag, hdata, hparams, hdataParams,
    hcell, henabled, hrate, hcanonical, ?_, hselected, ?_⟩
  · intro j
    calc
      ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
          rate rewards C_star C_h u t control0 j b = selectedWeight.view.payload.anchor j :=
        hweightAnchor j
      _ = data.2.1.payload.anchor j := by
        rw [hselectedEq]
        exact congrFun (congrArg (fun payload => payload.anchor) hsame).symm j
  · intro j
    have hanchors := congrArg (fun payload => payload.anchor) hsame
    exact congrFun hanchors j

private theorem mapM_id_length {α : Type*} (cells : List (Option α))
    (inputs : List α) (h : cells.mapM id = some inputs) :
    inputs.length = cells.length := by
  induction cells generalizing inputs with
  | nil => simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst inputs; rfl
  | cons cell cells ih =>
      cases cell with
      | none => simp at h
      | some cell =>
          cases hs : cells.mapM id with
          | none => simp [List.mapM_cons, hs] at h
          | some tail =>
              have heq : cell :: tail = inputs := by
                simpa [List.mapM_cons, hs] using h
              subst inputs
              simpa only [List.length_cons] using congrArg Nat.succ (ih tail hs)

private theorem execute_records_suffix {K : ℕ}
    (qp : RecordedQueueRun.Parameters) (rounds : List (RecordedQueueRun.RoundInput K))
    (state : RecordedQueueRun.RunState K) (j : Fin K) :
    ∃ word : List (Bool × ℕ), word.length = rounds.length ∧
      (RecordedQueueRun.execute qp rounds state).records j = state.records j ++ word := by
  induction rounds generalizing state with
  | nil => exact ⟨[], rfl, (List.append_nil _).symm⟩
  | cons cell rounds ih =>
      obtain ⟨word, hlen, hrecords⟩ := ih (RecordedQueueRun.step qp state cell)
      refine ⟨RecordedQueueRun.acceptedRecord qp state cell j :: word, ?_, ?_⟩
      · simpa only [List.length_cons] using congrArg Nat.succ hlen
      · change (RecordedQueueRun.execute qp rounds
          (RecordedQueueRun.step qp state cell)).records j = _
        rw [hrecords]
        change (state.records j ++ [RecordedQueueRun.acceptedRecord qp state cell j]) ++ word = _
        rw [List.append_assoc]
        rfl

/-- Literal optional calendar suffix strictly after the birth cell and before
`q`. The birth cell is supplied separately, exactly once, in the replay below. -/
def postBirthCells (q : Fin p.T) (z : Z) :
    List (Option (RecordedQueueRun.RoundInput p.K)) :=
  (((ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
    rate rewards C_star C_h u t z).drop
      (t.val + 1 - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
        rate rewards C_star C_h u t z)).take (q.val - (t.val + 1))).map
          (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate)

/-- Exact replay from the generally nonzero incoming registers. The emitted
word contains the actual birth update followed by every accepted suffix
record, including disabled and post-overflow no-ops. Its length is bounded
by the original calendar interval, with no compression of absent positions. -/
theorem futurePrefix_actual_replay (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (z : Z)
    (r : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))
    (hread : O_q q.val z = some r) :
    ∃ suffix : List (RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
        (postBirthCells rate rewards C_star C_h u t q z) = some suffix ∧
      suffix.length ≤ q.val - (t.val + 1) ∧
      r = ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.execute (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
            rate rewards C_star C_h u t z :: suffix)
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
            rate rewards C_star C_h u t z)) ∧
      ∀ j : Fin p.K, ∃ word : List (Bool × ℕ),
        word.length = suffix.length + 1 ∧ word.length ≤ q.val - t.val ∧
        r.2.2 j = (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
          rate rewards C_star C_h u t z).records j ++ word ∧
        r.1 j = QueueReplay.replay (4 * rate.n)
          ((ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
            rate rewards C_star C_h u t z).registers j) word := by
  let current := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
    rate rewards C_star C_h u t z
  have hstart := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
    rate rewards C_star C_h u t z
  have hsplit : ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t q.val z =
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t (t.val + 1) z ++
        postBirthCells rate rewards C_star C_h u t q z := by
    have heq : q.val = (t.val + 1) + (q.val - (t.val + 1)) := by omega
    conv_lhs => rw [heq]
    exact calendarCells_add rate rewards C_star C_h u t (t.val + 1)
      (q.val - (t.val + 1)) z (by omega)
  change ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout rate
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t q.val z) = some r at hread
  rw [hsplit] at hread
  unfold ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout at hread
  have hmap : ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t (t.val + 1) z ++
        postBirthCells rate rewards C_star C_h u t q z) =
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
        (postBirthCells rate rewards C_star C_h u t q z)).map (current ++ ·) := by
    change List.mapM id (_ ++ _) = _
    rw [List.mapM_append]
    have hc := ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells_current_mapM
      rate rewards C_star C_h u t z
    change List.mapM id _ = some current at hc
    rw [hc]
    change _ = (List.mapM id (postBirthCells rate rewards C_star C_h u t q z)).map _
    cases List.mapM id (postBirthCells rate rewards C_star C_h u t q z) <;> rfl
  rw [hmap] at hread
  cases hs : ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
      (postBirthCells rate rewards C_star C_h u t q z) with
  | none => simp [hs] at hread
  | some suffix =>
      simp only [hs, Option.map_some, Option.some.injEq] at hread
      have hlen : suffix.length ≤ q.val - (t.val + 1) := by
        have hl := mapM_id_length _ suffix hs
        rw [hl]
        exact (List.length_map _).trans_le (List.length_take_le _ _)
      have hstate : r = ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.execute (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
              rate rewards C_star C_h u t z :: suffix)
            (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
              rate rewards C_star C_h u t z)) := by
        rw [← hread]
        change ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run _ ((_ ++ [_]) ++ suffix)) = _
        rw [List.append_assoc]
        rw [run_append_execute]
        rfl
      refine ⟨suffix, rfl, hlen, hstate, ?_⟩
      intro j
      obtain ⟨word, hword, hrecords⟩ := execute_records_suffix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t z :: suffix)
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
          rate rewards C_star C_h u t z) j
      have hword' : word.length = suffix.length + 1 := by
        simpa only [List.length_cons] using hword
      refine ⟨word, hword', by omega, ?_, ?_⟩
      · rw [hstate]; exact hrecords
      · rw [hstate]
        have hfinal := RecordedQueueRun.run_replay_projection
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
            rate rewards C_star C_h u t z ++
            ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
              rate rewards C_star C_h u t z :: suffix) j
        unfold ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming at hrecords
        rw [run_append_execute, hrecords, QueueReplay.replay_append] at hfinal
        have hincoming := RecordedQueueRun.run_replay_projection
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
            rate rewards C_star C_h u t z) j
        rw [← hincoming] at hfinal
        exact hfinal

private theorem actual_birth_shape (z : Z) :
    match (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
        rate rewards C_star C_h u t z).output.preparation.coordinator with
    | .collection _ _ _ _ (.laterChosen ..) => True
    | _ => False := by
  obtain ⟨d, consistent, output, hlocal, _hstart, _hvector, _hreconstruction,
    _hslow, _hslowSet, _hinstalledPayload, _hinstalledVector, _hinstalledReconstruction,
    _hanchor, _hqueues, _hretained, selection, _hchoice, hdispatch, hprep, hcoord,
    _harm, _hpost⟩ :=
    ReferenceFirstCollectionRenewalSampleInstallation.actual_renewal_call_installation
      rate rewards C_star C_h u t z
  have heq := ReferenceFirstCollectionRenewalIncomingQueuePrefix.actual_call_record_eq
    rate rewards C_star C_h u t z d
  have hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
        rate rewards C_star C_h u t z).input = true := by
    rw [← heq]
    unfold ReferenceCollectionPhaseHistory.laterChosen
    rw [← hprep, hcoord, hdispatch]
  unfold ReferenceCollectionPhaseHistory.laterChosen at hb
  have hp : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
        rate rewards C_star C_h u t z).output.preparation =
      ReferenceActivePhysicalStep.prepare (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
        rate rewards C_star C_h u t z).input := by
    rw [(ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
      rate rewards C_star C_h u t z).output_eq]
    rfl
  rw [← hp] at hb
  cases h : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
      rate rewards C_star C_h u t z).output.preparation.coordinator
    <;> simp only [h] at hb ⊢ <;> try contradiction
  rename_i outcome
  cases outcome <;> simp_all

/-- The actual slice selector ensures that the last pre-q continuing record
is still before the installed grid boundary. This includes the first cutoff
endpoint and uses one-based source dates, so the birth update is counted. -/
theorem futureView_calendar_bound (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (z : Z)
    (data : ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate)
    (hdata : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture = some data) :
    q.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val t := by
  have hlength : q.val - (t.val + 1) ≤
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
        rate rewards C_star C_h u t z).length := by
    cases hb : ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch
        rate rewards C_star C_h u t z q hfuture with
    | none => simp [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView,
        hb] at hdata
    | some branch =>
        have hg := ReferenceFirstCollectionRenewalFutureFirstReplacementView.sliceBranch_geometry
          rate rewards C_star C_h u t z q hfuture branch hb
        cases branch with
        | false => exact (hg.1 rfl).le
        | true => exact (hg.2 rfl).le
  have hg := ReferenceFirstReplacementLiveFollowerPrefix.complete_first_replacement_continuing_geometry
    rate z.val rewards C_star C_h
  have hi := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.firstReplacementIndex_eq
    rate rewards C_star C_h u t z
  have h0 : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
      rate rewards C_star C_h u t z)[t.val -
        ReferenceFirstCollectionRenewalIncomingQueuePrefix.start rate rewards C_star C_h u t z]? =
      some (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
        rate rewards C_star C_h u t z) :=
    List.getElem?_eq_getElem (ReferenceFirstCollectionRenewalIncomingQueuePrefix.call_index_lt
      rate rewards C_star C_h u t z)
  dsimp only [ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords] at hi h0
  dsimp only at hg
  simp only [hi, h0] at hg
  have hb := actual_birth_shape rate rewards C_star C_h u t z
  cases hc : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
      rate rewards C_star C_h u t z).output.preparation.coordinator
    <;> simp only [hc] at hb hg
  rename_i outcome
  cases outcome <;> try contradiction
  obtain ⟨hsigma, hgeometry⟩ := hg
  rw [hi] at hgeometry
  let k : Fin (ReferenceFirstCollectionRenewalFutureFirstReplacementView.continuingRecords
      rate rewards C_star C_h u t z).length := ⟨q.val - (t.val + 1) - 1, by omega⟩
  obtain ⟨_, htime, _, _, _, selected, _, _, _, hgrid, _⟩ := hgeometry k
  have hbirthTime := congrArg Fin.val
    (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord_time
      rate rewards C_star C_h u t z)
  have hsigma' : _ = t := Fin.ext (hsigma.trans hbirthTime)
  rw [hsigma'] at hgrid
  rw [htime, hbirthTime] at hgrid
  dsimp only [k] at hgrid
  omega

/-- The literal clipped grid gives the required replay horizon, including
all off-by-one shifts between table coordinates and source dates. -/
theorem futureView_episode_length_bound (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (z : Z)
    (data : ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate)
    (hdata : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture = some data) :
    q.val - t.val ≤ ReplayWeightStability.episodeHorizon rate.eta.val := by
  have hgrid := futureView_calendar_bound rate rewards C_star C_h u t q hfuture z data hdata
  have hclip := Nat.min_le_right (p.T + 1)
    (ReplayWeightStability.episodeHorizon rate.eta.val *
      ((t.val + 1) / ReplayWeightStability.episodeHorizon rate.eta.val + 1))
  change q.val + 1 ≤ min (p.T + 1) _ at hgrid
  have hdiv := Nat.div_mul_le_self (t.val + 1)
    (ReplayWeightStability.episodeHorizon rate.eta.val)
  have hbound := hgrid.trans hclip
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm _ ((t.val + 1) / _)] at hbound
  omega

/-- The full numerical score vector has the source replay envelope relative
to the pre-birth incoming weights. No physical complement weight is used. -/
theorem futurePrefix_incoming_weight_envelope (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (z : Z)
    (r : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))
    (data : ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate)
    (hread : O_q q.val z = some r)
    (hdata : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture = some data) :
    ∀ j : Fin p.K,
      RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
            rate rewards C_star C_h u t z) j ≤
        (1 + 1 / (D p : ℝ)) ^ (r.1 j).1 ∧
      (1 + 1 / (D p : ℝ)) ^ (r.1 j).1 ≤
        2 * RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
            rate rewards C_star C_h u t z) j := by
  obtain ⟨suffix, _, _, _, hwords⟩ := futurePrefix_actual_replay
    rate rewards C_star C_h u t q hfuture z r hread
  have hH := futureView_episode_length_bound rate rewards C_star C_h u t q hfuture z data hdata
  intro j
  obtain ⟨word, _, hlen, _, hreplay⟩ := hwords j
  have henvelope := ReplayWeightStability.replay_source_weight_envelope
    (score := ((ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t z).registers j).1)
    (backlog := ((ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t z).registers j).2)
    (D_pos p) rate.eta.val rate.eta.property rate.n_scale.symm word (hlen.trans hH)
  rw [hreplay]
  exact henvelope

private theorem measurable_view_anchor :
    Measurable (fun data : ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate =>
      data.2.1.payload.anchor) := by
  have hv : Measurable (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
      (p := p) (rate := rate)) := comap_measurable _
  have hp : Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload) := measurable_fst.comp hv
  have ho := (ReferenceCollectionDispatchMeasurability.measurable_payloadObservation
    (p := p) (rate := rate)).comp hp
  have ha : Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload.anchor) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp ho)))
  exact ha.comp (measurable_fst.comp measurable_snd)

private theorem measurable_option_elim {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (f : α → β) (hf : Measurable f) (b : β) :
    Measurable (fun o : Option α => o.elim b f) := by
  have hsum : Measurable (fun o : Option α => Equiv.optionEquivSumPUnit α o) :=
    comap_measurable _
  convert (hf.sumElim measurable_const).comp hsum using 1
  funext o
  cases o <;> rfl

/-- The actual incoming numerical weights equal the future installed anchor
on the original finite, unnormalized renewal-source law. The event is derived
from the same literal future gate; no probability normalization is needed. -/
theorem ae_Gfuture_incoming_weight_eq_future_anchor
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    ∀ᵐ z : Z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t,
      z ∈ G_q q hfuture →
      ∀ data : ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate,
        ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
          rate rewards C_star C_h u t z q hfuture = some data →
        ∀ j : Fin p.K,
          RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
              rate rewards C_star C_h u t z) j = data.2.1.payload.anchor j := by
  let anchorRead : Z → Fin p.K → ℝ := fun z =>
    (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture).elim (fun _ => 0)
        (fun data => data.2.1.payload.anchor)
  let incomingWeight : Z → Fin p.K → ℝ := fun z j =>
    RecordedQueueRun.scoreWeight (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t z) j
  have ha : Measurable anchorRead :=
    (measurable_option_elim _ (measurable_view_anchor rate) (fun _ => 0)).comp
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.measurable_futureRecordingView_ambient
        rate rewards C_star C_h u t control0 q hfuture)
  have hw : Measurable incomingWeight :=
    (measurable_of_countable (fun registers : Fin p.K → ℕ × ℕ =>
      fun j => (1 + 1 / (D p : ℝ)) ^ (registers j).1)).comp
        (measurable_fst.comp
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
            rate rewards C_star C_h u t))
  have hG : MeasurableSet (G_q q hfuture) :=
    (ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
      rate rewards C_star C_h u t control0 q (by omega)) _
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
        rate rewards C_star C_h u t q hfuture control0)
  have hmeas : MeasurableSet {z : Z | z ∈ G_q q hfuture → anchorRead z = incomingWeight z} := by
    have heq : {z : Z | z ∈ G_q q hfuture → anchorRead z = incomingWeight z} =
        (G_q q hfuture)ᶜ ∪ {z | anchorRead z = incomingWeight z} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]
    rw [heq]
    exact hG.compl.union (measurableSet_eq_fun ha hw)
  have hpair : ∀ᵐ b : B ∂μ,
      b.2 ∈ G_q q hfuture → anchorRead b.2 = incomingWeight b.2 := by
    filter_upwards [ae_Gfuture_futureView_anchor_eq_wholeCell_anchor
      rate rewards C_star C_h u t control0 q hfuture] with b hb
    intro hz
    obtain ⟨r, data, xi, cell, selected, _, _, hview, _, _, _, _, _, _, hweights, _⟩ := hb hz
    funext j
    dsimp only [anchorRead]
    rw [hview]
    exact (hweights j).symm
  have hsource : ∀ᵐ z : Z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
      rate rewards C_star C_h u t,
      z ∈ G_q q hfuture → anchorRead z = incomingWeight z := by
    rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
      rate rewards C_star C_h u t]
    exact (MeasureTheory.ae_map_iff measurable_snd.aemeasurable hmeas).mpr hpair
  filter_upwards [hsource] with z hz
  intro hgate data hdata j
  have heq := congrFun (hz hgate) j
  dsimp only [anchorRead] at heq
  rw [hdata] at heq
  exact heq.symm

private theorem mapM_id_eq_map_some {α : Type*} (cells : List (Option α))
    (inputs : List α) (h : cells.mapM id = some inputs) : cells = inputs.map some := by
  induction cells generalizing inputs with
  | nil => simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst inputs; rfl
  | cons cell cells ih =>
      cases cell with
      | none => simp at h
      | some cell =>
          cases hs : cells.mapM id with
          | none => simp [List.mapM_cons, hs] at h
          | some tail =>
              have heq : cell :: tail = inputs := by simpa [List.mapM_cons, hs] using h
              subst inputs
              rw [List.map_cons, ih tail hs]

/-- The actual optional prefix immediately before the birth cell is present
and is the complete inherited incoming readout, including its full histories. -/
theorem calendarCells_incoming_readout (z : Z) :
    O_q t.val z = some (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
      rate rewards C_star C_h u t z) := by
  have hstart := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
    rate rewards C_star C_h u t z
  have htake : ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t t.val z =
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t (t.val + 1) z).take
          (t.val - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
            rate rewards C_star C_h u t z) := by
    simp only [ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells,
      ← List.map_take, List.take_take]
    rw [Nat.min_eq_left (by omega)]
  have hcurrent := mapM_id_eq_map_some _ _
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells_current_mapM
      rate rewards C_star C_h u t z)
  have hlength : t.val - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
      rate rewards C_star C_h u t z =
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t z).length := by
    rw [ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells_length]
    change t.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h =
      t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start rate rewards C_star C_h u t z
    rw [ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart]
  have hcells : ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t t.val z =
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t z).map some := by
    rw [htake, hcurrent, ← List.map_take, hlength]
    change ((_ ++ [_]).take _).map some = _
    rw [List.take_left]
  unfold ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixReadout
  rw [hcells]
  have hm : ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
      ((ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t z).map some) =
      some (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t z) := by
    induction ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t z with
    | nil => rfl
    | cons cell cells ih =>
        change (some cell :: cells.map some).mapM id = some (cell :: cells)
        rw [List.mapM_cons]
        simp [ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells] at ih
        simp [ih]
  rw [hm]
  rfl

/-- Every present full numerical prefix and every actual future view obey
this same-anchor envelope on the original renewal law and literal future gate. -/
theorem ae_Gfuture_numerical_weight_envelope
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    ∀ᵐ z : Z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t,
      z ∈ G_q q hfuture →
      ∀ (r : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))
        (data : ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate),
        O_q q.val z = some r →
        ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
          rate rewards C_star C_h u t z q hfuture = some data →
        ∀ j : Fin p.K,
          data.2.1.payload.anchor j ≤ (1 + 1 / (D p : ℝ)) ^ (r.1 j).1 ∧
            (1 + 1 / (D p : ℝ)) ^ (r.1 j).1 ≤ 2 * data.2.1.payload.anchor j := by
  filter_upwards [ae_Gfuture_incoming_weight_eq_future_anchor
    rate rewards C_star C_h u t control0 q hfuture] with z hanchor
  intro hgate r data hread hdata j
  have henvelope := futurePrefix_incoming_weight_envelope
    rate rewards C_star C_h u t q hfuture z r data hread hdata j
  rw [hanchor hgate data hdata j] at henvelope
  exact henvelope

/-- Actual source-law witnesses for the numerical anchor envelope and its
canonical rate sum. The optional incoming prefix is preserved, and the
marginal/rate estimate is derived here from the numerical score envelope. -/
theorem ae_Gfuture_actual_numerical_weight_envelope
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    ∀ᵐ z : Z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t,
      z ∈ G_q q hfuture →
      ∃ (r : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))
        (data : ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate)
        (xi : Fin p.K → ℝ) (cell : RecordedQueueRun.RoundInput p.K),
        O_q q.val z = some r ∧
        O_q t.val z = some (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
          rate rewards C_star C_h u t z) ∧ r.2.1 = false ∧
        ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
          rate rewards C_star C_h u t z q hfuture = some data ∧
        ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
          rate rewards C_star C_h u t z q hfuture = some (true, xi) ∧
        data.1 = some (true, xi) ∧
        ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
          rate rewards C_star C_h u t z q hfuture = some cell ∧
        cell.enabled = true ∧ cell.rate = xi ∧
        (∀ j : Fin p.K, xi j = CanonicalRecordingRates.xi p rate.eta.val
          data.2.1.payload.anchor j) ∧
        (∀ j : Fin p.K,
          data.2.1.payload.anchor j ≤ (1 + 1 / (D p : ℝ)) ^ (r.1 j).1 ∧
            (1 + 1 / (D p : ℝ)) ^ (r.1 j).1 ≤ 2 * data.2.1.payload.anchor j) ∧
        (∑ j : Fin p.K, ProductSetLaw.theta p.m
          (fun i => (1 + 1 / (D p : ℝ)) ^ (r.1 i).1) j / xi j) ≤
            CanonicalRecordingRates.R p := by
  filter_upwards [ae_Gfuture_numerical_weight_envelope
    rate rewards C_star C_h u t control0 q hfuture] with z henvelope
  intro hgate
  obtain ⟨r, data, xi, cell, hread, hflag, hdata, hparameters, hdataParameters,
    hcell, henabled, hrate, hcanonical⟩ :=
      Gfuture_actual_readouts rate rewards C_star C_h u t q hfuture z hgate
  have hweights := henvelope hgate r data hread hdata
  refine ⟨r, data, xi, cell, hread,
    calendarCells_incoming_readout rate rewards C_star C_h u t z, hflag, hdata,
    hparameters, hdataParameters, hcell, henabled, hrate, hcanonical, hweights, ?_⟩
  have hxi : xi = CanonicalRecordingRates.xi p rate.eta.val data.2.1.payload.anchor :=
    funext hcanonical
  rw [hxi]
  exact CanonicalRecordingRates.sum_theta_div_xi_le_R p rate.eta.property
    data.2.1.payload.anchor (fun i => (1 + 1 / (D p : ℝ)) ^ (r.1 i).1)
    data.2.1.payload.anchor_pos hweights

/-- The actual per-arm history after removing the complete pre-birth history.
This is a literal list projection of the full numerical readout, not a new
execution or a chosen replay word. -/
def acceptedRenewalWord (z : Z)
    (r : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))
    (j : Fin p.K) : List (Bool × ℕ) :=
  (r.2.2 j).drop ((ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
    rate rewards C_star C_h u t z).records j).length

/-- The literal accepted-history projection replays from the incoming
registers and lies within the actual installed episode horizon. -/
theorem acceptedRenewalWord_replay (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (z : Z)
    (r : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))
    (data : ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate)
    (hread : O_q q.val z = some r)
    (hdata : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture = some data) (j : Fin p.K) :
    (acceptedRenewalWord rate rewards C_star C_h u t z r j).length ≤
        ReplayWeightStability.episodeHorizon rate.eta.val ∧
    r.2.2 j = (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t z).records j ++
        acceptedRenewalWord rate rewards C_star C_h u t z r j ∧
    r.1 j = QueueReplay.replay (4 * rate.n)
      ((ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t z).registers j)
      (acceptedRenewalWord rate rewards C_star C_h u t z r j) := by
  obtain ⟨suffix, _, _, _, hwords⟩ := futurePrefix_actual_replay
    rate rewards C_star C_h u t q hfuture z r hread
  obtain ⟨word, _, hlen, hrecords, hreplay⟩ := hwords j
  have heq : acceptedRenewalWord rate rewards C_star C_h u t z r j = word := by
    unfold acceptedRenewalWord
    rw [hrecords, List.drop_left]
  rw [heq]
  exact ⟨hlen.trans (futureView_episode_length_bound
    rate rewards C_star C_h u t q hfuture z data hdata), hrecords, hreplay⟩

/-- The accepted word starts with the genuine birth cell once. Earlier
overflow is preserved by its literal `acceptedRecord`, and the remaining
word has one entry per executed post-birth calendar cell. -/
theorem acceptedRenewalWord_birth (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (z : Z)
    (r : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))
    (hread : O_q q.val z = some r) (j : Fin p.K) :
    ∃ tailWord : List (Bool × ℕ),
      acceptedRenewalWord rate rewards C_star C_h u t z r j =
        RecordedQueueRun.acceptedRecord (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
            rate rewards C_star C_h u t z)
          (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
            rate rewards C_star C_h u t z) j :: tailWord ∧
      tailWord.length ≤ q.val - (t.val + 1) := by
  obtain ⟨suffix, _, hlen, hstate, _⟩ := futurePrefix_actual_replay
    rate rewards C_star C_h u t q hfuture z r hread
  obtain ⟨word, hword, hrecords⟩ := execute_records_suffix
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) suffix
    (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t z)
      (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
        rate rewards C_star C_h u t z)) j
  refine ⟨word, ?_, hword.le.trans hlen⟩
  unfold acceptedRenewalWord
  rw [hstate]
  change ((RecordedQueueRun.execute _ suffix (RecordedQueueRun.step _ _ _)).records j).drop _ = _
  rw [hrecords]
  change (((ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
    rate rewards C_star C_h u t z).records j ++ [_]) ++ word).drop _ = _
  rw [List.append_assoc, List.drop_left]
  rfl

/-- Literal real floor arithmetic at the actual future cell, using the
whole reward table, the installed canonical rate and `n = eta * D`. -/
theorem futureCell_quantizedArrival_eq_floor (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) (z : Z)
    (data : ReferenceFirstCollectionRenewalFutureFirstReplacementView.ViewData rate)
    (cell : RecordedQueueRun.RoundInput p.K)
    (hdata : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture = some data)
    (hcell : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some cell) (j : Fin p.K) :
    RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        cell j =
      if cell.recordedArm = some j then
        Nat.floor ((D p : ℝ) * rate.eta.val *
          (((rewards q j).val : ℝ) / (D p : ℝ)) /
          CanonicalRecordingRates.xi p rate.eta.val data.2.1.payload.anchor j)
      else 0 := by
  rcases data with ⟨parameters, view, code⟩
  have hactual := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
    rate rewards C_star C_h u t z q hfuture
  rw [hdata] at hactual
  obtain ⟨c, snapshot, valid, hc, _, hrate, hreward, _⟩ := hactual
  have hsame : c = cell := Option.some.inj (hc.symm.trans hcell)
  subst c
  rw [RecordedQueueRun.quantizedArrival, hrate, hreward]
  change (if cell.recordedArm = some j then
    Nat.floor ((rate.n : ℝ) * (((rewards q j).val : ℝ) / (D p : ℝ)) /
      CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor j) else 0) = _
  rw [rate.n_scale, mul_comm rate.eta.val (D p : ℝ)]

end Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalWeightEnvelope

end
