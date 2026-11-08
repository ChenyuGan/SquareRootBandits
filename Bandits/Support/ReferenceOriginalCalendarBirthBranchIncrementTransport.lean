/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition
public import Bandits.Support.ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# The actual renewed-birth carried-energy increment

This module joins the literal selected branch to the original-source later
birth calculation at the same calendar date and under the same source law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceOriginalCalendarBirthBranchIncrementTransport

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p

local instance sourceInputMeasurableSpace : MeasurableSpace X := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- The literal active renewed-birth selector event at the original date. -/
public def renewedBirthActiveUpdateSet (q : Fin p.T) : Set X :=
  {z | (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
      rate rewards C_star C_h q z).isSome = true ∧
    ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z}

/-- The selected branch, cell, source row, and inherited queue observation
are all witnesses from the same original record and date. -/
public theorem renewedBirthActiveUpdate_selectedWitnesses
    (q : Fin p.T) (a : Fin p.K) (z : X)
    (hz : z ∈ renewedBirthActiveUpdateSet rate rewards C_star C_h q) :
    ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (c : RecordedQueueRun.RoundInput p.K)
      (payload : ReferenceActivePhysicalStep.Payload rate)
      (o : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K),
      ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
        rate rewards C_star C_h q z = some ⟨r, (c, payload)⟩ ∧
      ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
        rate rewards C_star C_h q z = some c ∧
      r.input.rows = z.1.2 ∧ r.input.selected =
        ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = q ∧ r.input.rewards = rewards ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h q.val z = some o ∧ o.2.1 = false ∧
      ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
        rate rewards C_star C_h q.val a z =
        Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
          ((o.1 a).2 : ℝ) /
            ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) ∧
      ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt
        rate rewards C_star C_h q a z =
        RecordedRoundMoments.normalizedQuantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a - 4 := by
  change (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
      rate rewards C_star C_h q z).isSome = true ∧ _ at hz
  obtain ⟨hselector, hactive⟩ := hz
  obtain ⟨data, hdata⟩ := Option.isSome_iff_exists.mp hselector
  rcases data with ⟨r, cp⟩
  rcases cp with ⟨c, payload⟩
  have hcell := ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector_actualCell
    rate rewards C_star C_h q z r c payload hdata
  have hcanonical := ReferenceOriginalCalendarRetainedBranchPartition.chosenSelector_canonical
    rate rewards C_star C_h q z r c payload (Or.inr (Or.inr hdata))
  rcases hcanonical with ⟨hrows, hselected, htime, hrewards, _⟩
  obtain ⟨o, hprefix, hclear, henergy, hincrement, _⟩ :=
    ReferenceOriginalCalendarRetainedBranchPartition.chosenSelector_retainedContribution
      rate rewards C_star C_h q a z r c payload hactive (Or.inr (Or.inr hdata))
  exact ⟨r, c, payload, o, hdata, hcell, hrows, hselected, htime, hrewards,
    hprefix, hclear, henergy, hincrement⟩

/-- The selected update's literal present clear prefix is exactly the
original-source prior-clear event. -/
public theorem activeUpdate_in_originalPriorClear
    (q : Fin p.T) (z : X)
    (hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z) :
    z ∈ ReferenceFirstCollectionCurrentRetainedGate.H
      rate rewards C_star C_h q := by
  obtain ⟨o, _c, hprefix, _hcell, hclear, _⟩ := hactive
  have hreadout :
      ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
        rate rewards C_star C_h q z = some o := by
    have hEq :
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
            rate rewards C_star C_h q.val z =
          ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
            rate rewards C_star C_h q z := by
      unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
      rw [ReferenceFirstCollectionCorrectedFutureRetainedMoment.prefixInputs_eq_pastCells
        rate rewards C_star C_h q z]
    exact hEq ▸ hprefix
  exact ⟨o, hreadout, hclear⟩

private theorem physicalStart_lt_date_of_actualRecord_not_first
    (q : Fin p.T) (z : X)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h q z = some r)
    (hnotfirst : r.input.state.coordinator ≠ .first) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < q.val := by
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h q.val z := by
    by_contra hn
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h q z hn] at hr
    cases hr
  have hlookup :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[q.val -
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]? = some r := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
    split_ifs at hr with hs
    · exact hr
  by_contra hnot
  have hdate : q.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
    have hle := hlaunch.2
    omega
  have hhead :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[0]? =
        some r := by
    simpa only [hdate, Nat.sub_self] using hlookup
  obtain ⟨active, hcorrected, hactiveFirst, _, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate z rewards C_star C_h hlaunch.1
  have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate z rewards C_star C_h active hcorrected
  cases hrecords :
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h with
  | nil => simp [hrecords] at hhead
  | cons head tail =>
      simp only [hrecords, List.getElem?_cons_zero, Option.some.injEq] at hhead
      subst head
      rw [hrecords] at hchain
      exact hnotfirst (by rw [hchain.1, hactiveFirst])

/-- A selected renewed birth is an actual present pre-sampler call at the same
source record. -/
public theorem preSamplerSet_of_renewedBirthSelector
    (q : Fin p.T) (z : X)
    (hselector :
      (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
        rate rewards C_star C_h q z).isSome = true) :
    z ∈ ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet
      rate rewards C_star C_h q := by
  obtain ⟨data, hdata⟩ := Option.isSome_iff_exists.mp hselector
  rcases data with ⟨r, cp⟩
  rcases cp with ⟨c, payload⟩
  have hparts :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r ∧
      ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector rate r =
        some (c, payload) := by
    unfold ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector at hdata
    rcases Option.bind_eq_some_iff.mp hdata with ⟨r', hr, hmap⟩
    rcases Option.map_eq_some_iff.mp hmap with ⟨cp, hcp, hdata'⟩
    cases hdata'
    exact ⟨hr, hcp⟩
  rcases hparts with ⟨hr, hrecord⟩
  have hread :=
    ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector_cell
      rate r c payload hrecord
  have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have hdispatch : ReferenceActivePhysicalStep.dispatch r.input =
      r.output.preparation.coordinator := r.output.preparation.coordinator_eq.symm
  have hrecord' := hrecord
  unfold ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector at hrecord'
  rw [hread] at hrecord'
  simp only [Option.bind_some] at hrecord'
  rw [hdispatch] at hrecord'
  have hchosen : ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
    unfold ReferenceCollectionPhaseHistory.laterChosen
    rw [← hprep]
    cases hcoord : r.output.preparation.coordinator with
    | collection old ledger clock cutoff outcome =>
        cases outcome with
        | laterChosen core consistent started hstart instruction hinstruction output hcons
            clockData installed selected =>
            rfl
        | _ =>
            simp only [hcoord] at hrecord'
            cases hrecord'
    | first outcome =>
        simp only [hcoord] at hrecord'
        cases hrecord'
    | live registers owned base outcome =>
        simp only [hcoord] at hrecord'
        cases hrecord'
    | invalidCollectionCutoff =>
        simp only [hcoord] at hrecord'
        cases hrecord'
    | dagger =>
        simp only [hcoord] at hrecord'
        cases hrecord'
  have hparams :=
    ReferenceFirstCollectionRenewalRecordingFeedback.laterChosen_parameters_present
      (rate := rate) r.input hchosen
  change (ReferenceCalendarLaterSamplerPredictability.calendarParameters
    rate rewards C_star C_h q z).isSome = true
  rw [ReferenceCalendarLaterSamplerPredictability.calendarParameters, hr]
  simpa only [ReferenceLaterSamplerParameterMeasurability.parameters?, Option.bind_some]
    using hparams

/-- The zero-origin branch readout and the original physical-origin marker
are the same selected cell on an actual renewed birth. -/
public theorem sourceLaterMarker_of_renewedBirthSelector
    (q : Fin p.T) (z : X)
    (hselector :
      (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
        rate rewards C_star C_h q z).isSome = true) :
    (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker
      rate rewards C_star C_h q z).isSome = true := by
  obtain ⟨data, hdata⟩ := Option.isSome_iff_exists.mp hselector
  rcases data with ⟨r, cp⟩
  rcases cp with ⟨c, payload⟩
  have hparts :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r ∧
      ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector rate r =
        some (c, payload) := by
    unfold ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector at hdata
    rcases Option.bind_eq_some_iff.mp hdata with ⟨r', hr, hmap⟩
    rcases Option.map_eq_some_iff.mp hmap with ⟨cp, hcp, hdata'⟩
    cases hdata'
    exact ⟨hr, hcp⟩
  rcases hparts with ⟨hr, hrecord⟩
  have hread :=
    ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector_cell
      rate r c payload hrecord
  have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have hdispatch : ReferenceActivePhysicalStep.dispatch r.input =
      r.output.preparation.coordinator := r.output.preparation.coordinator_eq.symm
  have hrecord' := hrecord
  unfold ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector at hrecord'
  rw [hread] at hrecord'
  simp only [Option.bind_some] at hrecord'
  rw [hdispatch] at hrecord'
  have htime : r.input.time = q := by
    exact (ReferenceOriginalCalendarRetainedBranchPartition.chosenSelector_canonical
      rate rewards C_star C_h q z r c payload (Or.inr (Or.inr hdata))).2.2.1
  unfold ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker
  rw [hr]
  simp only [Option.bind_some, Option.isSome_map]
  cases hcoord : r.output.preparation.coordinator with
  | collection old ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hinstruction output hcons
          clockData installed selected =>
          have hrecordEq := hrecord'
          simp only [hcoord] at hrecordEq
          have hpayload : payload = installed.registers.payload := by
            have hp := congrArg Prod.snd (Option.some.inj hrecordEq)
            exact hp.symm
          have hd : ReferenceActivePhysicalStep.dispatch r.input =
              .collection old ledger clock cutoff
                (.laterChosen core consistent started hstart instruction hinstruction output hcons
                  clockData installed selected) := hdispatch.trans hcoord
          have hnotfirst : r.input.state.coordinator ≠ .first := by
            intro hfirst
            have hfirstDispatch := ReferenceActivePhysicalStep.dispatch_first r.input hfirst
            rw [hfirstDispatch] at hd
            cases hd
          have hstartLt := physicalStart_lt_date_of_actualRecord_not_first
            rate rewards C_star C_h q z r hr hnotfirst
          have hprovenance :=
            ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance r.input
          rw [hd] at hprovenance
          rcases hprovenance with ⟨_, _, hsigma, _⟩
          have hstartSigma :
              ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
                payload.sigma.val := by
            rw [hpayload, hsigma, congrArg Fin.val htime]
            exact hstartLt
          obtain ⟨actual, ho, hselection, _, hlive, hcell⟩ :=
            ReferenceLaterLiveNumericalReadout.laterLiveReadout_some 0 r c hread
          have hview : actual.view.payload = payload :=
            ReferenceOriginalCalendarRetainedBranchPartition.chosenRecordSelector_payload
              rate r c payload actual hselection (Or.inr (Or.inr hrecord))
          have hphysicalReadout :
              ReferenceLaterLiveNumericalReadout.laterLiveReadout
                (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r =
                some c := by
            unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
            have hdomain :
                ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h <
                    actual.view.payload.sigma.val ∧
                  CoordinatorLocalArmChoice.assignmentIsLive actual.view.payload
                    actual.view.cutoff r.input.time := by
              exact ⟨by rw [hview]; exact hstartSigma, hlive⟩
            simp [hselection, hdomain, ho, ← hcell]
          rw [hphysicalReadout]
          rfl
      | _ =>
          simp only [hcoord] at hrecord'
          cases hrecord'
  | first outcome =>
      simp only [hcoord] at hrecord'
      cases hrecord'
  | live registers owned base outcome =>
      simp only [hcoord] at hrecord'
      cases hrecord'
  | invalidCollectionCutoff =>
      simp only [hcoord] at hrecord'
      cases hrecord'
  | dagger =>
      simp only [hcoord] at hrecord'
      cases hrecord'

/-- One direction of the actual event join: a selected active update is a
pre-sampler call, has the original clear-prefix witness, and has the same
physical-origin source marker. -/
public theorem renewedBirthActiveUpdate_subset_sourceEvent
    (q : Fin p.T) :
    renewedBirthActiveUpdateSet rate rewards C_star C_h q ⊆
      (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet
          rate rewards C_star C_h q ∩
        ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q ∩
        {z | (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker
          rate rewards C_star C_h q z).isSome = true}) := by
  intro z hz
  change (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
      rate rewards C_star C_h q z).isSome = true ∧ _ at hz
  rcases hz with ⟨hselector, hactive⟩
  exact ⟨⟨preSamplerSet_of_renewedBirthSelector rate rewards C_star C_h q z hselector,
      activeUpdate_in_originalPriorClear rate rewards C_star C_h q z hactive⟩,
    sourceLaterMarker_of_renewedBirthSelector rate rewards C_star C_h q z hselector⟩

/-- The original source call, clear strict prefix, and true physical marker
construct the same renewed-birth selector and its active queue update. -/
public theorem sourceEvent_subset_renewedBirthActiveUpdate
    (q : Fin p.T) :
    (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet
        rate rewards C_star C_h q ∩
      ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q ∩
      {z | (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker
        rate rewards C_star C_h q z).isSome = true}) ⊆
      renewedBirthActiveUpdateSet rate rewards C_star C_h q := by
  intro z hz
  rcases hz with ⟨⟨hcall, hclear⟩, hmarker⟩
  have hparameters :
      (ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h q z).isSome = true := by
    simpa [ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet] using hcall
  obtain ⟨theta, hparameters⟩ := Option.isSome_iff_exists.mp hparameters
  obtain ⟨r, hr, hparameter⟩ := Option.bind_eq_some_iff.mp hparameters
  obtain ⟨r', cell, hr', htime, _hrows, _hselected, _hrewards, hstrict,
      hcurrent, _hmark, _hphysicalMarker, _howner, _hquantized, _hfree, _hsaved⟩ :=
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirth_physical
      rate rewards C_star C_h q z hcall hmarker
  have hrEq : r = r' := Option.some.inj (hr.symm.trans hr')
  subst r'
  have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have hselected :
      (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection = some cell.selected := by
    rw [← hprep]
    exact cell.selection_actual
  have hchosen := ReferenceFirstCollectionCurrentRemainderLaw.selected_laterChosen
    rate r.input theta hparameter cell.selected hselected
  have ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r := by
    intro i
    simp [ReferenceLaterLiveNumericalReadout.ordinaryData, cell.ordinary i]
  have hstates : ReferenceLaterLiveNumericalReadout.preparedStates r ho = cell.states := by
    funext i
    simp [ReferenceLaterLiveNumericalReadout.preparedStates,
      ReferenceLaterLiveNumericalReadout.ordinaryData, cell.ordinary i]
  have hcellInput : cell.input =
      ReferenceFirstWindowNumericalStream.sourceCell r cell.selected.view.payload
        cell.selected.view.pendingAtChoice
        (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
        cell.selected.view.complementWeights cell.selected.view.cutoff
        cell.choiceInputsValid := by
    rw [hstates]
    exact cell.input_eq
  have hzero : 0 < cell.selected.view.payload.sigma.val := by omega
  have hreadZero : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some cell.input := by
    unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
    simp only [cell.selection_actual, hzero, cell.assignment_live, and_self,
      ite_true, dite_eq_left ho]
    exact congrArg some hcellInput.symm
  have hcell :
      ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
        rate rewards C_star C_h q z = some cell.input := by
    have hcell0 : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some cell.input := by
      simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hreadZero]
    change (ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h q z).bind
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some cell.input
    rw [hr, Option.bind_some, hcell0]
  obtain ⟨Pfx, c, hPfx, _hPfxNext, hcurrentCell, henabled, hclearRun, _hstep⟩ :=
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirth_prefix_energy_step
      rate rewards C_star C_h q z hcall hmarker
  have hc : c = cell.input := Option.some.inj (hcurrentCell.symm.trans hcurrent)
  subst c
  have hrunClear :
      (RecordedQueueRun.run
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) Pfx).overflow = false :=
    hclearRun.mp hclear
  have hprefix :
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h q.val z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) Pfx)) := by
    unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
    rw [hPfx]
    rfl
  have hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z := by
    refine ⟨_, cell.input, hprefix, hcell, ?_, cell.enabled⟩
    exact hrunClear
  have hdispatch : ReferenceActivePhysicalStep.dispatch r.input =
      (ReferenceActivePhysicalStep.prepare r.input).coordinator := by
    calc
      ReferenceActivePhysicalStep.dispatch r.input = r.output.preparation.coordinator :=
        r.output.preparation.coordinator_eq.symm
      _ = (ReferenceActivePhysicalStep.prepare r.input).coordinator := by rw [hprep]
  have hrecordSelector :
      (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector
        rate r).isSome = true := by
    cases hcoord : (ReferenceActivePhysicalStep.prepare r.input).coordinator with
    | collection old ledger clock cutoff outcome =>
        cases outcome with
        | laterChosen core consistent started hstart instruction hinstruction output hcons
            clockData installed selected =>
            unfold ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthRecordSelector
            rw [hreadZero]
            simp [hdispatch, hcoord]
        | _ =>
            simp [ReferenceCollectionPhaseHistory.laterChosen, hcoord] at hchosen
    | first outcome =>
        simp [ReferenceCollectionPhaseHistory.laterChosen, hcoord] at hchosen
    | live registers owned base outcome =>
        simp [ReferenceCollectionPhaseHistory.laterChosen, hcoord] at hchosen
    | invalidCollectionCutoff =>
        simp [ReferenceCollectionPhaseHistory.laterChosen, hcoord] at hchosen
    | dagger =>
        simp [ReferenceCollectionPhaseHistory.laterChosen, hcoord] at hchosen
  have hselector :
      (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
        rate rewards C_star C_h q z).isSome = true := by
    obtain ⟨cp, hcp⟩ := Option.isSome_iff_exists.mp hrecordSelector
    unfold ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
    rw [hr]
    simp only [Option.bind_some]
    rw [hcp]
    rfl
  exact ⟨hselector, hactive⟩

/-- The same original event admits both the selector and source descriptions. -/
public theorem renewedBirthActiveUpdateSet_eq_sourceEvent (q : Fin p.T) :
    renewedBirthActiveUpdateSet rate rewards C_star C_h q =
      (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet
          rate rewards C_star C_h q ∩
        ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q ∩
        {z | (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker
          rate rewards C_star C_h q z).isSome = true}) := by
  apply Set.Subset.antisymm
  · exact renewedBirthActiveUpdate_subset_sourceEvent rate rewards C_star C_h q
  · exact sourceEvent_subset_renewedBirthActiveUpdate rate rewards C_star C_h q

/-- The actual selected carried increment is integrable under the original
source law, with measurability obtained from the exact source-event join. -/
public theorem renewedBirthActiveUpdate_carriedIncrement_integrable
    (control0 : TimeControl p) (q : Fin p.T) (a : Fin p.K) :
    Integrable
      ((renewedBirthActiveUpdateSet rate rewards C_star C_h q).indicator
        (fun z =>
          ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
              rate rewards C_star C_h (q.val + 1) a z -
            ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
              rate rewards C_star C_h q.val a z))
      (sourceInputLaw p) := by
  let ambient : MeasurableSpace X :=
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceInputMeasurableSpace p
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)
  have hle : F ≤ ambient :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (q.val + 1)
  have hcall : MeasurableSet[F]
      (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet
        rate rewards C_star C_h q) :=
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet_measurable
      rate rewards C_star C_h control0 q
  have hclear : MeasurableSet[F]
      (ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q) :=
    ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
      rate rewards C_star C_h control0 q
  have hmarkerFn : @Measurable X (Option (Option (Fin p.K))) ambient _
      (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker
        rate rewards C_star C_h q) :=
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker_measurable
      rate rewards C_star C_h q
  have hmarker : MeasurableSet[ambient]
      {z | (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker
        rate rewards C_star C_h q z).isSome = true} :=
    measurableSet_eq_fun
      ((measurable_of_countable Option.isSome).comp
        hmarkerFn) measurable_const
  have hsource : MeasurableSet[ambient]
      (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet
          rate rewards C_star C_h q ∩
        ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q ∩
        {z | (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker
          rate rewards C_star C_h q z).isSome = true}) := by
    exact ((hle _ hcall).inter (hle _ hclear)).inter hmarker
  have hset : MeasurableSet[ambient]
      (renewedBirthActiveUpdateSet rate rewards C_star C_h q) := by
    rw [renewedBirthActiveUpdateSet_eq_sourceEvent rate rewards C_star C_h q]
    exact hsource
  have hnext := ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
    rate rewards C_star C_h (q.val + 1) (by omega) a
  have hcurrent := ReferenceOriginalCalendarCarriedStoppedEnergy.integrable_carriedStoppedEnergy
    rate rewards C_star C_h q.val (by omega) a
  exact (hnext.sub hcurrent).indicator hset

/-- On an actual active prefix the source calculation's incoming energy is
the same carried scalar, with the same optional readout. -/
public theorem incomingEnergy_eq_carriedStoppedEnergy_of_active
    (q : Fin p.T) (a : Fin p.K) (z : X)
    (hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z) :
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.incomingEnergy
        rate rewards C_star C_h q a z =
      ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
        rate rewards C_star C_h q.val a z := by
  obtain ⟨o, _c, hprefix, _hcell, _hclear, _henabled⟩ := hactive
  have hgate : ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
      rate rewards C_star C_h q z = some o := by
    have hEq : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h q.val z =
        ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
          rate rewards C_star C_h q z := by
      unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
      rw [← ReferenceFirstCollectionCorrectedFutureRetainedMoment.prefixInputs_eq_pastCells
        rate rewards C_star C_h q z]
    exact hEq ▸ hprefix
  have hcarry := ReferenceOriginalCalendarCarriedStoppedEnergy.carriedPrefixReadout_of_present
    rate rewards C_star C_h q.val z o hprefix
  simp [ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.incomingEnergy,
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.readoutEnergy,
    ReferenceFirstCollectionCurrentQueueReadout.before?, hgate,
    ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog,
    ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy, hcarry]
  ring

/-- The source physical readout and retained selector use the very same
selected cell at the original date. -/
private theorem selectedActualCell_eq_originalCurrentCell
    (q : Fin p.T) (z : X)
    (hselector :
      (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
        rate rewards C_star C_h q z).isSome = true)
    (hcall : z ∈ ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet
      rate rewards C_star C_h q)
    (hmarker :
      (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker
        rate rewards C_star C_h q z).isSome = true) :
    ∃ c, ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
        rate rewards C_star C_h q z = some c ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h q z = some c := by
  obtain ⟨data, hdata⟩ := Option.isSome_iff_exists.mp hselector
  rcases data with ⟨r, cp⟩
  rcases cp with ⟨c, payload⟩
  have hactual := ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector_actualCell
    rate rewards C_star C_h q z r c payload hdata
  obtain ⟨_, _, _, _, selected, ho, hselection, hpayload, hsourceCell,
      _harm, _henabled, _hreward, _hrate, _hquantized⟩ :=
    ReferenceOriginalCalendarRetainedBranchPartition.chosenSelector_canonical
      rate rewards C_star C_h q z r c payload (Or.inr (Or.inr hdata))
  obtain ⟨r', cell, hr', _htime, _hrows, _hselected, _hrewards, _hstrict,
      hcurrent, _hmarker, _hphysicalMarker, _howner, _hquantized, _hfree, _hsaved⟩ :=
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirth_physical
      rate rewards C_star C_h q z hcall hmarker
  have hr := (ReferenceOriginalCalendarRetainedBranchPartition.chosenSelector_record
    rate rewards C_star C_h q z r c payload (Or.inr (Or.inr hdata))).1
  have hrEq : r = r' := Option.some.inj (hr.symm.trans hr')
  subst r'
  have hselectionEq : selected = cell.selected :=
    Option.some.inj (hselection.symm.trans cell.selection_actual)
  have hstates : ReferenceLaterLiveNumericalReadout.preparedStates r ho = cell.states := by
    funext i
    simp [ReferenceLaterLiveNumericalReadout.preparedStates,
      ReferenceLaterLiveNumericalReadout.ordinaryData, cell.ordinary i]
  have hcell : c = cell.input := by
    calc
      c = ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
          selected.view.pendingAtChoice (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
          selected.view.complementWeights selected.view.cutoff
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) := hsourceCell
      _ = ReferenceFirstWindowNumericalStream.sourceCell r cell.selected.view.payload
          cell.selected.view.pendingAtChoice cell.states cell.selected.view.complementWeights
          cell.selected.view.cutoff cell.choiceInputsValid := by
        rw [hselectionEq, hstates]
      _ = cell.input := cell.input_eq.symm
  have hcurrent' : ReferenceFirstCollectionCurrentNumericalCell.currentCell
      rate rewards C_star C_h q z = some c := by
    exact hcurrent.trans (congrArg some hcell.symm)
  exact ⟨c, hactual, hcurrent'⟩

/-- On the actual source event, the retained post-update energy is exactly the
next value of the same carried prefix, including an overflow-causing update. -/
private theorem laterBirthRetainedEnergy_eq_carriedSuccessor
    (q : Fin p.T) (a : Fin p.K) (z : X)
    (hz : z ∈ renewedBirthActiveUpdateSet rate rewards C_star C_h q) :
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.laterBirthRetainedEnergy
        rate rewards C_star C_h q a z =
      ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
        rate rewards C_star C_h (q.val + 1) a z := by
  change (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
      rate rewards C_star C_h q z).isSome = true ∧ _ at hz
  obtain ⟨hselector, hactive⟩ := hz
  have hcall := preSamplerSet_of_renewedBirthSelector
    rate rewards C_star C_h q z hselector
  have hmarker := sourceLaterMarker_of_renewedBirthSelector
    rate rewards C_star C_h q z hselector
  obtain ⟨L, c, hL, hLnext, hcurrent, _henabled, _hclear, _hstep⟩ :=
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirth_prefix_energy_step
      rate rewards C_star C_h q z hcall hmarker
  obtain ⟨c', hcell, hcurrent'⟩ := selectedActualCell_eq_originalCurrentCell
    rate rewards C_star C_h q z hselector hcall hmarker
  have hc : c = c' := Option.some.inj (hcurrent.symm.trans hcurrent')
  subst c'
  have hreadNext :
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h (q.val + 1) z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (L ++ [c]))) := by
    unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
    rw [hLnext]
    rfl
  have hcarriedNext :=
    ReferenceOriginalCalendarCarriedStoppedEnergy.carriedPrefixReadout_of_present
      rate rewards C_star C_h (q.val + 1) z _ hreadNext
  have hafter : ReferenceFirstCollectionCurrentQueueReadout.after?
      rate rewards C_star C_h q z =
      some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) c)) := by
    unfold ReferenceFirstCollectionCurrentQueueReadout.after?
    rw [← ReferenceFirstCollectionCorrectedFutureRetainedMoment.prefixInputs_eq_pastCells
      rate rewards C_star C_h q z, hL, hcurrent]
    rfl
  have hBenergy :
      ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.laterBirthRetainedEnergy
          rate rewards C_star C_h q a z =
        ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.readoutEnergy
          rate a (ReferenceFirstCollectionCurrentQueueReadout.after?
            rate rewards C_star C_h q z) := by
    unfold ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.laterBirthRetainedEnergy
    rw [Set.indicator_of_mem (show z ∈
      ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet
          rate rewards C_star C_h q ∩
        ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q from
      ⟨hcall, activeUpdate_in_originalPriorClear rate rewards C_star C_h q z hactive⟩)]
    simp [hmarker]
  rw [hBenergy, hafter]
  simp [ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.readoutEnergy,
    ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog,
    ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy,
    hcarriedNext, ReferenceFirstCollectionRenewalFutureNumericalPrefix.run_append_one]
  ring

private theorem laterBirthRetainedEnergy_eq_activeIndicator
    (q : Fin p.T) (a : Fin p.K) :
    ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.laterBirthRetainedEnergy
        rate rewards C_star C_h q a =
      (renewedBirthActiveUpdateSet rate rewards C_star C_h q).indicator
        (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.laterBirthRetainedEnergy
          rate rewards C_star C_h q a) := by
  funext z
  by_cases hz : z ∈ renewedBirthActiveUpdateSet rate rewards C_star C_h q
  · rw [Set.indicator_of_mem hz]
  · rw [Set.indicator_of_notMem hz]
    unfold ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.laterBirthRetainedEnergy
    by_cases her : z ∈
        ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet
          rate rewards C_star C_h q ∩
        ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h q
    · by_cases hm : (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker
          rate rewards C_star C_h q z).isSome = true
      · have hs : z ∈ renewedBirthActiveUpdateSet rate rewards C_star C_h q := by
          rw [renewedBirthActiveUpdateSet_eq_sourceEvent]
          exact ⟨her, hm⟩
        exact (hz hs).elim
      · simp [her, hm]
    · simp [her]

public theorem renewedBirthActiveUpdate_increment_eq_retained_sub_incoming
    (q : Fin p.T) (a : Fin p.K) :
    (renewedBirthActiveUpdateSet rate rewards C_star C_h q).indicator
      (fun z =>
        ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
            rate rewards C_star C_h (q.val + 1) a z -
          ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
            rate rewards C_star C_h q.val a z) =
      fun z =>
        ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.laterBirthRetainedEnergy
            rate rewards C_star C_h q a z -
          (renewedBirthActiveUpdateSet rate rewards C_star C_h q).indicator
            (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.incomingEnergy
              rate rewards C_star C_h q a) z := by
  funext z
  by_cases hz : z ∈ renewedBirthActiveUpdateSet rate rewards C_star C_h q
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    have hzSet := hz
    change (ReferenceOriginalCalendarRetainedBranchPartition.renewedBirthSelector
        rate rewards C_star C_h q z).isSome = true ∧ _ at hz
    obtain ⟨hsel, hact⟩ := hz
    rw [laterBirthRetainedEnergy_eq_carriedSuccessor rate rewards C_star C_h q a z hzSet,
      incomingEnergy_eq_carriedStoppedEnergy_of_active rate rewards C_star C_h q a z hact]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    rw [laterBirthRetainedEnergy_eq_activeIndicator rate rewards C_star C_h q a]
    simp [hz]


section BirthExpectation

open ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep
  (preSamplerSet sourceLaterMarker presentIndicator incomingEnergy readoutEnergy
    laterBirthPresenceMass laterBirthPresenceMassAtPrefix laterBirthRetainedEnergy
    laterBirthExponentialCoefficient)
open ReferenceFirstCollectionCurrentRetainedGate (H pastCells? prefixReadout?)
open ReferenceFirstCollectionCurrentQueueReadout (before? normalizedReadoutBacklog)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open ReferenceFirstLaunchNumericalCell (queueParameters)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix sourcePrefixFiltration)
open ContinuousControlSlice (assignmentLaw)
open AssignmentParameterFibreKernel (AssignmentVector)

variable (control0 : TimeControl p) (q : Fin p.T)
local notation "μ" => sourceInputLaw p
local notation "F" => sourcePrefixFiltration control0 (q.val + 1)
local notation "E" => preSamplerSet rate rewards C_star C_h q
local notation "R" => H rate rewards C_star C_h q
local notation "S" => renewedBirthActiveUpdateSet rate rewards C_star C_h q
local notation "alpha" => laterBirthPresenceMass rate rewards C_star C_h control0 q
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "capEnergy" => Real.exp (beta * (1 / (32 * rate.eta.val)))

private theorem incomingEnergy_prefix_measurable (a : Fin p.K) :
    Measurable[F] (incomingEnergy rate rewards C_star C_h q a) :=
  (measurable_of_countable (readoutEnergy rate a)).comp
    (ReferenceFirstCollectionCurrentQueueReadout.before?_measurable
      rate rewards C_star C_h control0 q)

/-- The bound is used only on the actual present, prior-clear prefix. -/
private theorem incomingEnergy_le_of_priorClear (a : Fin p.K) (z : X) (hz : z ∈ R) :
    incomingEnergy rate rewards C_star C_h q a z ≤ capEnergy := by
  obtain ⟨v, hv, hfalse⟩ := hz
  cases hP : pastCells? rate rewards C_star C_h q z with
  | none => simp only [prefixReadout?, hP, Option.map_none, reduceCtorEq] at hv
  | some Pfx =>
      simp only [prefixReadout?, hP, Option.map_some, Option.some.injEq] at hv
      subst v
      have hb := StoppedQueueBound.run_prefix_normalized_backlog_le_threshold_of_overflow_false
        (queueParameters rate) Pfx Pfx.length a
        (by simpa only [List.take_length, stateReadout] using hfalse)
      rw [List.take_length] at hb
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _
        (CanonicalRecordingRates.beta_pos p rate.eta.property).le
      simpa only [incomingEnergy, readoutEnergy, before?, prefixReadout?, hP,
        Option.map_some, normalizedReadoutBacklog, stateReadout,
        StoppedQueueBound.normalizedBacklog, queueParameters] using hb

/-- A bounded predictable weight is multiplied by the actual random success,
then conditioned. Only the pre-sampler and prior-clear events are predictable. -/
private theorem selected_weight_condExp
    (f : X → ℝ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hf : Measurable[F] f) (hb : ∀ z ∈ E ∩ R, ‖f z‖ ≤ bound) :
    Integrable ((S).indicator f) μ ∧
      μ[(S).indicator f | F] =ᵐ[μ]
        (E ∩ R).indicator (fun z => f z * alpha z) := by
  let J := (E ∩ R).indicator f
  let Y := (E).indicator (fun z => presentIndicator
    (sourceLaterMarker rate rewards C_star C_h q z).isSome)
  have hle := (sourcePrefixFiltration control0).le' (q.val + 1)
  have hE := ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.preSamplerSet_measurable
    rate rewards C_star C_h control0 q
  have hR := ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
    rate rewards C_star C_h control0 q
  have hJ : Measurable[F] J := hf.indicator (hE.inter hR)
  have hJbound (z : X) : ‖J z‖ ≤ bound := by
    by_cases hz : z ∈ E ∩ R
    · rw [show J z = f z from Set.indicator_of_mem hz f]
      exact hb z hz
    · simp only [J, Set.indicator_of_notMem hz, norm_zero]
      exact hbound
  have hmarker := ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.sourceLaterMarker_measurable
    rate rewards C_star C_h q
  have hpresent : Measurable (fun z : X => presentIndicator
      (sourceLaterMarker rate rewards C_star C_h q z).isSome) :=
    Measurable.ite (measurableSet_eq_fun
      ((measurable_of_countable Option.isSome).comp hmarker) measurable_const)
      measurable_const measurable_const
  have hY : Measurable Y := hpresent.indicator (hle _ hE)
  have hYbound (z : X) : ‖Y z‖ ≤ 1 := by
    by_cases hz : z ∈ E
    · rw [show Y z = _ from Set.indicator_of_mem hz _]
      unfold presentIndicator
      split_ifs <;> norm_num
    · simp only [Y, Set.indicator_of_notMem hz, norm_zero, zero_le_one]
  have hYi : Integrable Y μ := (integrable_const (1 : ℝ)).mono'
    hY.aestronglyMeasurable (Filter.Eventually.of_forall hYbound)
  have hproduct : Integrable (J * Y) μ := by
    apply (integrable_const bound).mono'
      (((hJ.mono hle le_rfl).mul hY).aestronglyMeasurable)
    filter_upwards [] with z
    calc
      ‖(J * Y) z‖ = ‖J z‖ * ‖Y z‖ := norm_mul _ _
      _ ≤ ‖J z‖ * 1 := mul_le_mul_of_nonneg_left (hYbound z) (norm_nonneg _)
      _ ≤ bound := by rw [mul_one]; exact hJbound z
  have hselected : (S).indicator f = J * Y := by
    funext z
    rw [renewedBirthActiveUpdateSet_eq_sourceEvent]
    by_cases her : z ∈ E ∩ R
    · by_cases hm : (sourceLaterMarker rate rewards C_star C_h q z).isSome = true
      · simp [J, Y, her, her.1, hm, presentIndicator]
      · simp [J, Y, her, her.1, hm, presentIndicator]
    · by_cases he : z ∈ E
      · have hr : z ∉ R := fun hr => her ⟨he, hr⟩
        simp [J, Y, he, hr]
      · simp [J, Y, he]
  constructor
  · rw [hselected]
    exact hproduct
  rw [hselected]
  have hpull := condExp_mul_of_stronglyMeasurable_left hJ.stronglyMeasurable
    hproduct hYi
  have hsuccess := ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirthPresence_condExp
    rate rewards C_star C_h control0 q
  filter_upwards [hpull, hsuccess] with z hp hs
  rw [hp]
  change J z * μ[Y | F] z = _
  rw [hs]
  by_cases her : z ∈ E ∩ R
  · simp only [J, Set.indicator_of_mem her, Set.indicator_of_mem her.1]
  · simp only [J, Set.indicator_of_notMem her, zero_mul]

/-- Integrability and the exact conditional successful inherited energy.
The current whole-vector success is retained inside conditional expectation. -/
public theorem renewedBirthActiveUpdate_incoming_condExp (a : Fin p.K) :
    Integrable ((S).indicator (incomingEnergy rate rewards C_star C_h q a)) μ ∧
      μ[(S).indicator (incomingEnergy rate rewards C_star C_h q a) | F] =ᵐ[μ]
        (E ∩ R).indicator (fun z =>
          incomingEnergy rate rewards C_star C_h q a z * alpha z) := by
  apply selected_weight_condExp rate rewards C_star C_h control0 q
    _ capEnergy (Real.exp_nonneg _)
    (incomingEnergy_prefix_measurable rate rewards C_star C_h control0 q a)
  intro z hz
  rw [Real.norm_of_nonneg (show 0 ≤ incomingEnergy rate rewards C_star C_h q a z from
    Real.exp_nonneg _)]
  exact incomingEnergy_le_of_priorClear rate rewards C_star C_h q a z hz.2

/-- Exact conditional mass of the actual active renewed-birth event. -/
public theorem renewedBirthActiveUpdate_mass_condExp :
    Integrable ((S).indicator (fun _ => (1 : ℝ))) μ ∧
      μ[(S).indicator (fun _ => (1 : ℝ)) | F] =ᵐ[μ] (E ∩ R).indicator alpha := by
  simpa only [one_mul] using
    selected_weight_condExp rate rewards C_star C_h control0 q
      (fun _ => (1 : ℝ)) 1 zero_le_one measurable_const (fun _ _ => by norm_num)

/-- The actual selected carried increment has conditional upper bound equal
to the conditional mass of that SAME successful birth. -/
public theorem renewedBirthActiveUpdate_increment_condExp_le_mass (a : Fin p.K) :
    ∀ᵐ z ∂μ,
      μ[(S).indicator (fun z =>
        ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
            rate rewards C_star C_h (q.val + 1) a z -
          ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
            rate rewards C_star C_h q.val a z) | F] z ≤
      μ[(S).indicator (fun _ => (1 : ℝ)) | F] z := by
  have hret := ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.originalLaterBirth_retained_energy
    rate rewards C_star C_h control0 q a
  have hin := renewedBirthActiveUpdate_incoming_condExp rate rewards C_star C_h control0 q a
  have hmass := renewedBirthActiveUpdate_mass_condExp rate rewards C_star C_h control0 q
  have hsub := condExp_sub hret.1 hin.1 F
  change μ[(fun z => laterBirthRetainedEnergy rate rewards C_star C_h q a z -
    (S).indicator (incomingEnergy rate rewards C_star C_h q a) z) | F] =ᵐ[μ] _ at hsub
  rw [← renewedBirthActiveUpdate_increment_eq_retained_sub_incoming
    rate rewards C_star C_h q a] at hsub
  filter_upwards [hsub, hret.2.1, hin.2, hmass.2] with z hs hr hi hm
  rw [hs, Pi.sub_apply, hi, hm]
  by_cases hz : z ∈ E ∩ R
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    have hstrong := hr.1
    rw [Set.indicator_of_mem hz] at hstrong
    obtain ⟨theta, hp⟩ := Option.isSome_iff_exists.mp hz.1
    have hpp :=
      (ReferenceCalendarLaterSamplerPredictability.calendarParameters_factor
        rate rewards C_star C_h control0 q z).symm.trans hp
    have hmgf :=
      (ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep.laterBirthExponential_vector_integral
        rate rewards C_star C_h control0 q (sourcePrefix control0 q.val z) a theta hpp).2
    change _ ≤ alpha z at hmgf
    have hnonneg : 0 ≤ incomingEnergy rate rewards C_star C_h q a z := Real.exp_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hmgf hnonneg
    linarith only [hstrong, hmul]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    have hstrong := hr.1
    rw [Set.indicator_of_notMem hz] at hstrong
    simpa only [sub_zero] using hstrong

include control0 in
/-- Original-source integral bound for the SAME selected carried increment,
with the actual successful-birth mass retained before the final bound by one. -/
public theorem renewedBirthActiveUpdate_carriedIncrement_integral_le_mass
    (a : Fin p.K) :
    (∫ z, (S).indicator (fun z =>
        ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
            rate rewards C_star C_h (q.val + 1) a z -
          ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
            rate rewards C_star C_h q.val a z) z ∂μ) ≤
      (∫ z, (S).indicator (fun _ => (1 : ℝ)) z ∂μ) ∧
      (∫ z, (S).indicator (fun _ => (1 : ℝ)) z ∂μ) ≤ 1 := by
  have hle := (sourcePrefixFiltration control0).le' (q.val + 1)
  have hmass := renewedBirthActiveUpdate_mass_condExp rate rewards C_star C_h control0 q
  constructor
  · conv_lhs => rw [← integral_condExp hle]
    conv_rhs => rw [← integral_condExp hle]
    exact integral_mono_ae integrable_condExp integrable_condExp
      (renewedBirthActiveUpdate_increment_condExp_le_mass
        rate rewards C_star C_h control0 q a)
  · calc
      _ ≤ ∫ _ : X, (1 : ℝ) ∂μ := integral_mono hmass.1 (integrable_const _) (fun z => by
        by_cases hz : z ∈ S <;> simp [hz])
      _ = 1 := by simp

end BirthExpectation


end Bandits.Support.ReferenceOriginalCalendarBirthBranchIncrementTransport

end
