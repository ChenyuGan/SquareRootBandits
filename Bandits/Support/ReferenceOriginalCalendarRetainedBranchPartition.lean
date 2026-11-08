/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarCarriedStoppedEnergy
public import Bandits.Support.ReferenceOriginalCalendarCollectionRetainedEnergyStep
public import Bandits.Support.ReferenceOriginalCalendarLaterBirthRemainderRecorder

import Mathlib.Tactic

/-!
# Actual branch partition for an original-calendar retained update

The branch selectors below inspect the actual record's dispatcher constructor
and the corresponding existing optional numerical readout. They retain that
record, the selected cell, and its selected payload.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput)

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "Input" => RecordedQueueRun.RoundInput p.K
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord
  (p := p) (rate := rate)
local notation "Payload" => ReferenceActivePhysicalStep.Payload rate
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- The concrete original record, cell, and selected assignment payload kept
by each actual branch selector. -/
public abbrev ActualBranchData := Σ _r : Record, Input × Payload

/-- Record-local selector for the actual first chosen readout. -/
public def firstChosenRecordSelector (r : Record) : Option (Input × Payload) :=
  (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).bind fun c =>
    match ReferenceActivePhysicalStep.dispatch r.input with
    | .first (.chosen installed _) => some (c, installed.registers.payload)
    | _ => none

/-- Record-local selector for a continuing LIVE choice. -/
public def continuingLiveRecordSelector (r : Record) : Option (Input × Payload) :=
  (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).bind fun c =>
    match ReferenceActivePhysicalStep.dispatch r.input with
    | .live registers _ _ (.continuingChosen _ _ _ _) => some (c, registers.payload)
    | _ => none

/-- Record-local selector for a renewed assignment birth. -/
public def renewedBirthRecordSelector (r : Record) : Option (Input × Payload) :=
  (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).bind fun c =>
    match ReferenceActivePhysicalStep.dispatch r.input with
    | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        some (c, installed.registers.payload)
    | _ => none

/-- Record-local selector for an incoming LIVE cutoff or continuing
collection dispatch, using the collection producer's actual readout. -/
public def collectionOrCutoffRecordSelector (r : Record) :
    Option (Input × Payload) :=
  (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).bind fun c =>
    match ReferenceActivePhysicalStep.dispatch r.input with
    | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
        some (c, registers.payload)
    | .collection payload _ _ _ (.continuing _ _ _ _) => some (c, payload)
    | _ => none

/-- A first-calendar chosen cell from the actual live numerical readout. -/
public def firstChosenSelector (q : Fin p.T) (z : X) :
    Option (ActualBranchData rate) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).bind
    fun r => (firstChosenRecordSelector rate r).map fun cp => ⟨r, cp⟩

/-- A continuing LIVE chosen cell from the same record's live readout. -/
public def continuingLiveSelector (q : Fin p.T) (z : X) :
    Option (ActualBranchData rate) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).bind
    fun r => (continuingLiveRecordSelector rate r).map fun cp => ⟨r, cp⟩

/-- A renewed assignment birth from the actual collection dispatch. -/
public def renewedBirthSelector (q : Fin p.T) (z : X) :
    Option (ActualBranchData rate) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).bind
    fun r => (renewedBirthRecordSelector rate r).map fun cp => ⟨r, cp⟩

/-- The collection readout of either an incoming LIVE cutoff or a continuing
collection round. The cutoff and continuing dispatch outcomes stay distinct
inside this selector's literal constructor test. -/
public def collectionOrCutoffSelector (q : Fin p.T) (z : X) :
    Option (ActualBranchData rate) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).bind
    fun r => (collectionOrCutoffRecordSelector rate r).map fun cp => ⟨r, cp⟩

/-- The exact local nonlinear contribution attached to one selected actual
cell, extended by zero unless the retained update is active. -/
public def branchContribution (q : Fin p.T) (a : Fin p.K) (z : X)
    (branch : Option (ActualBranchData rate)) : ℝ :=
  match branch with
  | none => 0
  | some data =>
      if ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
          rate rewards C_star C_h q z then
        ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
            rate rewards C_star C_h q.val a z *
          (Real.exp (beta * (RecordedRoundMoments.normalizedQuantizedArrival Q
            data.2.1 a - 4)) - 1)
      else 0

/-- One unit of branch allowance, retained only on the active actual update. -/
public def branchPenalty (q : Fin p.T) (z : X)
    (branch : Option (ActualBranchData rate)) : ℝ :=
  match branch with
  | none => 0
  | some _ =>
      if ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
          rate rewards C_star C_h q z then 1 else 0

/-- The existing collection domain test selects exactly the incoming cutoff
and continuing-collection constructors retained by the collection selector. -/
public theorem collectionRecordSelector_of_readout
    (r : Record) (c : Input)
    (hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c) :
    ∃ payload : Payload,
      collectionOrCutoffRecordSelector rate r = some (c, payload) := by
  have hdomain := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain
    0 r).mp (by rw [hread]; rfl)
  have hdispatch : ReferenceActivePhysicalStep.dispatch r.input =
      r.output.preparation.coordinator := r.output.preparation.coordinator_eq.symm
  cases hcoord : r.output.preparation.coordinator with
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcand hvalid hclock hpending hnone selected =>
          have hsigma : 0 < registers.payload.sigma.val := by
            simpa only [hcoord] using hdomain.2
          refine ⟨registers.payload, ?_⟩
          simp [collectionOrCutoffRecordSelector, hdispatch, hcoord, hread]
      | _ => simp [hcoord] at hdomain
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          refine ⟨payload, ?_⟩
          simp [collectionOrCutoffRecordSelector, hdispatch, hcoord, hread]
      | _ => simp [hcoord] at hdomain
  | first outcome => simp [hcoord] at hdomain
  | invalidCollectionCutoff => simp [hcoord] at hdomain
  | dagger => simp [hcoord] at hdomain

/-- The four record-level selectors test disjoint constructors of one actual
dispatcher value. This excludes overlapping tags even when their readout
functions are both in scope. -/
public theorem recordSelectors_disjoint (r : Record) :
    ¬ ((firstChosenRecordSelector rate r).isSome = true ∧
        (continuingLiveRecordSelector rate r).isSome = true) ∧
    ¬ ((firstChosenRecordSelector rate r).isSome = true ∧
        (renewedBirthRecordSelector rate r).isSome = true) ∧
    ¬ ((firstChosenRecordSelector rate r).isSome = true ∧
        (collectionOrCutoffRecordSelector rate r).isSome = true) ∧
    ¬ ((continuingLiveRecordSelector rate r).isSome = true ∧
        (renewedBirthRecordSelector rate r).isSome = true) ∧
    ¬ ((continuingLiveRecordSelector rate r).isSome = true ∧
        (collectionOrCutoffRecordSelector rate r).isSome = true) ∧
    ¬ ((renewedBirthRecordSelector rate r).isSome = true ∧
        (collectionOrCutoffRecordSelector rate r).isSome = true) := by
  cases hdispatch : ReferenceActivePhysicalStep.dispatch r.input with
  | first outcome => cases outcome <;> simp [firstChosenRecordSelector,
      continuingLiveRecordSelector, renewedBirthRecordSelector,
      collectionOrCutoffRecordSelector, hdispatch]
  | live registers owned base outcome => cases outcome <;> simp [firstChosenRecordSelector,
      continuingLiveRecordSelector, renewedBirthRecordSelector,
      collectionOrCutoffRecordSelector, hdispatch]
  | collection payload ledger clock cutoff outcome => cases outcome <;> simp [firstChosenRecordSelector,
      continuingLiveRecordSelector, renewedBirthRecordSelector,
      collectionOrCutoffRecordSelector, hdispatch]
  | invalidCollectionCutoff => simp [firstChosenRecordSelector,
      continuingLiveRecordSelector, renewedBirthRecordSelector,
      collectionOrCutoffRecordSelector, hdispatch]
  | dagger => simp [firstChosenRecordSelector, continuingLiveRecordSelector,
      renewedBirthRecordSelector, collectionOrCutoffRecordSelector, hdispatch]

/-- A present live readout is selected from one of the three actual chosen
dispatch constructors: first launch, continuing LIVE, or renewed birth. -/
public theorem liveRecordSelector_coverage
    (r : Record) (c : Input)
    (hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c) :
    (firstChosenRecordSelector rate r).isSome = true ∨
      (continuingLiveRecordSelector rate r).isSome = true ∨
      (renewedBirthRecordSelector rate r).isSome = true := by
  have hdomain := (ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain
    0 r).mp (by rw [hread]; rfl)
  change ReferenceLaterLiveNumericalReadout.laterLiveDomain 0 r at hdomain
  unfold ReferenceLaterLiveNumericalReadout.laterLiveDomain at hdomain
  have hdispatch : ReferenceActivePhysicalStep.dispatch r.input =
      r.output.preparation.coordinator := r.output.preparation.coordinator_eq.symm
  cases hcoord : r.output.preparation.coordinator with
  | first outcome =>
      have hcut : ReferenceActivePhysicalStep.dispatch r.input =
          .first outcome := hdispatch.trans hcoord
      cases outcome with
      | chosen installed selected =>
          exact Or.inl (by simp [firstChosenRecordSelector, hcut, hread])
      | _ => simp_all [ReferenceActivePhysicalStep.DispatchCut.selection]
  | live registers owned base outcome =>
      have hcut : ReferenceActivePhysicalStep.dispatch r.input =
          .live registers owned base outcome := hdispatch.trans hcoord
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcand hvalid hclock hpending hnone selected =>
          rcases hdomain with ⟨selected', hselected, _, hlive, _⟩
          have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r
          rw [hcoord] at hframes
          have hnotLive : ¬ CoordinatorLocalArmChoice.assignmentIsLive
              registers.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
              r.input.time := by simpa using hframes.1
          have hselectedEq := hselected
          simp [hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt] at hselectedEq
          cases hselectedEq
          exact False.elim (hnotLive hlive)
      | continuingChosen dispatched hstart continuation selected =>
          exact Or.inr (Or.inl (by
            simp [continuingLiveRecordSelector, hcut, hread]))
      | _ => simp_all [ReferenceActivePhysicalStep.DispatchCut.selection]
  | collection payload ledger clock cutoff outcome =>
      have hcut : ReferenceActivePhysicalStep.dispatch r.input =
          .collection payload ledger clock cutoff outcome := hdispatch.trans hcoord
      cases outcome with
      | continuing core prepared boundary scores =>
          rcases hdomain with ⟨selected', hselected, _, hlive, _⟩
          have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r
          rw [hcoord] at hframes
          have hnotLive : ¬ CoordinatorLocalArmChoice.assignmentIsLive payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                prepared.clockStarted.clock.u) r.input.time := by simpa using hframes.1
          have hselectedEq := hselected
          simp [hcoord, ReferenceActivePhysicalStep.DispatchCut.selection] at hselectedEq
          cases hselectedEq
          exact False.elim (hnotLive hlive)
      | laterChosen _ _ _ _ _ _ _ _ _ installed selected =>
          exact Or.inr (Or.inr (by
            simp [renewedBirthRecordSelector, hcut, hread]))
      | _ => simp_all [ReferenceActivePhysicalStep.DispatchCut.selection]
  | invalidCollectionCutoff =>
      rw [hcoord] at hdomain
      simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hdomain
  | dagger =>
      rw [hcoord] at hdomain
      simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hdomain

public theorem firstRecordSelector_cell
    (r : Record) (c : Input) (payload : Payload)
    (hselector : firstChosenRecordSelector rate r = some (c, payload)) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
  rcases Option.bind_eq_some_iff.mp hselector with ⟨readCell, hread, hmatch⟩
  cases hdispatch : ReferenceActivePhysicalStep.dispatch r.input with
  | first outcome =>
      cases outcome with
      | chosen installed selected =>
          simp [hdispatch] at hmatch
          have hcell : readCell = c := congrArg Prod.fst hmatch
          rw [hcell] at hread
          exact hread
      | _ => simp [hdispatch] at hmatch
  | live registers owned base outcome => simp [hdispatch] at hmatch
  | collection selectedPayload ledger clock cutoff outcome => simp [hdispatch] at hmatch
  | invalidCollectionCutoff => simp [hdispatch] at hmatch
  | dagger => simp [hdispatch] at hmatch

public theorem continuingLiveRecordSelector_cell
    (r : Record) (c : Input) (payload : Payload)
    (hselector : continuingLiveRecordSelector rate r = some (c, payload)) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
  rcases Option.bind_eq_some_iff.mp hselector with ⟨readCell, hread, hmatch⟩
  cases hdispatch : ReferenceActivePhysicalStep.dispatch r.input with
  | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation selected =>
          simp [hdispatch] at hmatch
          have hcell : readCell = c := hmatch.1
          rw [hcell] at hread
          exact hread
      | _ => simp [hdispatch] at hmatch
  | first outcome => simp [hdispatch] at hmatch
  | collection selectedPayload ledger clock cutoff outcome => simp [hdispatch] at hmatch
  | invalidCollectionCutoff => simp [hdispatch] at hmatch
  | dagger => simp [hdispatch] at hmatch

public theorem renewedBirthRecordSelector_cell
    (r : Record) (c : Input) (payload : Payload)
    (hselector : renewedBirthRecordSelector rate r = some (c, payload)) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
  rcases Option.bind_eq_some_iff.mp hselector with ⟨readCell, hread, hmatch⟩
  cases hdispatch : ReferenceActivePhysicalStep.dispatch r.input with
  | collection selectedPayload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hinstruction output hcons
          clockData installed selected =>
          simp [hdispatch] at hmatch
          have hcell : readCell = c := congrArg Prod.fst hmatch
          rw [hcell] at hread
          exact hread
      | _ => simp [hdispatch] at hmatch
  | first outcome => simp [hdispatch] at hmatch
  | live registers owned base outcome => simp [hdispatch] at hmatch
  | invalidCollectionCutoff => simp [hdispatch] at hmatch
  | dagger => simp [hdispatch] at hmatch

/-- The FIRST selector forces the incoming constructor, before any selected
payload is installed. It is not a later assignment birth. -/
public theorem firstRecordSelector_incoming
    (r : Record) (c : Input) (payload : Payload)
    (hselector : firstChosenRecordSelector rate r = some (c, payload)) :
    r.input.state.coordinator = .first := by
  rcases Option.bind_eq_some_iff.mp hselector with ⟨readCell, _, hmatch⟩
  cases hstate : r.input.state.coordinator with
  | first => rfl
  | live registers owned base =>
      simp only [ReferenceActivePhysicalStep.dispatch, hstate,
        CoordinatorRoundDispatch.dispatch] at hmatch
      cases hd : CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput r.input registers owned base) <;>
        (simp only [hd] at hmatch; cases hmatch)
  | collection old ledger proposal =>
      simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hmatch
      split_ifs at hmatch with hcut
      · simp only [CoordinatorRoundDispatch.dispatch] at hmatch
        cases hd : CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput r.input old ledger
            (ReferenceActivePhysicalStep.collectionClock old ledger proposal
              ⟨ledger.cutoff - 1, by omega⟩) ⟨ledger.cutoff - 1, by omega⟩) <;>
          (simp only [hd] at hmatch; cases hmatch)
  | dagger => simp [ReferenceActivePhysicalStep.dispatch, hstate] at hmatch

/-- In each of the three chosen constructors the payload retained by the
selector is exactly the payload of the actual checked selection. -/
public theorem chosenRecordSelector_payload
    (r : Record) (c : Input) (payload : Payload)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected)
    (hbranch : firstChosenRecordSelector rate r = some (c, payload) ∨
      continuingLiveRecordSelector rate r = some (c, payload) ∨
      renewedBirthRecordSelector rate r = some (c, payload)) :
    selected.view.payload = payload := by
  have hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
    rcases hbranch with h | h | h
    · exact firstRecordSelector_cell rate r c payload h
    · exact continuingLiveRecordSelector_cell rate r c payload h
    · exact renewedBirthRecordSelector_cell rate r c payload h
  have hselection : (ReferenceActivePhysicalStep.dispatch r.input).selection =
      some selected := by
    rw [← r.output.preparation.coordinator_eq]
    exact hs
  simp only [firstChosenRecordSelector, continuingLiveRecordSelector,
    renewedBirthRecordSelector, hread, Option.bind_some] at hbranch
  cases hd : ReferenceActivePhysicalStep.dispatch r.input with
  | first outcome =>
      cases outcome with
      | chosen installed chosen =>
          simp only [hd, Option.some.injEq, reduceCtorEq, or_false] at hbranch
          simp only [hd, ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt] at hselection
          split_ifs at hselection
          cases hselection
          exact congrArg Prod.snd hbranch
      | _ => simp [hd] at hbranch
  | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation chosen =>
          simp only [hd, Option.some.injEq, Prod.mk.injEq, reduceCtorEq,
            false_or, or_false] at hbranch
          simp only [hd, ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt, dite_true] at hselection
          cases hselection
          exact hbranch.2
      | _ => simp [hd] at hbranch
  | collection old ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hinstruction output hcons
          clockData installed chosen =>
          simp only [hd, Option.some.injEq, reduceCtorEq, false_or] at hbranch
          simp only [hd, ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt] at hselection
          split_ifs at hselection
          cases hselection
          exact congrArg Prod.snd hbranch
      | _ => simp [hd] at hbranch
  | invalidCollectionCutoff => simp [hd] at hbranch
  | dagger => simp [hd] at hbranch

/-- Canonical cell and marker from the SAME selected view and actual prepared
ordinary states. The selector hypothesis is a literal dispatch test, not a
recorder law. In particular a present bottom marker remains a present cell. -/
public theorem chosenRecordSelector_canonical
    (r : Record) (c : Input) (payload : Payload)
    (hbranch : firstChosenRecordSelector rate r = some (c, payload) ∨
      continuingLiveRecordSelector rate r = some (c, payload) ∨
      renewedBirthRecordSelector rate r = some (c, payload)) :
    ∃ (selected : ReferenceActivePhysicalStep.Selection r.input)
      (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r),
      r.output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = payload ∧
      0 < selected.view.payload.sigma.val ∧
      CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
        selected.view.cutoff r.input.time ∧
      c = ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
        selected.view.pendingAtChoice
        (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
        selected.view.complementWeights selected.view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) ∧
      c.recordedArm = ReferenceFirstWindowNumericalStream.sourceArm r selected.view.payload
        selected.view.pendingAtChoice
        (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
        selected.view.complementWeights selected.view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) := by
  have hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
    rcases hbranch with h | h | h
    · exact firstRecordSelector_cell rate r c payload h
    · exact continuingLiveRecordSelector_cell rate r c payload h
    · exact renewedBirthRecordSelector_cell rate r c payload h
  obtain ⟨selected, ho, hs, hbase, hlive, hc⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some 0 r c hread
  refine ⟨selected, ho, hs,
    chosenRecordSelector_payload rate r c payload selected hs hbranch,
    hbase, hlive, hc, ?_⟩
  rw [hc]
  rfl

public theorem firstSelector_actualCell
    (q : Fin p.T) (z : X) (r : Record) (c : Input) (payload : Payload)
    (hselector : firstChosenSelector rate rewards C_star C_h q z =
      some ⟨r, (c, payload)⟩) :
    ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
      rate rewards C_star C_h q z = some c := by
  have hparts :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r ∧
      firstChosenRecordSelector rate r = some (c, payload) := by
    unfold firstChosenSelector at hselector
    rcases Option.bind_eq_some_iff.mp hselector with ⟨r', hr', hmap⟩
    rcases Option.map_eq_some_iff.mp hmap with ⟨cp, hcp, hdata⟩
    cases hdata
    exact ⟨hr', hcp⟩
  obtain ⟨hr, hrecordSelector⟩ := hparts
  have hlive := firstRecordSelector_cell rate r c payload hrecordSelector
  have hcell0 : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
    simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hlive]
  change (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).bind
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some c
  rw [hr, Option.bind_some, hcell0]

public theorem continuingLiveSelector_actualCell
    (q : Fin p.T) (z : X) (r : Record) (c : Input) (payload : Payload)
    (hselector : continuingLiveSelector rate rewards C_star C_h q z =
      some ⟨r, (c, payload)⟩) :
    ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
      rate rewards C_star C_h q z = some c := by
  have hparts :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r ∧
      continuingLiveRecordSelector rate r = some (c, payload) := by
    unfold continuingLiveSelector at hselector
    rcases Option.bind_eq_some_iff.mp hselector with ⟨r', hr', hmap⟩
    rcases Option.map_eq_some_iff.mp hmap with ⟨cp, hcp, hdata⟩
    cases hdata
    exact ⟨hr', hcp⟩
  obtain ⟨hr, hrecordSelector⟩ := hparts
  have hlive := continuingLiveRecordSelector_cell rate r c payload hrecordSelector
  have hcell0 : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
    simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hlive]
  change (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).bind
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some c
  rw [hr, Option.bind_some, hcell0]

public theorem renewedBirthSelector_actualCell
    (q : Fin p.T) (z : X) (r : Record) (c : Input) (payload : Payload)
    (hselector : renewedBirthSelector rate rewards C_star C_h q z =
      some ⟨r, (c, payload)⟩) :
    ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
      rate rewards C_star C_h q z = some c := by
  have hparts :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r ∧
      renewedBirthRecordSelector rate r = some (c, payload) := by
    unfold renewedBirthSelector at hselector
    rcases Option.bind_eq_some_iff.mp hselector with ⟨r', hr', hmap⟩
    rcases Option.map_eq_some_iff.mp hmap with ⟨cp, hcp, hdata⟩
    cases hdata
    exact ⟨hr', hcp⟩
  obtain ⟨hr, hrecordSelector⟩ := hparts
  have hlive := renewedBirthRecordSelector_cell rate r c payload hrecordSelector
  have hcell0 : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
    simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hlive]
  change (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).bind
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some c
  rw [hr, Option.bind_some, hcell0]

/-- Every active update is covered by one of the four actual readout/dispatch
selectors. The case split is made only after `activeUpdateAt` supplies its
actual record and current cell; no optional-prefix totality is assumed. -/
public theorem activeUpdate_branchCoverage (q : Fin p.T) (z : X)
    (hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z) :
    (firstChosenSelector rate rewards C_star C_h q z).isSome = true ∨
      (continuingLiveSelector rate rewards C_star C_h q z).isSome = true ∨
      (renewedBirthSelector rate rewards C_star C_h q z).isSome = true ∨
      (collectionOrCutoffSelector rate rewards C_star C_h q z).isSome = true := by
  obtain ⟨o, c, hprefix, hcell, hclear, henabled⟩ := hactive
  obtain ⟨r, hr, hcell0⟩ := Option.bind_eq_some_iff.mp hcell
  change ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c at hcell0
  change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).or
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r) = some c at hcell0
  cases hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
  | some liveCell =>
      have hcoverage := liveRecordSelector_coverage rate r liveCell hlive
      rcases hcoverage with hfirst | hlive | hbirth
      · left
        simpa [firstChosenSelector, hr] using hfirst
      · right; left
        simpa [continuingLiveSelector, hr] using hlive
      · right; right; left
        simpa [renewedBirthSelector, hr] using hbirth
  | none =>
      have hcollection : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
          0 r = some c := by simpa [hlive] using hcell0
      obtain ⟨payload, hselector⟩ := collectionRecordSelector_of_readout rate r c hcollection
      right; right; right
      simp [collectionOrCutoffSelector, hr, hselector]

/-- The four source-facing branch indicators are pairwise disjoint because
they retain the actual dispatch constructors. -/
public theorem branchSelectors_disjoint (q : Fin p.T) (z : X) :
    ¬ ((firstChosenSelector rate rewards C_star C_h q z).isSome = true ∧
        (continuingLiveSelector rate rewards C_star C_h q z).isSome = true) ∧
    ¬ ((firstChosenSelector rate rewards C_star C_h q z).isSome = true ∧
        (renewedBirthSelector rate rewards C_star C_h q z).isSome = true) ∧
    ¬ ((firstChosenSelector rate rewards C_star C_h q z).isSome = true ∧
        (collectionOrCutoffSelector rate rewards C_star C_h q z).isSome = true) ∧
    ¬ ((continuingLiveSelector rate rewards C_star C_h q z).isSome = true ∧
        (renewedBirthSelector rate rewards C_star C_h q z).isSome = true) ∧
    ¬ ((continuingLiveSelector rate rewards C_star C_h q z).isSome = true ∧
        (collectionOrCutoffSelector rate rewards C_star C_h q z).isSome = true) ∧
    ¬ ((renewedBirthSelector rate rewards C_star C_h q z).isSome = true ∧
        (collectionOrCutoffSelector rate rewards C_star C_h q z).isSome = true) := by
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h q z with
  | none => simp [firstChosenSelector, continuingLiveSelector,
      renewedBirthSelector, collectionOrCutoffSelector, hr]
  | some r =>
      simpa [firstChosenSelector, continuingLiveSelector,
        renewedBirthSelector, collectionOrCutoffSelector, hr] using
        recordSelectors_disjoint rate r

/-- A selected collection cell is the exact cell of the original optional
collection recorder. The two readout domains remain separate. -/
public theorem collectionSelector_eq_collectionRecorder
    (q : Fin p.T) (z : X) (r : Record) (c : Input) (payload : Payload)
    (hselector : collectionOrCutoffSelector rate rewards C_star C_h q z =
      some ⟨r, (c, payload)⟩) :
    ReferenceOriginalCalendarCollectionRetainedEnergyStep.C
        rate rewards C_star C_h q z = some c ∧
      ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
        rate rewards C_star C_h q z = some c := by
  have hparts :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r ∧
      collectionOrCutoffRecordSelector rate r = some (c, payload) := by
    unfold collectionOrCutoffSelector at hselector
    rcases Option.bind_eq_some_iff.mp hselector with ⟨r', hr', hmap⟩
    rcases Option.map_eq_some_iff.mp hmap with ⟨cp, hcp, hdata⟩
    cases hdata
    exact ⟨hr', hcp⟩
  obtain ⟨hr, hrecordSelector⟩ := hparts
  have hcollectionReadout :
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c := by
    unfold collectionOrCutoffRecordSelector at hrecordSelector
    cases hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r with
    | none => simp [hread] at hrecordSelector
    | some readCell =>
        have hreadCell : readCell = c := by
          have heq := hrecordSelector
          cases hdispatch : ReferenceActivePhysicalStep.dispatch r.input with
          | first outcome => cases outcome <;> simp [hdispatch, hread] at heq
          | live registers owned base outcome =>
              cases outcome with
              | cutoffChosen dispatched hstart ledger hinit hcand hvalid hclock hpending hnone selected =>
                  simp [hdispatch, hread] at heq
                  exact heq.1
              | _ => simp [hdispatch, hread] at heq
          | collection payload ledger clock cutoff outcome =>
              cases outcome with
              | continuing core prepared boundary scores =>
                  simp [hdispatch, hread] at heq
                  exact heq.1
              | _ => simp [hdispatch, hread] at heq
          | invalidCollectionCutoff => simp [hdispatch, hread] at heq
          | dagger => simp [hdispatch, hread] at heq
        simp [hreadCell]
  have hliveNone : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none := by
    cases hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
    | none => rfl
    | some liveCell =>
        exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint
          rate 0 r ⟨by rw [hread]; rfl, by rw [hcollectionReadout]; rfl⟩)
  have hcell0 : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
    simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hliveNone, hcollectionReadout]
  constructor
  · change (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).bind
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0) = some c
    rw [hr, Option.bind_some, hcollectionReadout]
  · change (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).bind
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some c
    rw [hr, Option.bind_some, hcell0]

private theorem option_eq_none_of_not_isSome {α : Type*} (o : Option α)
    (h : ¬ o.isSome = true) : o = none := by
  cases o with
  | none => rfl
  | some value => exact False.elim (h rfl)

private theorem branchContribution_eq_zero_of_not_active
    (q : Fin p.T) (a : Fin p.K) (z : X)
    (branch : Option (ActualBranchData rate))
    (hactive : ¬ ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z) :
    branchContribution rate rewards C_star C_h q a z branch = 0 := by
  cases branch with
  | none => rfl
  | some data => simp [branchContribution, hactive]

private theorem branchPenalty_eq_zero_of_not_active
    (q : Fin p.T) (z : X)
    (branch : Option (ActualBranchData rate))
    (hactive : ¬ ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z) :
    branchPenalty rate rewards C_star C_h q z branch = 0 := by
  cases branch with
  | none => rfl
  | some data => simp [branchPenalty, hactive]

private theorem branchContribution_eq_actualIncrement
    (q : Fin p.T) (a : Fin p.K) (z : X)
    (branch : Option (ActualBranchData rate))
    (r : Record) (c : Input) (payload : Payload)
    (hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z)
    (hcell : ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
      rate rewards C_star C_h q z = some c)
    (hselector : branch = some ⟨r, (c, payload)⟩) :
    branchContribution rate rewards C_star C_h q a z branch =
      ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
        rate rewards C_star C_h q.val a z *
        (Real.exp (beta * ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt
          rate rewards C_star C_h q a z) - 1) := by
  have hx := ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt_eq
    rate rewards C_star C_h q a z c hactive hcell
  rw [hselector]
  simp [branchContribution, hactive, hx]

/-- Exact pointwise decomposition of the inherited nonlinear increment into
the four disjoint actual dispatch/readout branches. Off the active update the
increment and all four local contributions are zero. -/
public theorem normalizedIncrement_branchDecomposition
    (q : Fin p.T) (a : Fin p.K) (z : X) :
    ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
        rate rewards C_star C_h q.val a z *
        (Real.exp (beta * ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt
          rate rewards C_star C_h q a z) - 1) =
      branchContribution rate rewards C_star C_h q a z
          (firstChosenSelector rate rewards C_star C_h q z) +
        branchContribution rate rewards C_star C_h q a z
          (continuingLiveSelector rate rewards C_star C_h q z) +
        branchContribution rate rewards C_star C_h q a z
          (renewedBirthSelector rate rewards C_star C_h q z) +
        branchContribution rate rewards C_star C_h q a z
          (collectionOrCutoffSelector rate rewards C_star C_h q z) := by
  have hdisjoint := branchSelectors_disjoint rate rewards C_star C_h q z
  rcases hdisjoint with
    ⟨hfirstLive, hfirstBirth, hfirstCollection, hliveBirth, hliveCollection,
      hbirthCollection⟩
  by_cases hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z
  · rcases activeUpdate_branchCoverage rate rewards C_star C_h q z hactive with
      hfirst | hlive | hbirth | hcollection
    · obtain ⟨data, hselector⟩ := Option.isSome_iff_exists.mp hfirst
      rcases data with ⟨r, cp⟩
      rcases cp with ⟨c, payload⟩
      have hcell := firstSelector_actualCell rate rewards C_star C_h q z r c payload hselector
      have hterm := branchContribution_eq_actualIncrement rate rewards C_star C_h q a z
        (firstChosenSelector rate rewards C_star C_h q z) r c payload hactive hcell hselector
      have hnoneLive := option_eq_none_of_not_isSome
        (continuingLiveSelector rate rewards C_star C_h q z)
        (fun h => hfirstLive ⟨hfirst, h⟩)
      have hnoneBirth := option_eq_none_of_not_isSome
        (renewedBirthSelector rate rewards C_star C_h q z)
        (fun h => hfirstBirth ⟨hfirst, h⟩)
      have hnoneCollection := option_eq_none_of_not_isSome
        (collectionOrCutoffSelector rate rewards C_star C_h q z)
        (fun h => hfirstCollection ⟨hfirst, h⟩)
      calc
        _ = branchContribution rate rewards C_star C_h q a z
              (firstChosenSelector rate rewards C_star C_h q z) := hterm.symm
        _ = branchContribution rate rewards C_star C_h q a z
                (firstChosenSelector rate rewards C_star C_h q z) +
              branchContribution rate rewards C_star C_h q a z
                (continuingLiveSelector rate rewards C_star C_h q z) +
              branchContribution rate rewards C_star C_h q a z
                (renewedBirthSelector rate rewards C_star C_h q z) +
              branchContribution rate rewards C_star C_h q a z
                (collectionOrCutoffSelector rate rewards C_star C_h q z) := by
                  simp [branchContribution, hactive, hselector, hnoneLive, hnoneBirth,
                    hnoneCollection]
    · obtain ⟨data, hselector⟩ := Option.isSome_iff_exists.mp hlive
      rcases data with ⟨r, cp⟩
      rcases cp with ⟨c, payload⟩
      have hcell := continuingLiveSelector_actualCell rate rewards C_star C_h q z r c payload hselector
      have hterm := branchContribution_eq_actualIncrement rate rewards C_star C_h q a z
        (continuingLiveSelector rate rewards C_star C_h q z) r c payload hactive hcell hselector
      have hnoneFirst := option_eq_none_of_not_isSome
        (firstChosenSelector rate rewards C_star C_h q z)
        (fun h => hfirstLive ⟨h, hlive⟩)
      have hnoneBirth := option_eq_none_of_not_isSome
        (renewedBirthSelector rate rewards C_star C_h q z)
        (fun h => hliveBirth ⟨hlive, h⟩)
      have hnoneCollection := option_eq_none_of_not_isSome
        (collectionOrCutoffSelector rate rewards C_star C_h q z)
        (fun h => hliveCollection ⟨hlive, h⟩)
      calc
        _ = branchContribution rate rewards C_star C_h q a z
              (continuingLiveSelector rate rewards C_star C_h q z) := hterm.symm
        _ = branchContribution rate rewards C_star C_h q a z
                (firstChosenSelector rate rewards C_star C_h q z) +
              branchContribution rate rewards C_star C_h q a z
                (continuingLiveSelector rate rewards C_star C_h q z) +
              branchContribution rate rewards C_star C_h q a z
                (renewedBirthSelector rate rewards C_star C_h q z) +
              branchContribution rate rewards C_star C_h q a z
                (collectionOrCutoffSelector rate rewards C_star C_h q z) := by
                  simp [branchContribution, hactive, hselector, hnoneFirst, hnoneBirth,
                    hnoneCollection, add_comm]
    · obtain ⟨data, hselector⟩ := Option.isSome_iff_exists.mp hbirth
      rcases data with ⟨r, cp⟩
      rcases cp with ⟨c, payload⟩
      have hcell := renewedBirthSelector_actualCell rate rewards C_star C_h q z r c payload hselector
      have hterm := branchContribution_eq_actualIncrement rate rewards C_star C_h q a z
        (renewedBirthSelector rate rewards C_star C_h q z) r c payload hactive hcell hselector
      have hnoneFirst := option_eq_none_of_not_isSome
        (firstChosenSelector rate rewards C_star C_h q z)
        (fun h => hfirstBirth ⟨h, hbirth⟩)
      have hnoneLive := option_eq_none_of_not_isSome
        (continuingLiveSelector rate rewards C_star C_h q z)
        (fun h => hliveBirth ⟨h, hbirth⟩)
      have hnoneCollection := option_eq_none_of_not_isSome
        (collectionOrCutoffSelector rate rewards C_star C_h q z)
        (fun h => hbirthCollection ⟨hbirth, h⟩)
      calc
        _ = branchContribution rate rewards C_star C_h q a z
              (renewedBirthSelector rate rewards C_star C_h q z) := hterm.symm
        _ = branchContribution rate rewards C_star C_h q a z
                (firstChosenSelector rate rewards C_star C_h q z) +
              branchContribution rate rewards C_star C_h q a z
                (continuingLiveSelector rate rewards C_star C_h q z) +
              branchContribution rate rewards C_star C_h q a z
                (renewedBirthSelector rate rewards C_star C_h q z) +
              branchContribution rate rewards C_star C_h q a z
                (collectionOrCutoffSelector rate rewards C_star C_h q z) := by
                  simp [branchContribution, hactive, hselector, hnoneFirst, hnoneLive,
                    hnoneCollection, add_comm]
    · obtain ⟨data, hselector⟩ := Option.isSome_iff_exists.mp hcollection
      rcases data with ⟨r, cp⟩
      rcases cp with ⟨c, payload⟩
      have hcell := (collectionSelector_eq_collectionRecorder
        rate rewards C_star C_h q z r c payload hselector).2
      have hterm := branchContribution_eq_actualIncrement rate rewards C_star C_h q a z
        (collectionOrCutoffSelector rate rewards C_star C_h q z) r c payload hactive hcell hselector
      have hnoneFirst := option_eq_none_of_not_isSome
        (firstChosenSelector rate rewards C_star C_h q z)
        (fun h => hfirstCollection ⟨h, hcollection⟩)
      have hnoneLive := option_eq_none_of_not_isSome
        (continuingLiveSelector rate rewards C_star C_h q z)
        (fun h => hliveCollection ⟨h, hcollection⟩)
      have hnoneBirth := option_eq_none_of_not_isSome
        (renewedBirthSelector rate rewards C_star C_h q z)
        (fun h => hbirthCollection ⟨h, hcollection⟩)
      calc
        _ = branchContribution rate rewards C_star C_h q a z
              (collectionOrCutoffSelector rate rewards C_star C_h q z) := hterm.symm
        _ = branchContribution rate rewards C_star C_h q a z
                (firstChosenSelector rate rewards C_star C_h q z) +
              branchContribution rate rewards C_star C_h q a z
                (continuingLiveSelector rate rewards C_star C_h q z) +
              branchContribution rate rewards C_star C_h q a z
                (renewedBirthSelector rate rewards C_star C_h q z) +
              branchContribution rate rewards C_star C_h q a z
                (collectionOrCutoffSelector rate rewards C_star C_h q z) := by
                  simp [branchContribution, hactive, hselector, hnoneFirst, hnoneLive,
                    hnoneBirth]
  · have hx0 : ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt
        rate rewards C_star C_h q a z = 0 := by
      simp [ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt, hactive]
    calc
      _ = 0 := by simp [hx0]
      _ = branchContribution rate rewards C_star C_h q a z
              (firstChosenSelector rate rewards C_star C_h q z) +
            branchContribution rate rewards C_star C_h q a z
              (continuingLiveSelector rate rewards C_star C_h q z) +
            branchContribution rate rewards C_star C_h q a z
              (renewedBirthSelector rate rewards C_star C_h q z) +
            branchContribution rate rewards C_star C_h q a z
              (collectionOrCutoffSelector rate rewards C_star C_h q z) := by
        rw [branchContribution_eq_zero_of_not_active rate rewards C_star C_h q a z
          (firstChosenSelector rate rewards C_star C_h q z) hactive]
        rw [branchContribution_eq_zero_of_not_active rate rewards C_star C_h q a z
          (continuingLiveSelector rate rewards C_star C_h q z) hactive]
        rw [branchContribution_eq_zero_of_not_active rate rewards C_star C_h q a z
          (renewedBirthSelector rate rewards C_star C_h q z) hactive]
        rw [branchContribution_eq_zero_of_not_active rate rewards C_star C_h q a z
          (collectionOrCutoffSelector rate rewards C_star C_h q z) hactive]
        simp

/-- The four mutually exclusive actual branches contribute exactly one unit
of branch allowance on an active update and zero otherwise. -/
public theorem branchPenalty_sum_eq_activeIndicator (q : Fin p.T) (z : X) :
    branchPenalty rate rewards C_star C_h q z
        (firstChosenSelector rate rewards C_star C_h q z) +
      branchPenalty rate rewards C_star C_h q z
        (continuingLiveSelector rate rewards C_star C_h q z) +
      branchPenalty rate rewards C_star C_h q z
        (renewedBirthSelector rate rewards C_star C_h q z) +
      branchPenalty rate rewards C_star C_h q z
        (collectionOrCutoffSelector rate rewards C_star C_h q z) =
      if ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
          rate rewards C_star C_h q z then 1 else 0 := by
  by_cases hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z
  · rcases activeUpdate_branchCoverage rate rewards C_star C_h q z hactive with
      hfirst | hlive | hbirth | hcollection
    · obtain ⟨data, hselector⟩ := Option.isSome_iff_exists.mp hfirst
      have hnoneLive := option_eq_none_of_not_isSome
        (continuingLiveSelector rate rewards C_star C_h q z)
        (fun h => (branchSelectors_disjoint rate rewards C_star C_h q z).1 ⟨hfirst, h⟩)
      have hnoneBirth := option_eq_none_of_not_isSome
        (renewedBirthSelector rate rewards C_star C_h q z)
        (fun h => (branchSelectors_disjoint rate rewards C_star C_h q z).2.1
          ⟨hfirst, h⟩)
      have hnoneCollection := option_eq_none_of_not_isSome
        (collectionOrCutoffSelector rate rewards C_star C_h q z)
        (fun h => (branchSelectors_disjoint rate rewards C_star C_h q z).2.2.1
          ⟨hfirst, h⟩)
      simp [branchPenalty, hactive, hselector, hnoneLive, hnoneBirth, hnoneCollection]
    · obtain ⟨data, hselector⟩ := Option.isSome_iff_exists.mp hlive
      have hnoneFirst := option_eq_none_of_not_isSome
        (firstChosenSelector rate rewards C_star C_h q z)
        (fun h => (branchSelectors_disjoint rate rewards C_star C_h q z).1 ⟨h, hlive⟩)
      have hnoneBirth := option_eq_none_of_not_isSome
        (renewedBirthSelector rate rewards C_star C_h q z)
        (fun h => (branchSelectors_disjoint rate rewards C_star C_h q z).2.2.2.1
          ⟨hlive, h⟩)
      have hnoneCollection := option_eq_none_of_not_isSome
        (collectionOrCutoffSelector rate rewards C_star C_h q z)
        (fun h => (branchSelectors_disjoint rate rewards C_star C_h q z).2.2.2.2.1
          ⟨hlive, h⟩)
      simp [branchPenalty, hactive, hselector, hnoneFirst, hnoneBirth, hnoneCollection]
    · obtain ⟨data, hselector⟩ := Option.isSome_iff_exists.mp hbirth
      have hnoneFirst := option_eq_none_of_not_isSome
        (firstChosenSelector rate rewards C_star C_h q z)
        (fun h => (branchSelectors_disjoint rate rewards C_star C_h q z).2.1
          ⟨h, hbirth⟩)
      have hnoneLive := option_eq_none_of_not_isSome
        (continuingLiveSelector rate rewards C_star C_h q z)
        (fun h => (branchSelectors_disjoint rate rewards C_star C_h q z).2.2.2.1
          ⟨h, hbirth⟩)
      have hnoneCollection := option_eq_none_of_not_isSome
        (collectionOrCutoffSelector rate rewards C_star C_h q z)
        (fun h => (branchSelectors_disjoint rate rewards C_star C_h q z).2.2.2.2.2
          ⟨hbirth, h⟩)
      simp [branchPenalty, hactive, hselector, hnoneFirst, hnoneLive, hnoneCollection]
    · obtain ⟨data, hselector⟩ := Option.isSome_iff_exists.mp hcollection
      have hnoneFirst := option_eq_none_of_not_isSome
        (firstChosenSelector rate rewards C_star C_h q z)
        (fun h => (branchSelectors_disjoint rate rewards C_star C_h q z).2.2.1
          ⟨h, hcollection⟩)
      have hnoneLive := option_eq_none_of_not_isSome
        (continuingLiveSelector rate rewards C_star C_h q z)
        (fun h => (branchSelectors_disjoint rate rewards C_star C_h q z).2.2.2.2.1
          ⟨h, hcollection⟩)
      have hnoneBirth := option_eq_none_of_not_isSome
        (renewedBirthSelector rate rewards C_star C_h q z)
        (fun h => (branchSelectors_disjoint rate rewards C_star C_h q z).2.2.2.2.2
          ⟨h, hcollection⟩)
      simp [branchPenalty, hactive, hselector, hnoneFirst, hnoneLive, hnoneBirth]
  · rw [branchPenalty_eq_zero_of_not_active rate rewards C_star C_h q z
      (firstChosenSelector rate rewards C_star C_h q z) hactive]
    rw [branchPenalty_eq_zero_of_not_active rate rewards C_star C_h q z
      (continuingLiveSelector rate rewards C_star C_h q z) hactive]
    rw [branchPenalty_eq_zero_of_not_active rate rewards C_star C_h q z
      (renewedBirthSelector rate rewards C_star C_h q z) hactive]
    rw [branchPenalty_eq_zero_of_not_active rate rewards C_star C_h q z
      (collectionOrCutoffSelector rate rewards C_star C_h q z) hactive]
    simp [hactive]

/-- The pointwise total of the four mutually exclusive branch penalties is at
most one. -/
public theorem branchPenalty_sum_le_one (q : Fin p.T) (z : X) :
    branchPenalty rate rewards C_star C_h q z
        (firstChosenSelector rate rewards C_star C_h q z) +
      branchPenalty rate rewards C_star C_h q z
        (continuingLiveSelector rate rewards C_star C_h q z) +
      branchPenalty rate rewards C_star C_h q z
        (renewedBirthSelector rate rewards C_star C_h q z) +
      branchPenalty rate rewards C_star C_h q z
        (collectionOrCutoffSelector rate rewards C_star C_h q z) ≤ 1 := by
  rw [branchPenalty_sum_eq_activeIndicator rate rewards C_star C_h q z]
  split_ifs <;> norm_num

/-- The inherited-energy update is bounded by the sum of the four local
branch penalties and the four matched nonlinear branch contributions. -/
public theorem carriedStoppedEnergy_update_by_branches (q : Fin p.T) (a : Fin p.K)
    (z : X) :
    ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
        rate rewards C_star C_h (q.val + 1) a z -
      ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
        rate rewards C_star C_h q.val a z ≤
      branchPenalty rate rewards C_star C_h q z
          (firstChosenSelector rate rewards C_star C_h q z) +
        branchPenalty rate rewards C_star C_h q z
          (continuingLiveSelector rate rewards C_star C_h q z) +
        branchPenalty rate rewards C_star C_h q z
          (renewedBirthSelector rate rewards C_star C_h q z) +
        branchPenalty rate rewards C_star C_h q z
          (collectionOrCutoffSelector rate rewards C_star C_h q z) +
      branchContribution rate rewards C_star C_h q a z
          (firstChosenSelector rate rewards C_star C_h q z) +
        branchContribution rate rewards C_star C_h q a z
          (continuingLiveSelector rate rewards C_star C_h q z) +
        branchContribution rate rewards C_star C_h q a z
          (renewedBirthSelector rate rewards C_star C_h q z) +
        branchContribution rate rewards C_star C_h q a z
          (collectionOrCutoffSelector rate rewards C_star C_h q z) := by
  have hupdate := ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy_update_bound
    rate rewards C_star C_h q a z
  rw [← branchPenalty_sum_eq_activeIndicator rate rewards C_star C_h q z,
    normalizedIncrement_branchDecomposition rate rewards C_star C_h q a z] at hupdate
  simpa [add_assoc] using hupdate

/-- On the actual collection-or-cutoff branch, the inherited readout, its
energy, and its normalized arrival agree with the accepted retained-step
objects at this same original date. -/
public theorem collectionBranch_matches_retainedStep (q : Fin p.T) (a : Fin p.K)
    (z : X) (r : Record) (c : Input) (payload : Payload)
    (hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z)
    (hselector : collectionOrCutoffSelector rate rewards C_star C_h q z =
      some ⟨r, (c, payload)⟩) :
    z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.G
        rate rewards C_star C_h q ∧
      ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
        rate rewards C_star C_h q.val a z =
        ReferenceOriginalCalendarCollectionRetainedEnergyStep.W
          rate rewards C_star C_h q a z ∧
      ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt
        rate rewards C_star C_h q a z =
        ReferenceOriginalCalendarCollectionRetainedEnergyStep.x
          rate rewards C_star C_h q a z := by
  have hactive' := hactive
  obtain ⟨o, c₀, hP, hactual, hclear, henabled⟩ := hactive
  obtain ⟨hOC, hactualC⟩ := collectionSelector_eq_collectionRecorder
    rate rewards C_star C_h q z r c payload hselector
  have hc : c₀ = c := Option.some.inj (hactual.symm.trans hactualC)
  subst c₀
  have hPO : ReferenceOriginalCalendarCollectionRetainedEnergyStep.P
      rate rewards C_star C_h q.val z = some o := hP
  have hD : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
      rate rewards C_star C_h q := by
    change (ReferenceOriginalCalendarCollectionRetainedEnergyStep.C
      rate rewards C_star C_h q z).isSome = true
    rw [hOC]
    rfl
  have hV : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.V
      rate rewards C_star C_h q := by
    change (ReferenceOriginalCalendarCollectionRetainedEnergyStep.P
      rate rewards C_star C_h q.val z).isSome = true
    rw [hPO]
    rfl
  have hB : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.B
      rate rewards C_star C_h q := by
    change z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
        rate rewards C_star C_h q ∧
      z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.V
        rate rewards C_star C_h q
    exact ⟨hD, hV⟩
  have hcurrent : ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
      rate rewards C_star C_h q z = some o := by
    rw [← ReferenceOriginalCalendarCollectionRetainedEnergyStep.P_eq_current
      rate rewards C_star C_h q z]
    exact hPO
  have hH : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.H
      rate rewards C_star C_h q := by
    change ∃ v, ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
        rate rewards C_star C_h q z = some v ∧ v.2.1 = false
    exact ⟨o, hcurrent, hclear⟩
  have hEnabledIncoming :=
    ReferenceFirstCollectionOldRecorderFoundation.oldCell_enabled_eq_incoming
      rate rewards C_star C_h q z c (by simpa only [ReferenceOriginalCalendarCollectionRetainedEnergyStep.C]
        using hOC)
  have hE : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.E
      rate rewards C_star C_h q := by
    change z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
        rate rewards C_star C_h q ∧
      ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
        rate rewards C_star C_h q z = some true
    refine ⟨hD, ?_⟩
    rw [hEnabledIncoming]
    simpa using henabled
  have hG : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.G
      rate rewards C_star C_h q := by
    change (z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.B
          rate rewards C_star C_h q ∧
        z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.H
          rate rewards C_star C_h q) ∧
      z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.E
        rate rewards C_star C_h q
    exact ⟨⟨hB, hH⟩, hE⟩
  have hcarry := ReferenceOriginalCalendarCarriedStoppedEnergy.carriedPrefixReadout_of_present
    rate rewards C_star C_h q.val z o hP
  have henergy :
      ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
          rate rewards C_star C_h q.val a z =
        ReferenceOriginalCalendarCollectionRetainedEnergyStep.queueExp
          rate rewards C_star C_h a q.val z := by
    rw [ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy, hcarry]
    simp only [ReferenceOriginalCalendarCollectionRetainedEnergyStep.queueExp,
      hPO, Option.elim_some]
    congr 1
    ring
  have hW : ReferenceOriginalCalendarCollectionRetainedEnergyStep.W
      rate rewards C_star C_h q a z =
      ReferenceOriginalCalendarCollectionRetainedEnergyStep.queueExp
        rate rewards C_star C_h a q.val z := by
    simp [ReferenceOriginalCalendarCollectionRetainedEnergyStep.W, hB]
  have hinc := ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt_eq
    rate rewards C_star C_h q a z c hactive' hactualC
  have hx : ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt
      rate rewards C_star C_h q a z =
      ReferenceOriginalCalendarCollectionRetainedEnergyStep.x
        rate rewards C_star C_h q a z := by
    have hOldCell : ReferenceFirstCollectionOldRecorderFoundation.oldCell?
        rate rewards C_star C_h q z = some c := by
      simpa only [ReferenceOriginalCalendarCollectionRetainedEnergyStep.C] using hOC
    rw [hinc, ReferenceOriginalCalendarCollectionRetainedEnergyStep.x,
      Set.indicator_of_mem hG,
      ReferenceFirstCollectionOldRecorderFoundation.oldRaw, hOldCell]
  exact ⟨hG, henergy.trans hW.symm, hx⟩

/-- Exact domain identification for the collection and cutoff union: once the
actual collection selector is present, its active retained branch is precisely
the accepted `G` domain. -/
public theorem activeCollectionSelector_iff_G (q : Fin p.T) (a : Fin p.K) (z : X) :
    (ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
        rate rewards C_star C_h q z ∧
      (collectionOrCutoffSelector rate rewards C_star C_h q z).isSome = true) ↔
      z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.G
        rate rewards C_star C_h q := by
  constructor
  · rintro ⟨hactive, hsome⟩
    obtain ⟨data, hselector⟩ := Option.isSome_iff_exists.mp hsome
    rcases data with ⟨r, cp⟩
    rcases cp with ⟨c, payload⟩
    exact (collectionBranch_matches_retainedStep rate rewards C_star C_h q a z
      r c payload hactive hselector).1
  · intro hG
    change (z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.B
          rate rewards C_star C_h q ∧
        z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.H
          rate rewards C_star C_h q) ∧
      z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.E
        rate rewards C_star C_h q at hG
    have hD : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
        rate rewards C_star C_h q := hG.1.1.1
    change (ReferenceOriginalCalendarCollectionRetainedEnergyStep.C
      rate rewards C_star C_h q z).isSome = true at hD
    obtain ⟨c, hOC⟩ := Option.isSome_iff_exists.mp hD
    have hOC' : ReferenceFirstCollectionOldRecorderFoundation.oldCell?
        rate rewards C_star C_h q z = some c := by
      simpa only [ReferenceOriginalCalendarCollectionRetainedEnergyStep.C] using hOC
    change (ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h q z).bind
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0) = some c at hOC'
    obtain ⟨r, hr, hread⟩ := Option.bind_eq_some_iff.mp hOC'
    obtain ⟨payload, hrecordSelector⟩ := collectionRecordSelector_of_readout
      rate r c hread
    have hselector : collectionOrCutoffSelector rate rewards C_star C_h q z =
        some ⟨r, (c, payload)⟩ := by
      simp [collectionOrCutoffSelector, hr, hrecordSelector]
    have hliveNone : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none := by
      cases hLive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
      | none => rfl
      | some other =>
          exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint
            rate 0 r ⟨by rw [hLive]; rfl, by rw [hread]; rfl⟩)
    have hcell0 : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
      simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hliveNone, hread]
    have hactual : ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
        rate rewards C_star C_h q z = some c := by
      change (ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h q z).bind
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = some c
      rw [hr, Option.bind_some, hcell0]
    have hV : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.V
        rate rewards C_star C_h q := hG.1.1.2
    change (ReferenceOriginalCalendarCollectionRetainedEnergyStep.P
      rate rewards C_star C_h q.val z).isSome = true at hV
    obtain ⟨o, hP⟩ := Option.isSome_iff_exists.mp hV
    have hcurrent : ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
        rate rewards C_star C_h q z = some o := by
      rw [← ReferenceOriginalCalendarCollectionRetainedEnergyStep.P_eq_current
        rate rewards C_star C_h q z]
      exact hP
    obtain ⟨o', hcurrent', hclear⟩ := hG.1.2
    have ho : o' = o := Option.some.inj (hcurrent'.symm.trans hcurrent)
    subst o'
    have hE : z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.E
        rate rewards C_star C_h q := hG.2
    change z ∈ ReferenceOriginalCalendarCollectionRetainedEnergyStep.D
        rate rewards C_star C_h q ∧
      ReferenceFirstCollectionOldRecorderFoundation.incomingEnabled?
        rate rewards C_star C_h q z = some true at hE
    have hEnabled :=
      ReferenceFirstCollectionOldRecorderFoundation.oldCell_enabled_eq_incoming
        rate rewards C_star C_h q z c hOC'
    have hcEnabled : c.enabled = true := Option.some.inj (hEnabled.symm.trans hE.2)
    have hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
        rate rewards C_star C_h q z := by
      exact ⟨o, c, hP, hactual, hclear, hcEnabled⟩
    exact ⟨hactive, by simp [hselector]⟩

/-- Extract the original record from any of the three chosen selectors.
The alternatives remain their literal independent constructor tests. -/
public theorem chosenSelector_record
    (q : Fin p.T) (z : X) (r : Record) (c : Input) (payload : Payload)
    (hbranch : firstChosenSelector rate rewards C_star C_h q z = some ⟨r, (c, payload)⟩ ∨
      continuingLiveSelector rate rewards C_star C_h q z = some ⟨r, (c, payload)⟩ ∨
      renewedBirthSelector rate rewards C_star C_h q z = some ⟨r, (c, payload)⟩) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r ∧
      (firstChosenRecordSelector rate r = some (c, payload) ∨
        continuingLiveRecordSelector rate r = some (c, payload) ∨
        renewedBirthRecordSelector rate r = some (c, payload)) := by
  rcases hbranch with h | h | h
  · unfold firstChosenSelector at h
    obtain ⟨r', hr, hm⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cp, hcp, he⟩ := Option.map_eq_some_iff.mp hm
    cases he
    exact ⟨hr, Or.inl hcp⟩
  · unfold continuingLiveSelector at h
    obtain ⟨r', hr, hm⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cp, hcp, he⟩ := Option.map_eq_some_iff.mp hm
    cases he
    exact ⟨hr, Or.inr (Or.inl hcp)⟩
  · unfold renewedBirthSelector at h
    obtain ⟨r', hr, hm⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cp, hcp, he⟩ := Option.map_eq_some_iff.mp hm
    cases he
    exact ⟨hr, Or.inr (Or.inr hcp)⟩

private theorem actualRecord_first_lineage
    (q : Fin p.T) (z : X) (r : Record)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h q z = some r)
    (hfirst : r.input.state.coordinator = .first) :
    q.val = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ∧
      r.input.state.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p := by
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h q.val z := by
    by_contra hn
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h q z hn] at hr
    cases hr
  have hlookup := hr
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hlookup
  rw [ite_eq_left hlaunch.2] at hlookup
  obtain ⟨hk, hrecord⟩ := List.getElem?_eq_some_iff.mp hlookup
  let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length :=
    ⟨q.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h, hk⟩
  have hzero : k.val = 0 := by
    by_contra hn
    have hpositive : 0 < k.val := Nat.pos_of_ne_zero hn
    let j : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length := ⟨k.val - 1, by omega⟩
    have hj : j.val + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length := by dsimp [j]; omega
    have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
      (rate := rate) rewards C_star C_h z j.val hj
    have hcoord := congrArg (fun state : ReferenceActivePhysicalStep.State p rate =>
      state.coordinator) hadj
    have hphase :=
      (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
        rate rewards C_star C_h z).1
    have hout := (hphase j).2.2.2.1
    have hindex : j.val + 1 = k.val := by dsimp [j]; omega
    apply hout
    apply hcoord.symm.trans
    simpa only [hindex, show k.val = q.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h from rfl,
      hrecord] using hfirst
  have hdate : q.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
    change q.val - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h = 0 at hzero
    have hs := hlaunch.2
    omega
  obtain ⟨active, hl, _, hbank, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate z rewards C_star C_h hlaunch.1
  have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate z rewards C_star C_h active hl
  have hhead : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[0]? = some r := by
    simpa only [hdate, Nat.sub_self] using hlookup
  have hstate : r.input.state = active := by
    cases he : ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h with
    | nil => simp only [he, List.getElem?_nil] at hhead; cases hhead
    | cons head tail =>
        simp only [he, List.getElem?_cons_zero, Option.some.injEq] at hhead
        subst head
        rw [he] at hchain
        exact hchain.1
  exact ⟨hdate, by rw [hstate]; exact hbank⟩

/-- FIRST is the original launch date and the literal empty initialized run.
No successful later sampler, prefix-totality premise, or supplied launch is used. -/
public theorem firstSelector_initialPrefix
    (q : Fin p.T) (z : X) (r : Record) (c : Input) (payload : Payload)
    (hselector : firstChosenSelector rate rewards C_star C_h q z =
      some ⟨r, (c, payload)⟩) :
    q.val = ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z ∧
      r.input.state.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h q.val z = some [] ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h q.val z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q [])) ∧
      ∀ a : Fin p.K,
        ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
          rate rewards C_star C_h q.val a z = 1 := by
  unfold firstChosenSelector at hselector
  obtain ⟨r', hr, hm⟩ := Option.bind_eq_some_iff.mp hselector
  obtain ⟨cp, hcp, he⟩ := Option.map_eq_some_iff.mp hm
  cases he
  have hfirst := firstRecordSelector_incoming rate r c payload hcp
  obtain ⟨hdate, hbank⟩ :=
    actualRecord_first_lineage
      rate rewards C_star C_h q z r hr hfirst
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h q.val z := by
    by_contra hn
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h q z hn] at hr
    cases hr
  have hdate' : q.val =
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h z := hdate
  have hinputs : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h q.val z = some [] := by
    unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
    rw [ite_eq_left hlaunch, hdate']
    simp
  refine ⟨hdate', hbank, hinputs, ?_, ?_⟩
  · simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hinputs, Option.map_some]
  · intro a
    rw [hdate']
    exact ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy_sourceStart
      rate rewards C_star C_h z a hlaunch.1

/-- Original-source restoration and the complete canonical chosen cell,
for FIRST, continuing LIVE, and renewed birth at the SAME calendar date.
The whole reward table and actual prepared family are retained. -/
public theorem chosenSelector_canonical
    (q : Fin p.T) (z : X) (r : Record) (c : Input) (payload : Payload)
    (hbranch : firstChosenSelector rate rewards C_star C_h q z = some ⟨r, (c, payload)⟩ ∨
      continuingLiveSelector rate rewards C_star C_h q z = some ⟨r, (c, payload)⟩ ∨
      renewedBirthSelector rate rewards C_star C_h q z = some ⟨r, (c, payload)⟩) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = q ∧ r.input.rewards = rewards ∧
      ∃ (selected : ReferenceActivePhysicalStep.Selection r.input)
        (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r),
        r.output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = payload ∧
        c = ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
          selected.view.pendingAtChoice
          (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
          selected.view.complementWeights selected.view.cutoff
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) ∧
        c.recordedArm = ReferenceFirstWindowNumericalStream.sourceArm r selected.view.payload
          selected.view.pendingAtChoice
          (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
          selected.view.complementWeights selected.view.cutoff
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) ∧
        c.enabled = true ∧
        c.reward = (fun a => ((rewards q a).val : ℝ) / (ConstructorDimensions.D p : ℝ)) ∧
        c.rate = payload.rate ∧
        ∀ a, RecordedRoundMoments.normalizedQuantizedArrival Q c a =
          ((if c.recordedArm = some a then
            Nat.floor ((ConstructorDimensions.D p : ℝ) * rate.eta.val *
              (((rewards q a).val : ℝ) / (ConstructorDimensions.D p : ℝ)) /
                payload.rate a) else 0 : ℕ) : ℝ) / ((Q).n : ℝ) := by
  obtain ⟨hr, hrecord⟩ := chosenSelector_record rate rewards C_star C_h q z r c payload hbranch
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z r hr
  obtain ⟨selected, ho, hs, hp, _, _, hc, hmark⟩ :=
    chosenRecordSelector_canonical rate r c payload hrecord
  have hread : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
    rcases hrecord with h | h | h
    · exact firstRecordSelector_cell rate r c payload h
    · exact continuingLiveRecordSelector_cell rate r c payload h
    · exact renewedBirthRecordSelector_cell rate r c payload h
  obtain ⟨henabled, selected', hs', hreward, hrate, hraw⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical 0 r c hread
  have he : selected' = selected := Option.some.inj (hs'.symm.trans hs)
  subst selected'
  rw [hp] at hrate hraw
  rw [hf.2.2.1, hf.2.2.2] at hreward hraw
  refine ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2,
    selected, ho, hs, hp, hc, hmark, henabled, hreward, hrate, ?_⟩
  intro a
  unfold RecordedRoundMoments.normalizedQuantizedArrival
  rw [hraw a]

/-- An actual chosen FIRST cell performs the initial retained update,
including a genuine marker whose integer floor happens to be zero. -/
public theorem firstSelector_activeUpdate
    (q : Fin p.T) (z : X) (r : Record) (c : Input) (payload : Payload)
    (hselector : firstChosenSelector rate rewards C_star C_h q z =
      some ⟨r, (c, payload)⟩) :
    ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z := by
  obtain ⟨_, _, _, hprefix, _⟩ :=
    firstSelector_initialPrefix rate rewards C_star C_h q z r c payload hselector
  obtain ⟨_, _, _, _, selected, ho, hs, hp, hc, hm, henabled, _⟩ :=
    chosenSelector_canonical rate rewards C_star C_h q z r c payload (Or.inl hselector)
  refine ⟨_, c, hprefix,
    firstSelector_actualCell rate rewards C_star C_h q z r c payload hselector,
    ?_, henabled⟩
  rfl

/-- Chosen branch increments use the energy of the SAME original prefix.
In particular renewed birth keeps this inherited queue; its energy is not
reinitialized from the newly installed payload. -/
public theorem chosenSelector_retainedContribution
    (q : Fin p.T) (a : Fin p.K) (z : X) (r : Record) (c : Input) (payload : Payload)
    (hactive : ReferenceOriginalCalendarCarriedStoppedEnergy.activeUpdateAt
      rate rewards C_star C_h q z)
    (hbranch : firstChosenSelector rate rewards C_star C_h q z = some ⟨r, (c, payload)⟩ ∨
      continuingLiveSelector rate rewards C_star C_h q z = some ⟨r, (c, payload)⟩ ∨
      renewedBirthSelector rate rewards C_star C_h q z = some ⟨r, (c, payload)⟩) :
    ∃ o, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h q.val z = some o ∧
      o.2.1 = false ∧
      ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
        rate rewards C_star C_h q.val a z =
        Real.exp (beta * ((o.1 a).2 : ℝ) / ((Q).n : ℝ)) ∧
      ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt
        rate rewards C_star C_h q a z =
        RecordedRoundMoments.normalizedQuantizedArrival Q c a - 4 ∧
      branchContribution rate rewards C_star C_h q a z (some ⟨r, (c, payload)⟩) =
        Real.exp (beta * ((o.1 a).2 : ℝ) / ((Q).n : ℝ)) *
          (Real.exp (beta * (RecordedRoundMoments.normalizedQuantizedArrival Q c a - 4)) - 1) := by
  have hactive' := hactive
  obtain ⟨o, c₀, hP, _, hclear, _⟩ := hactive'
  have hcell : ReferenceOriginalCalendarCarriedStoppedEnergy.actualCellAt
      rate rewards C_star C_h q z = some c := by
    rcases hbranch with h | h | h
    · exact firstSelector_actualCell rate rewards C_star C_h q z r c payload h
    · exact continuingLiveSelector_actualCell rate rewards C_star C_h q z r c payload h
    · exact renewedBirthSelector_actualCell rate rewards C_star C_h q z r c payload h
  have hcarry := ReferenceOriginalCalendarCarriedStoppedEnergy.carriedPrefixReadout_of_present
    rate rewards C_star C_h q.val z o hP
  have henergy : ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy
      rate rewards C_star C_h q.val a z =
      Real.exp (beta * ((o.1 a).2 : ℝ) / ((Q).n : ℝ)) := by
    simp only [ReferenceOriginalCalendarCarriedStoppedEnergy.carriedStoppedEnergy, hcarry]
  refine ⟨o, hP, hclear, henergy,
    ReferenceOriginalCalendarCarriedStoppedEnergy.normalizedArrivalIncrementAt_eq
      rate rewards C_star C_h q a z c hactive hcell, ?_⟩
  simp only [branchContribution, ite_eq_left hactive, henergy]

end Bandits.Support.ReferenceOriginalCalendarRetainedBranchPartition

end
