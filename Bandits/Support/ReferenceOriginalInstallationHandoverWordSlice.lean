/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalFixedInstallationHandoverSupport

import Mathlib.Tactic

/-!
# Same-scalar selected installation words on original H support

For a literal original raw H task, the actual selected installation payload
is unchanged when only the current affine family changes and its scalar slice
is fixed. First dispatch and later empty-collection dispatch use the same
whole scalar assignment vector; a continuing live record uses its retained
payload. Every record and selected choice below is an actual source witness.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ReferenceOriginalFixedInstallationHandoverSupport
open Bandits.Support.CoordinatorLocalArmChoice
open scoped Classical

namespace Bandits.Support.ReferenceOriginalInstallationHandoverWordSlice

abbrev Parameters := ConstructorDimensions.Parameters
variable {p : Parameters}
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable (p : Parameters) := ActualInitializationPhysicalStep.GridRewardTable p
abbrev Record (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "lookup" =>
  ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
local notation "rawTask" =>
  ReferenceOriginalFixedInstallationHandoverSupport.rawPending rate rewards C_star C_h

private theorem rawPending_replaceSourceControl
    (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (u : ContinuousLearningRows.TimeControl p) :
    rawTask ell t i z ↔ rawTask ell t i
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) := by
  have hsource := ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current
    control0 t z u
  rw [ReferenceOriginalFixedInstallationHandoverSupport.rawPending_factor
      rate rewards C_star C_h control0 ell t i z,
    ReferenceOriginalFixedInstallationHandoverSupport.rawPending_factor
      rate rewards C_star C_h control0 ell t i
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u),
    hsource]

/-- Each control on a supported scalar fibre has its own actual record and
selected choice. This constructs selectable words from the original support,
without assuming that a record or successful dispatch was supplied. -/
public theorem replacement_actual_selected_witness
    (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hp : rawTask ell t i z) (u : ContinuousLearningRows.TimeControl p) :
    ∃ (r : Record rate) (selected : ReferenceActivePhysicalStep.Selection r.input),
      lookup t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) = some r ∧
      r.output.preparation.coordinator.selection = some selected ∧
      i ∈ selected.view.pendingAtChoice := by
  have hrep := (rawPending_replaceSourceControl rate rewards C_star C_h
    control0 ell t i z u).mp hp
  obtain ⟨_hle, _birth, r, hr, selected, hsel, hi⟩ :=
    ReferenceOriginalFixedInstallationHandoverSupport.rawPending_actual_choice
      rate rewards C_star C_h ell t i _ hrep
  exact ⟨r, selected, hr, hsel, hi⟩

private theorem actualRecord_fields (t : Fin p.T) (z : SourceInput p)
    (r : Record rate) (hr : lookup t z = some r) :
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

private theorem actual_record_state_eq_of_same_prefix
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z z' : SourceInput p) (r r' : Record rate)
    (hr : lookup t z = some r) (hr' : lookup t z' = some r')
    (hprefix : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z') :
    r.input.state = r'.input.state := by
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z' := by
    calc
      _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) :=
        ReferenceSourcePrefixHistoryFiltration.incoming_factor
          rate rewards C_star C_h control0 t z
      _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z') :=
        congrArg (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t) hprefix
      _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z' :=
        (ReferenceSourcePrefixHistoryFiltration.incoming_factor
          rate rewards C_star C_h control0 t z').symm
  change (lookup t z).map
      (fun q => ReferenceActivePhysicalStepMeasurability.encodeState q.input.state) =
    (lookup t z').map
      (fun q => ReferenceActivePhysicalStepMeasurability.encodeState q.input.state) at hin
  rw [hr, hr'] at hin
  simp only [Option.map_some, Option.some.injEq] at hin
  exact ReferenceActivePhysicalStepMeasurability.encodeState_injective hin

private theorem rawPending_actual_state_shape
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hp : rawTask ell t i z) :
    ∃ r : Record rate, lookup t z = some r ∧
      ((ell = t ∧ r.input.state.coordinator = .first) ∨
       (ell = t ∧ ∃ payload : Payload rate, ∃ ledger : Ledger rate,
          ∃ saved : Option (Fin p.T × Bool),
            r.input.state.coordinator = .collection payload ledger saved ∧
            ledger.pending = ∅) ∨
       (ell.val < t.val ∧ ∃ registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
          ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters registers,
          ∃ base : Fin (p.m - 1) → ℕ,
            r.input.state.coordinator = .live registers owned base)) := by
  obtain ⟨hle, hbirth, r, hr, _selected, _hsel, _hi⟩ :=
    ReferenceOriginalFixedInstallationHandoverSupport.rawPending_actual_choice
      rate rewards C_star C_h ell t i z hp
  by_cases he : ell = t
  · subst t
    rcases hbirth with hfirst | hlater
    · obtain ⟨birth, hb, hcoord⟩ :=
        (ReferenceOriginalFixedInstallationHandoverSupport.initialBirthAt_iff_actual_first
          rate rewards C_star C_h ell z).mp hfirst
      have heq := Option.some.inj (hb.symm.trans hr)
      subst birth
      exact ⟨r, hr, Or.inl ⟨rfl, hcoord⟩⟩
    · obtain ⟨birth, payload, ledger, saved, hb, hcoord, hempty⟩ :=
        (ReferenceOriginalFixedInstallationHandoverSupport.laterBirthAt_iff_actual_empty_collection
          rate rewards C_star C_h ell z).mp hlater
      have heq := Option.some.inj (hb.symm.trans hr)
      subst birth
      exact ⟨r, hr, Or.inr (Or.inl ⟨rfl, payload, ledger, saved, hcoord, hempty⟩)⟩
  · have hlt : ell.val < t.val := by
      have hneq : ell.val ≠ t.val := fun h => he (Fin.ext h)
      omega
    have hrequest :=
      (ReferenceOriginalFixedInstallationHandoverSupport.rawPending_iff_preRoundRequest
        rate rewards C_star C_h ell t i z).mp hp
    rcases hrequest with hbirthRequest | ⟨_hlt, hlive, _hcontinues⟩
    · exact False.elim (he hbirthRequest.1)
    · unfold ReferenceOriginalFixedInstallationHandoverSupport.liveRequest
        ReferenceSourcePrefixHistoryFiltration.incoming at hlive
      rw [hr] at hlive
      cases hcoord : r.input.state.coordinator with
      | first => simp [ReferenceCollectionOutcomeMeasurability.optionalElim,
          ReferenceOriginalFixedInstallationHandoverSupport.liveRequestCode,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hcoord] at hlive
      | live registers owned base =>
          exact ⟨r, hr, Or.inr (Or.inr ⟨hlt, registers, owned, base, hcoord⟩)⟩
      | collection payload ledger saved =>
          simp [ReferenceCollectionOutcomeMeasurability.optionalElim,
            ReferenceOriginalFixedInstallationHandoverSupport.liveRequestCode,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hcoord] at hlive
      | dagger =>
          simp [ReferenceCollectionOutcomeMeasurability.optionalElim,
            ReferenceOriginalFixedInstallationHandoverSupport.liveRequestCode,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hcoord] at hlive

private theorem record_selection_eq_prepare (r : Record rate) :
    r.output.preparation.coordinator.selection =
      (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection := by
  rw [r.output_eq]
  rfl

private theorem first_selection_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hfirst : x.state.coordinator = .first)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hsel : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected) :
    selected.view.payload =
      (CoordinatorAssignmentRegisterInstall.installFirst
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput x))).registers.payload := by
  have h := congrArg Prod.snd
    (ReferenceActiveTemporalCausality.first_dispatch_readout x hfirst)
  change (ReferenceActivePhysicalStep.dispatch x).selection = some selected at hsel
  simp only [ReferenceActivePhysicalStep.DispatchCut.downView, hsel, Option.map_some,
    ReferenceActiveTemporalCausality.firstReadout, Option.some.injEq] at h
  exact congrArg (fun view => view.payload) h

private theorem live_selection_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : x.state.coordinator = .live registers owned base)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hsel : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected) :
    selected.view.payload = registers.payload := by
  change (ReferenceActivePhysicalStep.dispatch x).selection = some selected at hsel
  have hd : ReferenceActivePhysicalStep.dispatch x = .live registers owned base
      (CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x registers owned base)) := by
    simp only [ReferenceActivePhysicalStep.dispatch, hlive, CoordinatorRoundDispatch.dispatch]
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

private theorem actual_record_index (t : Fin p.T) (z : SourceInput p)
    (r : Record rate) (hr : lookup t z = some r) :
    ∃ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = r := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split_ifs at hr with hstart
  · obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp hr
    exact ⟨⟨_, hk⟩, heq⟩

private theorem actual_collection_selected_output (t : Fin p.T) (z : SourceInput p)
    (r : Record rate) (hr : lookup t z = some r)
    (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : r.input.state.coordinator = .collection payload ledger saved)
    (hempty : ledger.pending = ∅)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some selected) :
    ∃ u : Fin p.T, u.val + 1 = ledger.cutoff ∧
      ∃ core : CoordinatorRoundDispatch.CollectionCoreValid
          (ReferenceActivePhysicalStep.collectionInput r.input payload ledger
            (ReferenceActivePhysicalStep.collectionClock payload ledger saved u) u),
        ∃ started : CoordinatorPhaseClock.StartRoundResult p,
          CoordinatorPhaseClock.startRound p rate.eta.val r.input.time
            (ReferenceActivePhysicalStep.collectionClock payload ledger saved u) ledger.pending =
              .ok started ∧
          ∃ instruction : CoordinatorPhaseClock.AssignmentStartInstruction p,
            started.assignmentStart = some instruction ∧ instruction.time = r.input.time ∧
            ∃ consistent : LaterAssignmentStartOperation.LocalConsistency payload
                (CoordinatorRoundDispatch.collectionOperationLedger
                  (ReferenceActivePhysicalStep.collectionInput r.input payload ledger
                    (ReferenceActivePhysicalStep.collectionClock payload ledger saved u) u)
                  core.payload_n_eq),
              ∃ output : LaterAssignmentStartOperation.SuccessfulStart payload
                  (CoordinatorRoundDispatch.collectionOperationLedger
                    (ReferenceActivePhysicalStep.collectionInput r.input payload ledger
                      (ReferenceActivePhysicalStep.collectionClock payload ledger saved u) u)
                    core.payload_n_eq) instruction r.input.row,
                ∃ hlocal : output.localConsistency = consistent,
                  LaterAssignmentStartOperation.laterAssignmentStart payload
                      (CoordinatorRoundDispatch.collectionOperationLedger
                        (ReferenceActivePhysicalStep.collectionInput r.input payload ledger
                          (ReferenceActivePhysicalStep.collectionClock payload ledger saved u) u)
                        core.payload_n_eq)
                      instruction r.input.row consistent = .success output hlocal ∧
                    selected.view.payload = output.payload := by
  obtain ⟨k, hk⟩ := actual_record_index rate rewards C_star C_h t z r hr
  subst r
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hstate' : R[k.val].input.state.coordinator = .collection payload ledger saved := hstate
  have hsel' : R[k.val].output.preparation.coordinator.selection = some selected := hsel
  by_cases hbefore : R[k.val].input.time.val + 1 < ledger.freezeAt
  · obtain ⟨u, hu, core, started, hstart, instruction, hassignment,
      htime, _hkind, _hsigma, _hcutoff, consistent, output, hlocal,
      hcall, _clockData, _installed, _arm, _hprior, _hresult, _hpending,
      _hinstall, _hdispatch, _hscore, _hqueue, _hprevious, _hbase,
      _henvelope, hpayload, _hanchor, _hlawAnchor, _hcutoffRegisters,
      _hcurrentRegisters, _hsourceScore, _hinitialQueue, _hqueues,
      _hvector, actualSelected, _hselection, houtputSelection,
      hselectedPayload, _⟩ :=
      ReferenceCompleteEmptyCorrectedCoordinatorStep.complete_empty_corrected_coordinator_step
        rewards C_star C_h z k payload ledger saved hstate' hempty hbefore
    have hselectedEq := Option.some.inj (houtputSelection.symm.trans hsel')
    subst actualSelected
    exact ⟨u, hu, core, started, hstart, instruction, hassignment, htime,
      consistent, output, hlocal, hcall, hselectedPayload.trans hpayload⟩
  · obtain ⟨u, hu, core, _hscore, started, hstart, instruction,
      hassignment, htime, _hkind, output, hlocal, hcall, _hsource,
      _hinitial, _hweight, _hanchor, _hqueues, _hdomains, _hbase,
      _hclock, _mass, _sampled, _hmass, _hsampled, _hvector, _arm,
      _hdispatch, _hprepared, actualSelected, _hselection, hpayload,
      _hcutoff, _hlive, houtputSelection, _⟩ :=
      ReferenceCompleteEmptyRenewalCoordinatorStep.complete_empty_renewal_coordinator_step
        rate rewards C_star C_h z k payload ledger saved hstate' hempty
          (Nat.le_of_not_gt hbefore)
    have hselectedEq := Option.some.inj (houtputSelection.symm.trans hsel')
    subst actualSelected
    exact ⟨u, hu, core, started, hstart, instruction, hassignment, htime,
      _, output, hlocal, hcall, hpayload⟩

private theorem localConsistency_eq {P : Payload rate}
    {l : LaterAssignmentStartOperation.LocalLedger P}
    (a b : LaterAssignmentStartOperation.LocalConsistency P l) : a = b := by
  have hfreeze : a.oldFreezeAt = b.oldFreezeAt :=
    a.oldFreezeAt_eq.trans b.oldFreezeAt_eq.symm
  cases a
  cases b
  cases hfreeze
  rfl

private theorem collection_selection_payload_eq_of_scalar
    (t : Fin p.T) (z z' : SourceInput p) (r r' : Record rate)
    (hr : lookup t z = some r) (hr' : lookup t z' = some r')
    (payload : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hc : r.input.state.coordinator = .collection payload ledger saved)
    (hc' : r'.input.state.coordinator = .collection payload ledger saved)
    (hempty : ledger.pending = ∅)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (selected' : ReferenceActivePhysicalStep.Selection r'.input)
    (hsel : r.output.preparation.coordinator.selection = some selected)
    (hsel' : r'.output.preparation.coordinator.selection = some selected')
    (hscalar : (r.input.row.2 r.input.time).1 = (r'.input.row.2 r'.input.time).1) :
    selected.view.payload = selected'.view.payload := by
  obtain ⟨u, hu, core, started, hstart, instruction, hassignment, htime,
    consistent, output, hlocal, hcall, hpayload⟩ :=
    actual_collection_selected_output rate rewards C_star C_h t z r hr payload ledger saved
      hc hempty selected hsel
  obtain ⟨u', hu', core', started', hstart', instruction', hassignment', htime',
    consistent', output', hlocal', hcall', hpayload'⟩ :=
    actual_collection_selected_output rate rewards C_star C_h t z' r' hr' payload ledger saved
      hc' hempty selected' hsel'
  have huEq : u = u' := by
    apply Fin.ext
    omega
  subst u'
  have hdate : r.input.time = r'.input.time :=
    (actualRecord_fields rate rewards C_star C_h t z r hr).2.2.1.trans
      (actualRecord_fields rate rewards C_star C_h t z' r' hr').2.2.1.symm
  have hstarted : started = started' := by
    apply Except.ok.inj
    change CoordinatorPhaseClock.startRound p rate.eta.val r.input.time
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved u) ledger.pending =
        .ok started at hstart
    change CoordinatorPhaseClock.startRound p rate.eta.val r'.input.time
      (ReferenceActivePhysicalStep.collectionClock payload ledger saved u) ledger.pending =
        .ok started' at hstart'
    rw [← hdate] at hstart'
    exact hstart.symm.trans hstart'
  subst started'
  have hinstruction : instruction = instruction' := by
    apply Option.some.inj
    exact hassignment.symm.trans hassignment'
  subst instruction'
  have hconsistent : consistent = consistent' := localConsistency_eq rate consistent consistent'
  have hlocal'' : output'.localConsistency = consistent := hlocal'.trans hconsistent.symm
  have hcall'' : LaterAssignmentStartOperation.laterAssignmentStart payload
      (CoordinatorRoundDispatch.collectionOperationLedger
        (ReferenceActivePhysicalStep.collectionInput r.input payload ledger
          (ReferenceActivePhysicalStep.collectionClock payload ledger saved u) u)
        core.payload_n_eq)
      instruction r'.input.row consistent = .success output' hlocal'' := by
    cases hconsistent
    exact hcall'
  have hvector : LaterAssignmentStartOperation.ownAssignmentVector r.input.row instruction.time =
      LaterAssignmentStartOperation.ownAssignmentVector r'.input.row instruction.time := by
    calc
      _ = ContinuousControlSlice.assignmentVector (r.input.row.2 r.input.time).1 := by
        rw [htime]
        rfl
      _ = ContinuousControlSlice.assignmentVector (r'.input.row.2 r'.input.time).1 :=
        congrArg ContinuousControlSlice.assignmentVector hscalar
      _ = _ := by rw [htime']; rfl
  have h := LaterAssignmentStartMeasurability.laterAssignmentStart_payload?_eq_of_ownAssignmentVector_eq
    payload ⟨_, instruction, consistent⟩ r.input.row r'.input.row hvector
  rw [hcall, hcall''] at h
  change some output.payload = some output'.payload at h
  exact hpayload.trans ((Option.some.inj h).trans hpayload'.symm)

private theorem replacement_scalar_eq
    (t : Fin p.T) (z : SourceInput p) (u v : ContinuousLearningRows.TimeControl p)
    (r r' : Record rate)
    (hr : lookup t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) = some r)
    (hr' : lookup t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z v) = some r')
    (huv : u.1 = v.1) :
    (r.input.row.2 r.input.time).1 = (r'.input.row.2 r'.input.time).1 := by
  obtain ⟨hrows, hselected, htime, _hrewards⟩ :=
    actualRecord_fields rate rewards C_star C_h t _ r hr
  obtain ⟨hrows', hselected', htime', _hrewards'⟩ :=
    actualRecord_fields rate rewards C_star C_h t _ r' hr'
  simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hselected, htime,
    hrows', hselected', htime', ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ActualInitializationPhysicalStep.selectedRowIndex,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex, Function.update_self]
  exact huv

/-- Actual selected payloads agree across controls on one whole scalar slice.
The emitted DOWN record and its exact flattened codec word agree for every
follower; the affine hash remains the literal hash of that word at the chosen
control. -/
public theorem replacement_payload_eq_of_same_slice
    (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hp : rawTask ell t i z)
    (u v : ContinuousLearningRows.TimeControl p) (huv : u.1 = v.1)
    (r r' : Record rate)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (selected' : ReferenceActivePhysicalStep.Selection r'.input)
    (hr : lookup t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) = some r)
    (hr' : lookup t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z v) = some r')
    (hsel : r.output.preparation.coordinator.selection = some selected)
    (hsel' : r'.output.preparation.coordinator.selection = some selected') :
    selected.view.payload = selected'.view.payload ∧
      ∀ follower : Fin (p.m - 1),
        selected.view.payload.downRecord follower = selected'.view.payload.downRecord follower ∧
        CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload follower =
          CoordinatorLocalArmChoice.storedDownFlatWord selected'.view.payload follower := by
  obtain ⟨r0, hr0, hshape⟩ :=
    rawPending_actual_state_shape rate rewards C_star C_h ell t i z hp
  have hprefixU := ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current
    control0 t z u
  have hprefixV := ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current
    control0 t z v
  have hstateU := actual_record_state_eq_of_same_prefix rate rewards C_star C_h
    control0 t _ z r r0 hr hr0 hprefixU
  have hstateV := actual_record_state_eq_of_same_prefix rate rewards C_star C_h
    control0 t _ z r' r0 hr' hr0 hprefixV
  have hscalar := replacement_scalar_eq rate rewards C_star C_h t z u v r r' hr hr' huv
  have hprep : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection = some selected := by
    rw [← record_selection_eq_prepare rate r]
    exact hsel
  have hprep' : (ReferenceActivePhysicalStep.prepare r'.input).coordinator.selection = some selected' := by
    rw [← record_selection_eq_prepare rate r']
    exact hsel'
  have hpayload : selected.view.payload = selected'.view.payload := by
    rcases hshape with ⟨he, hfirst⟩ | ⟨he, payload, ledger, saved, hcollection, hempty⟩ |
      ⟨_hlt, registers, owned, base, hlive⟩
    · have hc : r.input.state.coordinator = .first :=
        (congrArg ReferenceActivePhysicalStep.State.coordinator hstateU).trans hfirst
      have hc' : r'.input.state.coordinator = .first :=
        (congrArg ReferenceActivePhysicalStep.State.coordinator hstateV).trans hfirst
      have htime : r.input.time = r'.input.time :=
        (actualRecord_fields rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) r hr).2.2.1.trans
        ((actualRecord_fields rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z v) r' hr').2.2.1.symm)
      have hlaunch : CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput r.input) =
        CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput r'.input) := by
        unfold CoordinatorRoundDispatch.firstLaunchInput ReferenceActivePhysicalStep.firstInput
          LaterAssignmentStartOperation.ownAssignmentVector
        dsimp only
        congr 1
        · exact congrArg ContinuousControlSlice.assignmentVector hscalar
      exact (first_selection_payload rate r.input hc selected hprep).trans
        ((congrArg (fun launch =>
          (CoordinatorAssignmentRegisterInstall.installFirst launch).registers.payload) hlaunch).trans
          (first_selection_payload rate r'.input hc' selected' hprep').symm)
    · have hc : r.input.state.coordinator = .collection payload ledger saved :=
        (congrArg ReferenceActivePhysicalStep.State.coordinator hstateU).trans hcollection
      have hc' : r'.input.state.coordinator = .collection payload ledger saved :=
        (congrArg ReferenceActivePhysicalStep.State.coordinator hstateV).trans hcollection
      exact collection_selection_payload_eq_of_scalar rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z v)
        r r' hr hr' payload ledger saved hc hc' hempty selected selected' hsel hsel' hscalar
    · have hc : r.input.state.coordinator = .live registers owned base :=
        (congrArg ReferenceActivePhysicalStep.State.coordinator hstateU).trans hlive
      have hc' : r'.input.state.coordinator = .live registers owned base :=
        (congrArg ReferenceActivePhysicalStep.State.coordinator hstateV).trans hlive
      exact (live_selection_payload rate r.input registers owned base hc selected hprep).trans
        (live_selection_payload rate r'.input registers owned base hc' selected' hprep').symm
  refine ⟨hpayload, ?_⟩
  intro follower
  rw [hpayload]
  exact ⟨rfl, rfl⟩

/-- The source support constructs both actual choices for every pair of
current controls on the same scalar slice and supplies their common word. -/
public theorem replacement_actual_selected_word_eq_of_same_slice
    (control0 : ContinuousLearningRows.TimeControl p)
    (ell t : Fin p.T) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hp : rawTask ell t i z)
    (u v : ContinuousLearningRows.TimeControl p) (huv : u.1 = v.1) :
    ∃ (r : Record rate) (selected : ReferenceActivePhysicalStep.Selection r.input)
      (r' : Record rate) (selected' : ReferenceActivePhysicalStep.Selection r'.input),
      lookup t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) = some r ∧
      lookup t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z v) = some r' ∧
      r.output.preparation.coordinator.selection = some selected ∧
      r'.output.preparation.coordinator.selection = some selected' ∧
      selected.view.payload = selected'.view.payload ∧
      ∀ follower : Fin (p.m - 1),
        selected.view.payload.downRecord follower = selected'.view.payload.downRecord follower ∧
        CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload follower =
          CoordinatorLocalArmChoice.storedDownFlatWord selected'.view.payload follower := by
  obtain ⟨r, selected, hr, hsel, _hi⟩ :=
    replacement_actual_selected_witness rate rewards C_star C_h control0 ell t i z hp u
  obtain ⟨r', selected', hr', hsel', _hi'⟩ :=
    replacement_actual_selected_witness rate rewards C_star C_h control0 ell t i z hp v
  have heq := replacement_payload_eq_of_same_slice rate rewards C_star C_h control0
    ell t i z hp u v huv r r' selected selected' hr hr' hsel hsel'
  exact ⟨r, selected, r', selected', hr, hr', hsel, hsel', heq.1, heq.2⟩

end Bandits.Support.ReferenceOriginalInstallationHandoverWordSlice

end
