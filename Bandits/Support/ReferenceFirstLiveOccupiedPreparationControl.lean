/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveReleaseGeometry
public import Bandits.Support.ReferenceRetainedSourceCoupling
public import Bandits.Support.ReferenceReleaseStrictPastFactor

/-!
# First-live occupied preparation across current controls

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,128-175,293-345`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This module keeps the original retained source, physical state, whole DOWN
records, and continuous control slice. It proves that the actual occupied
ordinary PREPARE configurations at a selected empty first-live choice are the
same for every replacement of that current control. It introduces no second
run, supplied occupancy trace, or current-control readiness assumption.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceGeneratedActivePrefixFactor
open Bandits.Support.ReferenceRetainedBoundaryMeasurability
open Bandits.Support.ReferenceFirstLiveReleaseGeometry
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveOccupiedPreparationControl

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev Selection := ReferenceActivePhysicalStep.Selection (p := p) (rate := rate)
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

/-- Replacing the whole current control in the retained source produces
exactly the existing physical boundary resampling operation. All other
original source coordinates remain those of the same retained remainder. -/
theorem retained_generated_next_input_eq_withControl
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t s hs control0)
    (u : TimeControl p) :
    ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
      rate rewards C_star C_h q t s hs control0 x u =
      ReferenceLaterOptionalControlResampling.withControl
        (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
          rate rewards C_star C_h q t s hs control0 x) u := by
  let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 x
  let source0 := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  have hsplit : ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source0 =
      (control0, x.1) :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).apply_symm_apply _
  have hindex : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source0 = q :=
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t control0 x.1 x.2.1
  have hreplace : ReferenceGeneratedActivePrefixFactor.splitSource q t u x.1 =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source0 u := by
    have h := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
      p q t source0 u hindex
    rw [hsplit] at h
    exact h
  have hbaseline :
      ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate beta source0 = beta := rfl
  rw [ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_roundInputAtSource,
    hreplace]
  change ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate beta
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p beta.time source0 u) = _
  rw [ReferenceFixedTimeSourceControlCoupling.roundInputAtSource_replaceSourceControl,
    hbaseline]

/-- The current coordinate of the actual phase factor is the lossless code
of this same retained incoming physical state. -/
theorem retained_phaseFactor_current_eq_boundary_state
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t s hs control0) :
    ReferenceReleaseStrictPastFactor.phaseFactor rate rewards C_star C_h q t s hs
      control0 x ⟨t.val - s, Nat.lt_succ_self _⟩ =
      ReferenceActivePhysicalStepMeasurability.encodeState
        (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
          rate rewards C_star C_h q t s hs control0 x).state := by
  rw [ReferenceReleaseStrictPastFactor.phaseFactor_eq
    rate rewards C_star C_h q t s hs control0 x control0]
  rfl

private theorem selected_live_payload_cutoff_weights
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator = .live r owned base)
    (hprior : r.priorClock.u = none)
    (hnoCut : ReferenceCollectionPhaseHistory.cutoffChosen x = false)
    (selected : Selection x)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected)
    (hempty : selected.view.pendingAtChoice = ∅) :
    selected.view.payload = r.payload ∧ selected.view.cutoff = none ∧
      HEq selected.view.complementWeights r.complementWeights := by
  let liveInput := ReferenceActivePhysicalStep.liveInput x r owned base
  have hdispatch : ReferenceActivePhysicalStep.dispatch x =
      .live r owned base (CoordinatorRoundDispatch.dispatchLive liveInput) := by
    simp only [ReferenceActivePhysicalStep.dispatch, hstate,
      CoordinatorRoundDispatch.dispatch]
    rfl
  have hselection :
      (ReferenceActivePhysicalStep.DispatchCut.live r owned base
        (CoordinatorRoundDispatch.dispatchLive liveInput)).selection = some selected := by
    simpa [ReferenceActivePhysicalStep.prepare, hdispatch] using hselected
  cases hout : CoordinatorRoundDispatch.dispatchLive liveInput with
  | clockFailure failure hfailure =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, hout] at hselection
  | initializerFailure dispatched hstart checked hchecked =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, hout] at hselection
  | localFailure dispatched hstart reason =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, hout] at hselection
  | cutoffChosen dispatched hstart ledger hinitial hledger hvalid hclock hpending hnone arm =>
      have hchosen : ReferenceCollectionPhaseHistory.cutoffChosen x = true := by
        simp [ReferenceCollectionPhaseHistory.cutoffChosen,
          ReferenceActivePhysicalStep.prepare, hdispatch, hout]
      rw [hchosen] at hnoCut
      cases hnoCut
  | continuingChosen dispatched hstart continuation arm =>
      have hselectionAt :
          ReferenceActivePhysicalStep.selectionAt x r.payload dispatched.startResult x.time
            (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights arm =
              some selected := by
        simpa [ReferenceActivePhysicalStep.DispatchCut.selection, hout] using hselection
      have hresult : continuation.startRoundResult = dispatched.startResult := by
        unfold CoordinatorRoundDispatch.dispatchLive at hout
        dsimp only at hout
        repeat' (first | split at hout <;> try cases hout)
        case h_3 =>
          rename_i actualDispatched hdispatch' hinitialization
          by_cases hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
              liveInput.registers actualDispatched.startResult
          · simp only [dite_eq_left hframe] at hout
            by_cases hpayload : liveInput.registers.priorClock.sigma =
                some liveInput.registers.payload.sigma
            · simp only [dite_eq_left hpayload] at hout
              by_cases hgrid : liveInput.registers.gridBoundary = liveInput.registers.priorClock.g
              · simp only [dite_eq_left hgrid] at hout
                by_cases hscore : liveInput.registers.scoreDomainValid
                · simp only [dite_eq_left hscore] at hout
                  by_cases hqueue : liveInput.ownedRegisters.queueDomainValid
                  · simp only [dite_eq_left hqueue] at hout
                    by_cases hprevious : liveInput.ownedRegisters.previousServiceDomainValid
                    · simp only [dite_eq_left hprevious] at hout
                      by_cases hbase : ∀ i, liveInput.followerBaseScore i ≤ p.T * D p
                      · simp only [dite_eq_left hbase] at hout
                        by_cases hlive : CoordinatorLocalArmChoice.assignmentIsLive
                            liveInput.registers.payload
                            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                              actualDispatched.startResult.clock.u) liveInput.registers.time
                        · simp only [dite_eq_left hlive] at hout
                          by_cases hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                              liveInput.registers.payload
                              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                actualDispatched.startResult.clock.u)
                              liveInput.registers.time liveInput.registers.complementWeights
                          · simp only [dite_eq_left hchoice] at hout
                            by_cases hboundary : actualDispatched.startResult.clock.g ≤ p.T + 1
                            · simp only [dite_eq_left hboundary] at hout
                              by_cases henvelope : liveInput.registers.complementEnvelopeValid
                              · simp only [dite_eq_left henvelope] at hout
                                have hnonempty :=
                                  CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                                    liveInput.registers.payload actualDispatched.startResult.pending
                                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                      actualDispatched.startResult.clock.u)
                                    liveInput.registers.time liveInput.registers.complementWeights
                                    liveInput.row hchoice
                                split at hout
                                · rename_i hselected
                                  exact False.elim (hnonempty hselected)
                                · have hp := congrArg (fun output =>
                                    match output with
                                    | .continuingChosen d _ c _ =>
                                        some (d.startResult, c.startRoundResult)
                                    | _ => none) hout
                                  have hp' := by simpa using hp
                                  rcases hp' with ⟨hfirst, hsecond⟩
                                  exact hsecond.symm.trans hfirst
                              · simp only [dite_eq_right henvelope] at hout
                                cases hout
                            · simp only [dite_eq_right hboundary] at hout
                              cases hout
                          · simp only [dite_eq_right hchoice] at hout
                            cases hout
                        · simp only [dite_eq_right hlive] at hout
                          cases hout
                      · simp only [dite_eq_right hbase] at hout
                        cases hout
                    · simp only [dite_eq_right hprevious] at hout
                      cases hout
                  · simp only [dite_eq_right hqueue] at hout
                    cases hout
                · simp only [dite_eq_right hscore] at hout
                  cases hout
              · simp only [dite_eq_right hgrid] at hout
                cases hout
            · simp only [dite_eq_right hpayload] at hout
              cases hout
          · simp only [dite_eq_right hframe] at hout
            cases hout
        case h_1 =>
          rename_i actualDispatched hdispatch' ledger hinitialization hchoice hboundary
            henvelope hselected
          have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
            liveInput.registers.payload actualDispatched.startResult.pending
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
              actualDispatched.startResult.clock.u)
            liveInput.registers.time liveInput.registers.complementWeights liveInput.row hchoice
          exact False.elim (hnonempty hselected)
      have hclock : dispatched.startResult.clock = r.priorClock := by
        calc
          dispatched.startResult.clock = continuation.startRoundResult.clock :=
            congrArg CoordinatorPhaseClock.StartRoundResult.clock hresult.symm
          _ = r.priorClock := by
            simpa [liveInput, ReferenceActivePhysicalStep.liveInput,
              ReferenceActivePhysicalStep.liveRegistersAt] using continuation.clockFrame.1
      have hstartU : dispatched.startResult.clock.u = none := by
        rw [hclock]
        exact hprior
      have hregFields := ReferenceActivePhysicalStep.liveRegistersAt_fields r x.time
      have hregisterWeight :
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights =
            r.complementWeights := by
        unfold CoordinatorLiveChoiceRecorderStep.Registers.complementWeights
        rw [hregFields.2.2.2.2.1]
        rfl
      have hpayload : selected.view.payload = r.payload := by
        simp only [ReferenceActivePhysicalStep.selectionAt] at hselectionAt
        cases hselectionAt
        rfl
      have hcutoff : selected.view.cutoff =
          CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u := by
        simp only [ReferenceActivePhysicalStep.selectionAt] at hselectionAt
        cases hselectionAt
        rfl
      have hweights : HEq selected.view.complementWeights r.complementWeights := by
        simp only [ReferenceActivePhysicalStep.selectionAt] at hselectionAt
        have heq := Option.some.inj hselectionAt
        cases heq
        exact heq_of_eq hregisterWeight
      refine ⟨hpayload, ?_, hweights⟩
      rw [hcutoff, hstartU]
      rfl

/-- If an actual PREPARE has ordinary occupied followers with their actual
accepted whole DOWN records, every replacement current control still has the
same ordinary follower configurations and proposal memories. The proof
reconstructs each successful StartRound, its local queue domain, the actual
no-offer result, and every occupied arm-choice branch. -/
theorem occupied_prepare_at_all_controls
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i,
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
        .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied ∧
      (states i).lastDown = some (payload.downRecord i)) :
    ∀ u : TimeControl p, ∀ i : Fin (p.m - 1),
      ((ReferenceActivePhysicalStep.prepare
        (ReferenceLaterOptionalControlResampling.withControl x u)).followers.followers i).configuration =
          .ordinary (states i) (memories i) := by
  intro u i
  classical
  obtain ⟨before, beforeMemory, _offered, hinput, hstart, _hchoice⟩ :=
    ReferenceActiveDataOwnership.prepare_ordinary_choice i x.row
      (x.state.activations i) x.time (x.active i) (x.state.followers i)
      (states i) (memories i) (hordinary i)
  have hlocal : ActiveFollowerLifecycle.localStateDomainValid before := by
    by_contra hbad
    have hreject := ActiveFollowerLifecycle.interruptionDecision_invalid_domain
      rate.eta x.time before beforeMemory hbad
    simp [ActiveFollowerLifecycle.startRound, hreject] at hstart
  have hdomainBefore : ActiveFollowerQueueOperation.stateInputDomain before := by
    rcases hlocal with ⟨hregs, hbuffer, _⟩
    rcases hregs with ⟨hS, hdelta, hbacklog⟩
    rcases hbuffer with ⟨htimestamps, hkeys, _⟩
    exact ⟨hS, hdelta, hbacklog, htimestamps, hkeys⟩
  have hstartFrame := ActiveFollowerLifecycle.startRound_frame rate.eta x.time
    before (states i) beforeMemory (memories i) hstart
  have hdomainState : ActiveFollowerQueueOperation.stateInputDomain (states i) := by
    rcases hdomainBefore with ⟨hS, hdelta, hbacklog, htimestamps, hkeys⟩
    rcases hstartFrame with ⟨_, hS', hdelta', hbacklog', _, hbuffer', _, _⟩
    change (states i).S ≤ p.T * D p ∧ (states i).delta ≤ D p ∧
      (states i).backlog ≤ p.T * D p ∧
      (∀ record ∈ (states i).buffer, 1 ≤ record.calendarRound ∧
        record.calendarRound ≤ p.T) ∧
      ((states i).buffer.map ActiveFollowerQueueOperation.bufferKey).Nodup
    rw [hS', hdelta', hbacklog', hbuffer']
    exact ⟨hS, hdelta, hbacklog, htimestamps, hkeys⟩
  let y := ReferenceLaterOptionalControlResampling.withControl x u
  have hnotSelectedUp : ¬ (ActiveFollowerQueueOperation.selectedUpRound i y.row
      (x.state.activations i) x.time ∧ (states i).status = .unoccupied) := by
    rintro ⟨_, hu⟩
    exact (hfields i).1 hu
  have hnoOffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i y.row
      (x.state.activations i) x.time (states i) = .noOffer :=
    ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i y.row
      (x.state.activations i) x.time (states i) hdomainState hnotSelectedUp
  have htimeControl : (y.row.2 x.time) = u := by
    dsimp [y]
    rw [ReferenceLaterOptionalControlResampling.withControl_row]
    simp only [Function.update_self]
  have hcore : ActiveFollowerArmChoice.followerArmChoiceCore (states i) u i none ≠ none := by
    rcases hfields i with ⟨hoccupied, hdown⟩
    cases hs : (states i).status with
    | unoccupied => exact (hoccupied hs).elim
    | released =>
        have hsuccess := ActiveFollowerArmChoice.followerArmChoiceCore_occupied_data_or_released
          (states i) u i none (payload.downRecord i) hoccupied hdown (Or.inl hs)
        rw [hsuccess]
        exact Option.some_ne_none _
    | pending =>
        by_cases hfirst : slotDraw u.1 = upSlot ∧
          selectedFollowerDraw p.two_le_m p.m_lt_K u.1 = i ∧
          (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1).val
            (coordinator p.two_le_m) =
              ActiveFollowerArmChoice.downAuxiliaryArm rate.eta (payload.downRecord i)
        · have hsuccess :=
            ActiveFollowerArmChoice.followerArmChoiceCore_pending_selected_up_escape
              (states i) u i none (payload.downRecord i) hs hdown
              hfirst.1 hfirst.2.1 hfirst.2.2
          rw [hsuccess]
          exact Option.some_ne_none _
        · by_cases hcollision :
            (slotDraw u.1 = downSlot ∧
              PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i) =
                (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1).val
                  (followerPlayer p.two_le_m
                    (selectedFollowerDraw p.two_le_m p.m_lt_K u.1))) ∨
            (slotDraw u.1 = upSlot ∧
              PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i) =
                (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1).val
                  (coordinator p.two_le_m))
          · have hsuccess :=
              ActiveFollowerArmChoice.followerArmChoiceCore_pending_collision_escape
                (states i) u i none (payload.downRecord i) hs hdown hcollision
            rw [hsuccess]
            exact Option.some_ne_none _
          · by_cases hdata : slotDraw u.1 = dataSlot
            · have hsuccess :=
                ActiveFollowerArmChoice.followerArmChoiceCore_occupied_data_or_released
                  (states i) u i none (payload.downRecord i) hoccupied hdown (Or.inr hdata)
              rw [hsuccess]
              exact Option.some_ne_none _
            · have hsuccess := ActiveFollowerArmChoice.followerArmChoiceCore_pending_own_arm
                (states i) u i none (payload.downRecord i) hs hdown hdata hfirst hcollision
              rw [hsuccess]
              exact Option.some_ne_none _
  obtain ⟨arm, harm⟩ := Option.ne_none_iff_exists.mp hcore
  have hcoreEq : ActiveFollowerArmChoice.followerArmChoice (states i) y.row x.time i none =
      some arm := by
    simpa only [ActiveFollowerArmChoice.followerArmChoice, htimeControl] using harm.symm
  change (DeclaredFollowerLocalRound.prepare rate i y.row (x.state.activations i)
      x.time (x.active i) (y.state.followers i)).configuration =
    .ordinary (states i) (memories i)
  rw [ReferenceLaterOptionalControlResampling.withControl_state, hinput]
  simp [DeclaredFollowerLocalRound.prepare, hstart, hnoOffer, hcoreEq]

/-- The retained incoming boundary's actual first-live PREPARE has one fixed
set of occupied ordinary follower configurations for every replacement of
the current whole control. The boundary, source, seed, and run are all
computed from the retained source stratum; only the three actual branch
selectors are supplied. -/
theorem retained_first_live_occupied_prepare_all_controls
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t s hs control0)
    (hn : t.val - s <
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run
          (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
            rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2)
          (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1).1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p
            (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1)) rewards s
          (t.val - s + 1) (by omega)
          ((ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
            rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1)).records).length)
    (selected0 : Selection
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run
          (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
            rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2)
          (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1).1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p
            (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1)) rewards s
          (t.val - s + 1) (by omega)
          ((ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
            rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1)).records)[t.val - s].input)
    (hselected : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run
          (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
            rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2)
          (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1).1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p
            (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1)) rewards s
          (t.val - s + 1) (by omega)
          ((ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
            rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1)).records)[t.val - s].output.preparation.coordinator.selection =
      some selected0)
    (hempty : selected0.view.pendingAtChoice = ∅) :
    let source0 := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
    let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0 x
    let generated := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1
    let E := ReferenceActivePhysicalHorizon.run generated source0.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s
      (t.val - s + 1) (by omega) hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∃ r owned base,
      beta = W[t.val - s].input ∧
      W[t.val - s].input.state.coordinator = .live r owned base ∧
      r.time.val + 1 = W[t.val - s].input.time.val ∧
      r.priorClock.u = none ∧ r.pendingAtChoice = ∅ ∧
      ReferenceCollectionPhaseHistory.cutoffChosen W[t.val - s].input = false ∧
      CoordinatorLocalArmChoice.assignmentIsLive selected0.view.payload
        selected0.view.cutoff W[t.val - s].input.time ∧
      CoordinatorLocalArmChoice.ChoiceInputsValid selected0.view.payload
        selected0.view.cutoff W[t.val - s].input.time selected0.view.complementWeights ∧
      selected0.view.payload = r.payload ∧ selected0.view.cutoff = none ∧
      HEq selected0.view.complementWeights r.complementWeights ∧
      ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
        (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
        (∀ (i : Fin (p.m - 1)),
          (W[t.val - s].output.preparation.followers.followers i).configuration =
            .ordinary (states i) (memories i)) ∧
        (∀ (i : Fin (p.m - 1)), (states i).status ≠ .unoccupied ∧
          (states i).lastDown = some (selected0.view.payload.downRecord i)) ∧
        (∀ u : TimeControl p, ∀ (i : Fin (p.m - 1)),
          ((ReferenceActivePhysicalStep.prepare
            (ReferenceLaterOptionalControlResampling.withControl beta u)).followers.followers i).configuration =
            .ordinary (states i) (memories i)) ∧
        (∀ (i : Fin (p.m - 1)),
          i ∈ ReferencePhysicalReleaseQuota.pendingAtStart
            selected0.view.payload beta.time beta.state ↔
              (states i).status = .pending) ∧
        ReferenceReleaseStrictPastFactor.phaseFactor rate rewards C_star C_h q t s hs
          control0 x ⟨t.val - s, Nat.lt_succ_self _⟩ =
            ReferenceActivePhysicalStepMeasurability.encodeState beta.state := by
  let source0 := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  let generated := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2
  let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1
  let count := t.val - s + 1
  let hspan : s + count ≤ p.T := by dsimp [count]; omega
  let E := ReferenceActivePhysicalHorizon.run generated source0.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s count hspan hmode
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 x
  let k : Fin W.length := ⟨t.val - s, hn⟩
  have hsourceFacts := ReferenceRetainedBoundaryMeasurability.retainedLaunchStart_source_facts
    rate rewards C_star C_h q t s hs control0 x.1 x.2.1 x.2.2
  have hsourceSelected : ActualInitializationPhysicalStep.selectedRowIndex p source0 = q := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t control0 x.1 x.2.1
  have hseedSpec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2
  obtain ⟨initial, sourceSeed, sourceMemory, hinitialMode, hlaunch, hfirst,
      hseedInitial, hS, hdelta, hbacklog, hnone, haccepted, hunoccupied,
      hbuffer, hpair, htime, hbatch, hsourceProofs⟩ :=
    ReferenceFirstLiveReleaseGeometry.original_source_first_live_release_projection
      source0 rewards C_star C_h hsourceFacts.1 s count hsourceFacts.2 hspan
  have hgeneratedInitial : generated = initial := by
    apply Option.some.inj
    exact hseedSpec.1.symm.trans hlaunch
  subst initial
  rcases hsourceProofs with ⟨hselectors, _hterminal⟩
  obtain ⟨hsourceValid, states, memories, hprepared, hfields, _hchoiceData⟩ :=
    hselectors k selected0 hselected hempty
  obtain ⟨r, owned, base, hstate, htimeNext, hprior, hpending, hnoCut,
      hassignment, hvalid⟩ :=
    ReferenceFirstLiveReleaseGeometry.first_live_actual_choice_data
      generated source0.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source0)
        rewards s count hspan hmode hfirst k selected0 hselected hempty
  have hselectedPrep :
      (ReferenceActivePhysicalStep.prepare W[t.val - s].input).coordinator.selection =
        some selected0 := by
    have h := hselected
    rw [W[t.val - s].output_eq] at h
    exact h
  obtain ⟨hpayload, hcutoff, hweights⟩ :=
    selected_live_payload_cutoff_weights W[k.val].input r owned base hstate hprior hnoCut
      selected0 hselectedPrep hempty
  have hrecordsAppend : E.records =
      (ReferenceActivePhysicalHorizon.run generated source0.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s
        (t.val - s) (by omega) hmode).records ++
        [ReferenceActivePhysicalHorizon.RoundRecord.mk
          (ReferenceActivePhysicalHorizon.roundInputAt generated source0.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s hmode
            (ReferenceActivePhysicalHorizon.run generated source0.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s
              (t.val - s) (by omega) hmode)
            ⟨s + (t.val - s), by omega, by omega⟩)
            (ReferenceActivePhysicalStep.step
            (ReferenceActivePhysicalHorizon.roundInputAt generated source0.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s hmode
              (ReferenceActivePhysicalHorizon.run generated source0.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s
                (t.val - s) (by omega) hmode)
              ⟨s + (t.val - s), by omega, by omega⟩)) rfl] := by
    dsimp [E, count]
    rw [ReferenceActivePhysicalHorizon.run_successor_step]
    exact (ReferenceActivePhysicalHorizon.foldRound_equations generated source0.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s
      hmode _ ⟨s + (t.val - s), by omega, by omega⟩).2
  have hwindowPrefix : W.IsPrefix E.records := by
    simp only [W, ReferenceFirstLiveConfirmationHistory.firstLiveWindow]
    exact List.takeWhile_prefix _
  have hnE : t.val - s < E.records.length :=
    lt_of_lt_of_le hn hwindowPrefix.length_le
  have hprefixLength := ReferenceActivePhysicalHorizon.run_record_count generated
    source0.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s
      (t.val - s) (by omega) hmode
  have hlastRecord : E.records[t.val - s]'hnE =
      ReferenceActivePhysicalHorizon.RoundRecord.mk
        (ReferenceActivePhysicalHorizon.roundInputAt generated source0.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s hmode
          (ReferenceActivePhysicalHorizon.run generated source0.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s
            (t.val - s) (by omega) hmode)
          ⟨s + (t.val - s), by omega, by omega⟩)
        (ReferenceActivePhysicalStep.step
          (ReferenceActivePhysicalHorizon.roundInputAt generated source0.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s hmode
            (ReferenceActivePhysicalHorizon.run generated source0.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s
              (t.val - s) (by omega) hmode)
            ⟨s + (t.val - s), by omega, by omega⟩)) rfl := by
    exact List.getElem_of_append hrecordsAppend hprefixLength
  have hwindowRecord : W[t.val - s]'hn = E.records[t.val - s]'hnE := by
    exact hwindowPrefix.getElem hn
  have hsourceInputEq :
      ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
        rate rewards C_star C_h q t s hs control0 x control0 =
      ReferenceActivePhysicalHorizon.roundInputAt generated source0.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s hmode
        (ReferenceActivePhysicalHorizon.run generated source0.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s
          (t.val - s) (by omega) hmode)
        ⟨s + (t.val - s), by omega, by omega⟩ := by
    dsimp [ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput,
      source0, generated, hmode, count]
    change ReferenceActivePhysicalHorizon.roundInputAt generated source0.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s hmode
      (ReferenceActivePhysicalHorizon.run generated source0.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s
        (t.val - s) (by omega) hmode)
      ⟨t.val, by omega, by omega⟩ =
      ReferenceActivePhysicalHorizon.roundInputAt generated source0.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s hmode
        (ReferenceActivePhysicalHorizon.run generated source0.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s
          (t.val - s) (by omega) hmode)
        ⟨s + (t.val - s), by omega, by omega⟩
    congr 1
    apply Subtype.ext
    simp [Nat.add_sub_of_le hs]
  have hretainedInput :=
    ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_roundInputAtSource
      rate rewards C_star C_h q t s hs control0 x control0
  have hsourceAt : ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate beta source0 = beta := by
    dsimp [beta, ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary,
      ReferenceFixedTimeSourceControlCoupling.roundInputAtSource,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex]
    rfl
  have hbetaRecord : beta = W[k.val].input := by
    calc
      beta = ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
          rate rewards C_star C_h q t s hs control0 x control0 :=
        hsourceAt.symm.trans hretainedInput.symm
      _ = (E.records[t.val - s]'hnE).input := by rw [hsourceInputEq, hlastRecord]
      _ = (W[t.val - s]'hn).input := by rw [hwindowRecord]
  have hphaseWitness := retained_phaseFactor_current_eq_boundary_state
    rewards C_star C_h q t s hs control0 x
  have hordinaryBeta : ∀ (i : Fin (p.m - 1)),
      ((ReferenceActivePhysicalStep.prepare beta).followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
    intro i
    rw [hbetaRecord]
    have h := hprepared i
    rw [W[k.val].output_eq] at h
    simpa only [ReferenceActivePhysicalStep.step] using h
  have hallControls := occupied_prepare_at_all_controls beta selected0.view.payload
    states memories hordinaryBeta hfields
  have hstateBeta : beta.state.coordinator = .live r owned base := by
    rw [hbetaRecord]
    exact hstate
  refine ⟨r, owned, base, hbetaRecord, ?_, htimeNext, hprior, hpending, hnoCut,
    hassignment, hvalid, hpayload, hcutoff, hweights, states, memories,
    hprepared, hfields, ?_, ?_, hphaseWitness⟩
  · simpa only [hbetaRecord] using hstate
  · intro u i
    exact hallControls u i
  · intro i
    have hchoice := hordinaryBeta i
    exact ReferencePhysicalReleaseQuota.pendingAtStart_ordinary_prepare
      selected0.view.payload beta r owned base hstateBeta
      hpayload.symm hpending i (states i) (memories i) hchoice

theorem source_first_live_record_time
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count : ℕ) (hspan : s + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ k : Fin W.length, s + k.val = W[k.val].input.time.val := by
  intro E W k
  have hwindowPrefix : W.IsPrefix E.records := List.takeWhile_prefix _
  have hkRecord : k.val < E.records.length := lt_of_lt_of_le k.isLt hwindowPrefix.length_le
  have hwindowRecord : W[k.val]'k.isLt = E.records[k.val]'hkRecord :=
    hwindowPrefix.getElem k.isLt
  have htimes := ReferenceActivePhysicalHorizon.run_time_values initial rows J rewards s count hspan hmode
  have hkCalendar : k.val < (ReferenceActivePhysicalHorizon.calendar s count).length := by
    rw [← htimes]
    simpa only [List.length_map] using hkRecord
  have hkRange : k.val < count := by
    simpa [ReferenceActivePhysicalHorizon.calendar] using hkCalendar
  have hcalendar : (ReferenceActivePhysicalHorizon.calendar s count)[k.val]? =
      some (s + k.val) := by
    simpa [ReferenceActivePhysicalHorizon.calendar, Nat.one_mul] using
      (List.getElem?_range' (s := s) (step := 1) (i := k.val) (n := count) hkRange)
  have htime? := congrArg (fun times : List ℕ => times[k.val]?) htimes
  have hmapElem : (E.records.map (fun record => record.input.time.val))[k.val]? =
      some (E.records[k.val].input.time.val) := by
    simp [List.getElem?_map, List.getElem?_eq_getElem hkRecord]
  rw [hmapElem, hcalendar] at htime?
  have hvalue : E.records[k.val].input.time.val = s + k.val := by
    exact Option.some.inj htime?
  rw [← hwindowRecord] at hvalue
  exact hvalue.symm

private theorem run_records_eq_of_source_data
    (initial initial' : ReferenceActivePhysicalHorizon.State p rate)
    (rows rows' : CompletePublicTable.CompleteRows p)
    (J J' : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count : ℕ) (hspan : s + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (hmode' : ReferenceActivePhysicalHorizon.allActiveAtStart initial' s)
    (hinitial : initial = initial') (hrows : rows = rows') (hJ : J = J') :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hmode).records =
      (ReferenceActivePhysicalHorizon.run initial' rows' J' rewards s count hspan hmode').records := by
  subst initial'
  subst rows'
  subst J'
  rfl

private theorem run_records_eq_of_count_eq
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count count' : ℕ) (hcount : count = count')
    (hspan : s + count ≤ p.T) (hspan' : s + count' ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s)
    (hmode' : ReferenceActivePhysicalHorizon.allActiveAtStart initial s) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hmode).records =
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s count' hspan' hmode').records := by
  cases hcount
  rfl

private theorem run_eq_of_count_eq
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count count' : ℕ) (hcount : count = count')
    (hspan : s + count ≤ p.T) (hspan' : s + count' ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s) :
    ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hmode =
      ReferenceActivePhysicalHorizon.run initial rows J rewards s count' hspan' hmode := by
  cases hcount
  rfl

private theorem original_source_record_eq_retained_boundary
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) :
    let launchData := ReferenceCorrectedInitializationLaunch.correctedLaunch_all_active_at_start
      rate source rewards C_star C_h hc
    let initial := Classical.choose launchData
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
      rw [← helapsed]
      exact (Classical.choose_spec launchData).2
    let E := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ k : Fin W.length,
      let q := ActualInitializationPhysicalStep.selectedRowIndex p source
      let t : Fin p.T := W[k.val].input.time
      let hs : s ≤ t.val := by
        have ht := source_first_live_record_time initial source.1.2 q rewards s count hspan hmode k
        change s + k.val = t.val at ht
        omega
      let control0 := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).1
      let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
        rate rewards C_star C_h q t s hs control0 source (by rfl) hc helapsed
      ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x = W[k.val].input := by
  intro launchData initial hmode E W k
  classical
  let q := ActualInitializationPhysicalStep.selectedRowIndex p source
  have hchosenLaunch :
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
        some initial := (Classical.choose_spec launchData).1
  have hwindowPrefix : W.IsPrefix E.records := List.takeWhile_prefix _
  have hkRecord : k.val < E.records.length := lt_of_lt_of_le k.isLt hwindowPrefix.length_le
  have hwindowRecord : W[k.val]'k.isLt = E.records[k.val]'hkRecord :=
    hwindowPrefix.getElem k.isLt
  have htimeEq : s + k.val = W[k.val].input.time.val :=
    source_first_live_record_time initial source.1.2 q rewards s count hspan hmode k
  let t : Fin p.T := W[k.val].input.time
  let control0 := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).1
  have hs : s ≤ t.val := by rw [← htimeEq]; omega
  have hrecords := ReferenceActivePhysicalHorizon.run_record_count initial source.1.2 q
    rewards s count hspan hmode
  have hkCount : k.val < count := by
    rw [← hrecords]
    exact hkRecord
  have hkPlusCount : k.val + 1 ≤ count := by omega
  let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
    rate rewards C_star C_h q t s hs control0 source (by rfl) hc helapsed
  let source0 := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  let seedPre := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2
  let seed0 := seedPre
  let mode0 := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1
  have hxval : (x : ReferenceRetainedBoundaryMeasurability.Remainder p q t) =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2 := by
    exact ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_val
      rate rewards C_star C_h q t s hs control0 source
      (by rfl) hc helapsed
  have hsource0 : source0 = source := by
    dsimp [source0, ReferenceGeneratedActivePrefixFactor.splitSource]
    rw [hxval]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_reconstruct p q t source
  have hselectedSplit :
      ActualInitializationPhysicalStep.selectedRowIndex p source0 = q := by
    rw [hsource0]
  have hseedLaunch := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).1
  have hseedLaunch' : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards
      C_star C_h = some seedPre := by
    calc
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
          ReferenceCorrectedInitializationLaunch.correctedLaunch rate source0 rewards C_star C_h := by
        rw [hsource0]
      _ = some seedPre := by simpa only [source0, seedPre] using hseedLaunch
  have hseedEq : seedPre = initial := by
    apply Option.some.inj
    exact hseedLaunch'.symm.trans hchosenLaunch
  let Eshort := ReferenceActivePhysicalHorizon.run seed0 source0.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s k.val
    (by omega) mode0
  let Eplus := ReferenceActivePhysicalHorizon.run seed0 source0.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s (k.val + 1)
    (by omega) mode0
  let shortInput := ReferenceActivePhysicalHorizon.roundInputAt seed0 source0.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s mode0 Eshort
    ⟨s + k.val, by constructor <;> omega⟩
  let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 x
  have htk : t.val - s = k.val := by omega
  have hretainedInput :=
    ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_roundInputAtSource
      rate rewards C_star C_h q t s hs control0 x control0
  have hsourceAt : ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate beta source0 = beta := by
    dsimp [beta, ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary,
      ReferenceFixedTimeSourceControlCoupling.roundInputAtSource,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex]
    rfl
  have hretainedBeta :
      ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
        rate rewards C_star C_h q t s hs control0 x control0 = beta := by
    calc
      _ = ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate beta source0 := by
        rw [hretainedInput]
      _ = beta := hsourceAt
  have hsourceInputEq :
      ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
        rate rewards C_star C_h q t s hs control0 x control0 = shortInput := by
    have hrun : ReferenceActivePhysicalHorizon.run seed0 source0.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s
        (t.val - s) (by omega) mode0 = Eshort := by
      dsimp [Eshort]
      exact run_eq_of_count_eq seed0 source0.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s
        (t.val - s) k.val htk (by omega) (by omega) mode0
    have hentry : (⟨t.val, by constructor <;> omega⟩ : ReferenceActivePhysicalHorizon.CalendarEntry p s) =
        ⟨s + k.val, by constructor <;> omega⟩ := by
      apply Subtype.ext
      exact htimeEq.symm
    dsimp [ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput,
      source0, seed0, Eshort, shortInput]
    rw [hrun]
    rw [hentry]
  have hbetaShort : beta = shortInput := hretainedBeta.symm.trans hsourceInputEq
  have hplusAppend : Eplus.records = Eshort.records ++
      [ReferenceActivePhysicalHorizon.RoundRecord.mk shortInput
        (ReferenceActivePhysicalStep.step shortInput) rfl] := by
    dsimp [Eplus, Eshort]
    rw [ReferenceActivePhysicalHorizon.run_successor_step]
    exact (ReferenceActivePhysicalHorizon.foldRound_equations seed0 source0.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source0) rewards s mode0 _
      ⟨s + k.val, by constructor <;> omega⟩).2
  have hkShort : Eshort.records.length = k.val := by
    dsimp [Eshort]
    rw [ReferenceActivePhysicalHorizon.run_record_count]
  have hkPlus : k.val < Eplus.records.length := by
    dsimp [Eplus]
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    omega
  have hshortRecord : Eplus.records[k.val]'hkPlus =
      ReferenceActivePhysicalHorizon.RoundRecord.mk shortInput
        (ReferenceActivePhysicalStep.step shortInput) rfl := by
    exact List.getElem_of_append hplusAppend hkShort
  have hfullPrefix : Eplus.records <+: E.records := by
    obtain ⟨suffix, hsuffix⟩ :=
      ReferenceCollectionPhaseHistory.run_records_prefix initial source.1.2 q rewards s
        (k.val + 1) (count - (k.val + 1)) (by omega) hmode
    refine ⟨suffix, ?_⟩
    dsimp [E]
    have hcount : (k.val + 1) + (count - (k.val + 1)) = count := by
      omega
    have hsourceRows : source0.1.2 = source.1.2 :=
      congrArg (fun original : SourceInput p => original.1.2) hsource0
    have hplusActual := run_records_eq_of_source_data seed0 initial source0.1.2 source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source0) q rewards s (k.val + 1)
      (by omega) mode0 hmode hseedEq hsourceRows hselectedSplit
    have hcountRun := run_records_eq_of_count_eq initial source.1.2 q rewards s
      (k.val + 1 + (count - (k.val + 1))) count hcount (by omega) hspan hmode hmode
    calc
      _ = (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s
        (k.val + 1) (by omega) hmode).records ++ suffix := by rw [← hplusActual]
      _ = (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s
        (k.val + 1 + (count - (k.val + 1))) (by omega) hmode).records := hsuffix.symm
      _ = E.records := by
        dsimp [E]
        exact hcountRun
  have hfullRecord : Eplus.records[k.val]'hkPlus = E.records[k.val]'hkRecord :=
    hfullPrefix.getElem hkPlus
  have hbetaRecord : beta = W[k.val].input := by
    calc
      beta = shortInput := hbetaShort
      _ = (Eplus.records[k.val]'hkPlus).input := by rw [hshortRecord]
      _ = (E.records[k.val]'hkRecord).input := by rw [hfullRecord]
      _ = W[k.val].input := by rw [hwindowRecord]
  exact hbetaRecord

private theorem original_source_phaseFactor_current_eq_boundary_state
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s) :
    let q := ActualInitializationPhysicalStep.selectedRowIndex p source
    let control0 := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).1
    let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs control0 source (by rfl) hc helapsed
    ReferenceReleaseStrictPastFactor.phaseFactor rate rewards C_star C_h q t s hs
      control0 x ⟨t.val - s, Nat.lt_succ_self _⟩ =
      ReferenceActivePhysicalStepMeasurability.encodeState
        (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
          rate rewards C_star C_h q t s hs control0 x).state := by
  intro q control0 x
  have hphase := ReferenceReleaseStrictPastFactor.phaseFactor_source_specialization
    rate rewards C_star C_h q t s hs control0 source (by rfl) hc helapsed
  have hsourcePrefix := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_on_source
    rate rewards C_star C_h q t source (by rfl) s (t.val - s) hs (by omega) hc helapsed
  have hphaseAt := hphase ⟨t.val - s, Nat.lt_succ_self _⟩
  have hstate := hsourcePrefix.1
  have hencoded := congrArg ReferenceActivePhysicalStepMeasurability.encodeState hstate
  refine hphaseAt.trans ?_
  simpa only [x, control0,
    ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_state,
    ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_val] using hencoded.symm

/-- Original-source specialization at an arbitrary actual first-live record.
The row index, physical time, baseline control, retained remainder, launch
state, and run are all computed from the original private source. The record
is the same record in the full source run and in the retained prefix. -/
theorem original_source_first_live_occupied_prepare_all_controls
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) :
    let launchData := ReferenceCorrectedInitializationLaunch.correctedLaunch_all_active_at_start
      rate source rewards C_star C_h hc
    let initial := Classical.choose launchData
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
      rw [← helapsed]
      exact (Classical.choose_spec launchData).2
    let E := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ (k : Fin W.length) (selected : Selection W[k.val].input),
      W[k.val].output.preparation.coordinator.selection = some selected →
      selected.view.pendingAtChoice = ∅ →
      let q := ActualInitializationPhysicalStep.selectedRowIndex p source
      let t : Fin p.T := W[k.val].input.time
      let htime := source_first_live_record_time initial source.1.2 q rewards s count hspan hmode k
      let hs : s ≤ t.val := by rw [← htime]; omega
      let htk : t.val - s = k.val := by
        have htime := source_first_live_record_time initial source.1.2 q rewards s count hspan hmode k
        change s + k.val = t.val at htime
        omega
      let control0 := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).1
      let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
        rate rewards C_star C_h q t s (by
          exact hs) control0 source (by rfl) hc helapsed
      let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x
      s + k.val = t.val ∧
      ∃ r owned base,
        beta = W[k.val].input ∧
        W[k.val].input.state.coordinator = .live r owned base ∧
        r.time.val + 1 = W[k.val].input.time.val ∧
        r.priorClock.u = none ∧ r.pendingAtChoice = ∅ ∧
        ReferenceCollectionPhaseHistory.cutoffChosen W[k.val].input = false ∧
        CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
          selected.view.cutoff W[k.val].input.time ∧
        CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
          selected.view.cutoff W[k.val].input.time selected.view.complementWeights ∧
        selected.view.payload = r.payload ∧ selected.view.cutoff = none ∧
        HEq selected.view.complementWeights r.complementWeights ∧
        ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
          (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
          (∀ i, (W[k.val].output.preparation.followers.followers i).configuration =
            .ordinary (states i) (memories i)) ∧
          (∀ i, (states i).status ≠ .unoccupied ∧
            (states i).lastDown = some (selected.view.payload.downRecord i)) ∧
          (∀ u : TimeControl p, ∀ i,
            ((ReferenceActivePhysicalStep.prepare
              (ReferenceLaterOptionalControlResampling.withControl beta u)).followers.followers i).configuration =
                .ordinary (states i) (memories i)) ∧
          (∀ i, i ∈ ReferencePhysicalReleaseQuota.pendingAtStart
            selected.view.payload beta.time beta.state ↔ (states i).status = .pending) ∧
          ReferenceReleaseStrictPastFactor.phaseFactor rate rewards C_star C_h q t s
            hs control0 x ⟨k.val, by rw [htk]; exact Nat.lt_succ_self _⟩ =
              ReferenceActivePhysicalStepMeasurability.encodeState beta.state := by
  intro launchData initial hmode E W k selected hselected hempty
  classical
  let q := ActualInitializationPhysicalStep.selectedRowIndex p source
  have hprojection :=
    ReferenceFirstLiveReleaseGeometry.original_source_first_live_release_projection
      source rewards C_star C_h hc s count helapsed hspan
  obtain ⟨projectedInitial, seed, memory, projectedMode, hlaunch, hfirst,
      hseed, hS, hdelta, hbacklog, hnone, haccepted, hunoccupied, hbuffer,
      hpair, htimeSource, hbatch, hsourceProofs⟩ := hprojection
  have hchosenLaunch :
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
        some initial := (Classical.choose_spec launchData).1
  have hprojectedInitial : projectedInitial = initial :=
    Option.some.inj (hlaunch.symm.trans hchosenLaunch)
  subst projectedInitial
  rcases hsourceProofs with ⟨hselectors, hterminal⟩
  have hfirstActual : initial.coordinator = .first := hfirst
  obtain ⟨hvalid, states, memories, hprepared, hfields, _hchoiceData⟩ :=
    hselectors k selected hselected hempty
  have hpreparedActual : ∀ i,
      (W[k.val].output.preparation.followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
    intro i
    exact hprepared i
  have hfieldsActual : ∀ i, (states i).status ≠ .unoccupied ∧
      (states i).lastDown = some (selected.view.payload.downRecord i) := by
    intro i
    exact hfields i
  have htimeEq : s + k.val = W[k.val].input.time.val :=
    source_first_live_record_time initial source.1.2 q rewards s count hspan hmode k
  let t : Fin p.T := W[k.val].input.time
  let control0 := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).1
  have hs : s ≤ t.val := by rw [← htimeEq]; omega
  have htk : t.val - s = k.val := by omega
  let x := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
    rate rewards C_star C_h q t s hs control0 source (by rfl) hc helapsed
  let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 x
  have hbetaRecord : beta = W[k.val].input :=
    original_source_record_eq_retained_boundary source rewards C_star C_h hc s count
      helapsed hspan k
  obtain ⟨r, owned, base, hstate, htimeNext, hprior, hpending, hnoCut,
      hassignment, hvalidActual⟩ :=
    ReferenceFirstLiveReleaseGeometry.first_live_actual_choice_data
      initial source.1.2 q rewards s count hspan hmode hfirstActual k selected hselected hempty
  have hselectedPrep :
      (ReferenceActivePhysicalStep.prepare W[k.val].input).coordinator.selection = some selected := by
    have h := hselected
    rw [W[k.val].output_eq] at h
    exact h
  obtain ⟨hpayload, hcutoff, hweights⟩ :=
    selected_live_payload_cutoff_weights W[k.val].input r owned base hstate hprior hnoCut
      selected hselectedPrep hempty
  have hallControls := occupied_prepare_at_all_controls beta selected.view.payload
    states memories (by
      intro i
      rw [hbetaRecord]
      have houtputFollower := congrArg
        (fun output => (output.preparation.followers.followers i).configuration) W[k.val].output_eq
      calc
        _ = ((ReferenceActivePhysicalStep.step W[k.val].input).preparation.followers.followers i).configuration := rfl
        _ = (W[k.val].output.preparation.followers.followers i).configuration := houtputFollower.symm
        _ = .ordinary (states i) (memories i) := hpreparedActual i) hfieldsActual
  have hstateBeta : beta.state.coordinator = .live r owned base := by
    rw [hbetaRecord]
    exact hstate
  have hphaseAt := original_source_phaseFactor_current_eq_boundary_state
    source rewards C_star C_h t s hs hc helapsed
  have hcurrentIndex : (⟨t.val - s, Nat.lt_succ_self _⟩ : Fin (t.val - s + 1)) =
      ⟨k.val, by rw [htk]; exact Nat.lt_succ_self _⟩ := Fin.ext htk
  rw [hcurrentIndex] at hphaseAt
  refine ⟨htimeEq, r, owned, base, hbetaRecord, ?_, htimeNext, hprior,
    hpending, hnoCut, hassignment, hvalidActual, hpayload, hcutoff, hweights,
    states, memories, hpreparedActual, hfieldsActual, ?_, ?_, ?_⟩
  · exact hstate
  · intro u i
    exact hallControls u i
  · intro i
    have hordinary := hpreparedActual i
    rw [W[k.val].output_eq] at hordinary
    have hordinaryBeta :
        ((ReferenceActivePhysicalStep.prepare beta).followers.followers i).configuration =
          .ordinary (states i) (memories i) := by
      rw [hbetaRecord]
      simpa only [ReferenceActivePhysicalStep.step] using hordinary
    exact ReferencePhysicalReleaseQuota.pendingAtStart_ordinary_prepare
      selected.view.payload beta r owned base hstateBeta hpayload.symm hpending
      i (states i) (memories i) hordinaryBeta
  · exact hphaseAt

/-- At the actual terminal launch endpoint the source run has zero records
and the first-live window has no current action. No `Fin T` sentinel action
is introduced. The same conclusion also holds for every zero-length span. -/
theorem original_source_first_live_terminal
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) :
    let launchData := ReferenceCorrectedInitializationLaunch.correctedLaunch_all_active_at_start
      rate source rewards C_star C_h hc
    let initial := Classical.choose launchData
    let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
      rw [← helapsed]
      exact (Classical.choose_spec launchData).2
    let E := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    (s = p.T ∨ count = 0) →
      count = 0 ∧ E.finalState = initial ∧ E.records = [] ∧ W = [] := by
  intro launchData initial hmode E W hend
  have hcount : count = 0 := by rcases hend with hterminal | hzero <;> omega
  subst count
  have hfinal : E.finalState = initial := ReferenceActivePhysicalHorizon.run_zero_final
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s hspan hmode
  have hrecords : E.records = [] := ReferenceActivePhysicalHorizon.run_zero_records
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s hspan hmode
  refine ⟨rfl, hfinal, hrecords, ?_⟩
  simp only [W, ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hrecords,
    List.takeWhile_nil]

end Bandits.Support.ReferenceFirstLiveOccupiedPreparationControl

end
