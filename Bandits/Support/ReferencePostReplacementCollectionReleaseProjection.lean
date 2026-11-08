/-
Copyright (c) 2026 Bandits Lean formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionReleaseBoundary

/-!
# Actual post-collection release projection

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-70,246-299,431-490`,
`sources/zip4/manuscript/05_binary_transport.tex:180-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:14-64`.

The original complete physical suffix supplies the later installation, its
literal pending-set release suffix, and the all-player deterministic signed
sentinel charge. The raw collection endpoint is retained with all of its
terminal, absent, cutoff, dagger, and empty-suffix alternatives.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveReleaseGeometry
open Bandits.Support.ReferencePhysicalReleaseQuota
open Bandits.Support.ReleaseRoundKernel

namespace Bandits.Support.ReferencePostReplacementCollectionReleaseProjection

variable {p : ConstructorDimensions.Parameters}

private theorem takeWhile_length_le {α : Type} (xs : List α) (pred : α → Bool) :
    (xs.takeWhile pred).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      cases hp : pred head <;> simp [List.takeWhile, hp, ih]

/-- At the exact raw collection endpoint, every actual record in the literal
post-replacement release suffix has the actual common-action projection,
physical UP/DATA flag characterization, and signed one-round sentinel bound.
The source root derives the selected choices, occupied fields, live choice
domain, and physical feedback from the same original run and payload.

The first conjunct retains the complete raw-endpoint case split, including
absent launch/birth/cutoff, terminal horizon, dagger, and empty release cases.
The second conjunct applies to the same `b = c + rawK.length` supplied by that
case split.

Sources: `05_binary_transport.tex:180-348`, `06_interruptions.tex:246-299,431-490`,
and `appendix_a_local_protocol.tex:14-64`.
-/
public theorem raw_collection_release_suffix_projection_and_signed_cost
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z
    ((K = [] ↔ R[v]? = none ∨ ∃ birth payload,
      R[v]? = some birth ∧
      ReferenceFirstReplacementCollectionPendingFoundation.birthPayload birth = some payload ∧
      (R[c]? = none ∨ ∃ cut, R[c]? = some cut ∧
        ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = false)) ∧
    (ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = none →
      K = []) ∧
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T →
      K = []) ∧
    (match R[v]? with
    | none => v = R.length
    | some birth => ∃ payload,
        ReferenceFirstReplacementCollectionPendingFoundation.birthPayload birth = some payload ∧
        c ≤ R.length ∧
        match R[c]? with
        | none => c = R.length ∧ tail = R.drop (v + 1) ∧
            ∀ r ∈ R.drop (v + 1),
              ReferenceFirstReplacementCollectionPendingFoundation.isCutoff r = false
        | some cut =>
          if ReferenceFirstReplacementCollectionPendingFoundation.isCutoff cut = true then
            c + K.length = R.length ∨
            ∃ b : Fin R.length, b.val = c + K.length ∧
              ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true ∧
              ∃ (ledger : ReferenceActivePhysicalStep.Ledger rate)
                (saved : Option (Fin p.T × Bool))
                (rb : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                (qb : CoordinatorLiveServiceFinish.OwnedRegisters rb)
                (beta : Fin (p.m - 1) → ℕ)
                (selected : ReferenceActivePhysicalStep.Selection R[b.val].input),
                R[b.val].input.state.coordinator = .collection payload ledger saved ∧
                ledger.pending = ∅ ∧
                R[b.val].output.next.coordinator = .live rb qb beta ∧
                R[b.val].output.preparation.coordinator.selection = some selected ∧
                selected.view.payload = rb.payload ∧
                let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                  rate rewards C_star C_h z (b.val + 1)
                let V := R[b.val] :: W
                let H := V.takeWhile
                  ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
                let Rel := V.dropWhile
                  ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
                let h := H.length
                H ++ Rel = V ∧
                (Rel = [] ↔ ∀ r ∈ V,
                  ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = true) ∧
                (∀ i (hi : i < Rel.length),
                  ∃ j, ∃ hj : j < W.length, Rel[i]'hi = W[j]'hj ∧
                    ∃ selected : ReferenceActivePhysicalStep.Selection (W[j]'hj).input,
                      (W[j]'hj).output.preparation.coordinator.selection = some selected ∧
                      selected.view.pendingAtChoice = ∅ ∧
                      ∀ follower (choice : ReferencePrelaunchFollower.State p rate.eta)
                        (memory : ActiveFollowerLifecycle.LocalMemory p),
                        (ReferenceFollowerFixedReply.actualChoice (W[j]'hj) follower).configuration =
                          .ordinary choice memory → choice.status ≠ .unoccupied) ∧
                (∀ r ∈ V, ∀ selected : ReferenceActivePhysicalStep.Selection r.input,
                  r.output.preparation.coordinator.selection = some selected →
                  ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected →
                  r ∈ H) ∧
                (∀ j : Fin V.length,
                  ReferencePostReplacementCollectionReleaseBoundary.clearingConfirmation V[j.val] →
                    j.val + 1 = h) ∧
                (Rel = [] ∨ ∃ j : Fin V.length, ∃ hn : j.val + 1 < V.length,
                  j.val = h - 1 ∧ 2 ≤ h ∧
                  ReferencePostReplacementCollectionReleaseBoundary.clearingConfirmation V[j.val] ∧
                  ∃ selected : ReferenceActivePhysicalStep.Selection V[j.val].input,
                    V[j.val].output.preparation.coordinator.selection = some selected ∧
                    selected.view.pendingAtChoice =
                      {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                        (V[j.val].input.row.2 V[j.val].input.time).1} ∧
                    R[b.val + j.val]? = some V[j.val] ∧
                    R[b.val + j.val + 1]? = some (V[j.val + 1]'hn) ∧
                    Rel.head? = some (V[j.val + 1]'hn) ∧
                    (V[j.val + 1]'hn).input.time.val = V[j.val].input.time.val + 1 ∧
                    ∀ i, ∃ (choice nextChoice : ReferencePrelaunchFollower.State p rate.eta)
                      (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p),
                      (ReferenceFollowerFixedReply.actualChoice V[j.val] i).configuration =
                        .ordinary choice memory ∧ choice.status = .pending ∧
                      (ReferenceFollowerFixedReply.actualChoice (V[j.val + 1]'hn) i).configuration =
                        .ordinary nextChoice nextMemory ∧ nextChoice.status = .pending)
          else cut.output.next.coordinator = .dagger ∧
            ∀ r ∈ R.drop (c + 1),
              r.input.state.coordinator = .dagger ∧
              ReferenceFirstReplacementCollectionPendingFoundation.isCutoff r = false)) ∧
      ∀ b : Fin R.length, b.val = c + K.length →
        if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
          let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z (b.val + 1)
          let V := R[b.val] :: W
          let Rel := V.dropWhile
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
          ∀ i (hi : i < Rel.length),
            ∃ j, ∃ hj : j < W.length,
              Rel[i]'hi = W[j]'hj ∧
              ∃ k : Fin R.length, k.val = b.val + 1 + j ∧
              ∃ selected : ReferenceActivePhysicalStep.Selection
                  (R[k.val].input),
                ∃ states : Fin (p.m - 1) →
                  ReferencePrelaunchFollower.State p rate.eta,
                ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
                ∃ input : ActiveRoundActions.RoundInput
                  selected.view.payload.assignment 0,
                  W[j]'hj = R[k.val] ∧
                  R[k.val].output.preparation.coordinator.selection =
                    some selected ∧
                  selected.view.pendingAtChoice = ∅ ∧
                  CoordinatorLocalArmChoice.assignmentIsLive
                    selected.view.payload selected.view.cutoff
                    R[k.val].input.time ∧
                  CoordinatorLocalArmChoice.ChoiceInputsValid
                    selected.view.payload selected.view.cutoff
                    R[k.val].input.time selected.view.complementWeights ∧
                  (∀ follower,
                    (ReferenceFollowerFixedReply.actualChoice
                      R[k.val] follower).configuration =
                        .ordinary (states follower) (memories follower)) ∧
                  (∀ follower, (states follower).status ≠ .unoccupied ∧
                    (states follower).lastDown =
                      some (selected.view.payload.downRecord follower)) ∧
                  ReferenceActiveDataOwnership.carriedOccupiedFields
                    selected.view.payload R[k.val].input.state ∧
                  ReferenceActiveDataOwnership.carriedOccupiedFields
                    selected.view.payload R[k.val].output.next ∧
                  input = ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput
                    selected (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) ∧
                  input.fast = selected.arm ∧
                  selected.arm ∉ selected.view.payload.slowSet.val ∧
                  (ReferenceActivePhysicalStep.prepare
                    R[k.val].input).arms.actions =
                    ActiveRoundActions.actions p.two_le_m
                      (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states)
                      input ∧
                  (∀ player : Fin p.m,
                    ((ReferenceActivePhysicalStep.prepare
                      R[k.val].input).feedback.observations player).val.val =
                    ActiveRoundActions.feedback p.two_le_m
                      (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states)
                      input
                      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                        rewards R[k.val].input.time) player) ∧
                  (∀ follower,
                    ActiveFollowerLifecycle.releaseCondition rate.eta follower
                      (ActiveFollowerLifecycle.publicRowOfCompleteRow
                        R[k.val].input.row R[k.val].input.time)
                      ((ReferenceActivePhysicalStep.prepare
                        R[k.val].input).feedback.observations
                        (PublicDiscreteDraws.followerPlayer p.two_le_m follower))
                      (selected.view.payload.downRecord follower) =
                    ActiveRoundActions.releaseObservation p.two_le_m
                      (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states)
                      input
                      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                        rewards R[k.val].input.time) follower) ∧
                  (∀ follower : ActiveRoundActions.Follower p.m,
                    (states (ReferenceFirstLiveReleaseGeometry.followerToFin follower)).status =
                        .pending →
                    (ReferencePhysicalReleaseQuota.upFlag selected.view.payload
                      R[k.val] (ReferenceFirstLiveReleaseGeometry.followerToFin follower) =
                        true ↔
                      input.slot = PublicDiscreteDraws.upSlot ∧
                      input.selected = follower ∧
                      input.tuple.val (ActiveRoundActions.coordinator p.two_le_m) =
                        selected.view.payload.assignment.auxiliary ∧
                      input.fast ≠ selected.view.payload.assignment.auxiliary ∧
                      0 < (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                        rewards R[k.val].input.time).val
                        selected.view.payload.assignment.auxiliary)) ∧
                  (∀ follower : ActiveRoundActions.Follower p.m,
                    (states (ReferenceFirstLiveReleaseGeometry.followerToFin follower)).status =
                        .pending →
                    (ReferencePhysicalReleaseQuota.dataFlag selected.view.payload
                      R[k.val] (ReferenceFirstLiveReleaseGeometry.followerToFin follower) =
                        true ↔
                      input.slot = PublicDiscreteDraws.dataSlot ∧
                      input.pilots (ActiveRoundActions.coordinator p.two_le_m) =
                        selected.view.payload.assignment.assigned follower ∧
                      0 < (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                        rewards R[k.val].input.time).val
                        (selected.view.payload.assignment.assigned follower))) ∧
                  ReleaseRoundKernel.slowReward
                    (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                      rewards R[k.val].input.time)
                    selected.view.payload.slowSet +
                    (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                      rewards R[k.val].input.time).val selected.arm -
                    (∑ player : Fin p.m,
                      ((R[k.val].ownEntries player).2).val.val) ≤
                  (∑ follower ∈ ReferencePhysicalReleaseQuota.pendingSet
                    selected.view.payload R[k.val],
                    ReleaseRoundKernel.chi
                      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                        rewards R[k.val].input.time)
                      (selected.view.payload.assignment.assigned follower)) +
                  (if selected.arm = selected.view.payload.assignment.auxiliary ∧
                      (ReferencePhysicalReleaseQuota.pendingSet
                        selected.view.payload R[k.val]).Nonempty then
                    (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                      rewards R[k.val].input.time).val
                        selected.view.payload.assignment.auxiliary
                  else 0)
        else True := by
  classical
  intro R w v tail c K
  constructor
  · exact ReferencePostReplacementCollectionReleaseBoundary.raw_collection_next_installation_release_boundary
      rate rewards C_star C_h z
  · intro b hbIndex
    by_cases hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true
    · simp only [ite_eq_left hb]
      let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (b.val + 1)
      let V := R[b.val] :: W
      let Rel := V.dropWhile
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
      have hoccupied :=
        ReferencePostReplacementCollectionReleaseBoundary.actual_later_installation_release_suffix_actual_occupied
          rate rewards C_star C_h z b
      rw [ite_eq_left hb] at hoccupied
      have hhistory :=
        ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
          rate rewards C_star C_h z b
      rw [ite_eq_left hb] at hhistory
      rcases hhistory with
        ⟨birthRegisters, birthOwned, beta, birthSelected, _hnext, _hbirth,
          hlaterBirth, _hbSelection, _hbPayload, _hbPending, _hbNoEvent,
          _hbFollowers, _hcontinued, _hnoRelease, hframes⟩
      change ∀ i (hi : i < Rel.length), _
      intro i hi
      obtain ⟨j, hj, hrelW, selectedW, hselectedW, hemptyW, hoccupiedW⟩ :=
        hoccupied i hi
      have hjW : j < W.length := by
        simpa only [W, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix] using hj
      have htake : W.length ≤ (R.drop (b.val + 1)).length := by
        dsimp only [W, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix]
        exact takeWhile_length_le _ _
      have hdrop : (R.drop (b.val + 1)).length = R.length - (b.val + 1) := by
        simp only [List.length_drop]
      have hboundW : b.val + 1 + W.length ≤ R.length := by
        rw [hdrop] at htake
        have hbLt := b.isLt
        omega
      have hindexBound : b.val + 1 + j < R.length := by omega
      have hbPlus : b.val + 1 < R.length := by omega
      let k : Fin R.length := ⟨b.val + 1 + j, hindexBound⟩
      have hprefix := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
        rewards C_star C_h z ⟨b.val + 1, hbPlus⟩ j hj
      have hrecordW : W[j]'hj = R[k.val]'k.isLt := by
        simpa only [k] using hprefix
      have hlaunchNe : ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate z rewards C_star C_h ≠ none := by
        intro hnone
        have hindex : b.val + 1 + j < R.length := by
          simpa only [k] using k.isLt
        simp [R, ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone] at hindex
      let active := ReferenceCompletePhysicalHistory.correctedLaunchPayload
        rate z rewards C_star C_h hlaunchNe
      have hlaunch := ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
        rate z rewards C_star C_h hlaunchNe
      have hrunRecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate z rewards C_star C_h active hlaunch
      have hrunInputs := ReferenceActivePhysicalHorizon.run_record_inputs
        active z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (by
          have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate z rewards C_star C_h
          omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate z rewards C_star C_h active hlaunch)
      have hrecordMemRun : R[k.val]'k.isLt ∈
          (ReferenceActivePhysicalHorizon.run active z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
            (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
            (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
            (by
              have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T
                rate z rewards C_star C_h
              omega)
            (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
              rate z rewards C_star C_h active hlaunch)).records := by
        rw [← hrunRecords]
        exact List.getElem_mem k.isLt
      have hrecordRewards := (hrunInputs _ hrecordMemRun).2.2
      have hrewards : R[k.val].input.rewards = rewards := hrecordRewards
      have hrelIndex : Rel[i]'hi = W[j]'hj := hrelW
      have hoccW : ∃ selected : ReferenceActivePhysicalStep.Selection W[j].input,
          W[j].output.preparation.coordinator.selection = some selected ∧
          selected.view.pendingAtChoice = ∅ ∧
          ∀ follower (choice : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
            (ReferenceFollowerFixedReply.actualChoice W[j] follower).configuration =
              .ordinary choice memory → choice.status ≠ .unoccupied :=
        ⟨selectedW, hselectedW, hemptyW, hoccupiedW⟩
      have hoccRecord :
          ∃ selected : ReferenceActivePhysicalStep.Selection (R[k.val].input),
            R[k.val].output.preparation.coordinator.selection = some selected ∧
            selected.view.pendingAtChoice = ∅ ∧
            ∀ follower (choice : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
              (ReferenceFollowerFixedReply.actualChoice R[k.val] follower).configuration =
                .ordinary choice memory → choice.status ≠ .unoccupied := by
        exact hrecordW ▸ hoccW
      obtain ⟨selected, hselected, hempty, hoccupied⟩ := hoccRecord
      have hframeW :
          ∃ registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
            ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters registers,
              ∃ selectedFrame : ReferenceActivePhysicalStep.Selection W[j].input,
                W[j].input.state.coordinator = .live registers owned beta ∧
                registers.payload = birthRegisters.payload ∧
                W[j].output.preparation.coordinator.selection = some selectedFrame ∧
                selectedFrame.view.payload = birthRegisters.payload ∧
                selectedFrame.view.pendingAtChoice = registers.pendingAtChoice := by
        obtain ⟨_, hframes⟩ := hframes
        obtain ⟨registers, owned, selectedFrame, next, nextOwned, states, memories,
          hstate, hregisterPayload, hframeSelection, hframePayload, hframePending,
          _hnext, _hnextPayload, _hnextPending, _hordinary, _hoccupied,
          _hcleared, _hfollowing⟩ := hframes ⟨j, hj⟩
        exact ⟨registers, owned, selectedFrame, hstate, hregisterPayload,
          hframeSelection, hframePayload, hframePending⟩
      have hframeRecord :
          ∃ registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
            ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters registers,
              ∃ selectedFrame : ReferenceActivePhysicalStep.Selection (R[k.val].input),
                R[k.val].input.state.coordinator = .live registers owned beta ∧
                registers.payload = birthRegisters.payload ∧
                R[k.val].output.preparation.coordinator.selection = some selectedFrame ∧
                selectedFrame.view.payload = birthRegisters.payload ∧
                selectedFrame.view.pendingAtChoice = registers.pendingAtChoice := by
        exact hrecordW ▸ hframeW
      obtain ⟨registers, owned, selectedFrame, hstate, hregisterPayload,
        hframeSelection, hframePayload, hframePending⟩ := hframeRecord
      have hselectedEq : selectedFrame = selected :=
        Option.some.inj (hframeSelection.symm.trans hselected)
      subst selectedFrame
      have hstrict : ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h < registers.payload.sigma.val := by
        rw [hregisterPayload]
        exact hlaterBirth
      have hcalendar :=
        ReferenceCompleteLaterLiveCalendarService.complete_later_live_calendar_service
          (rate := rate) rewards C_star C_h z k registers owned beta hstate
      rcases hcalendar with ⟨hpreparedCoordinator, hdispatchBranches⟩
      have hcontinueW :=
        ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_test
          rewards C_star C_h z ⟨b.val + 1, hbPlus⟩ j hj
      have hcontinue :
          ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest R[k.val] = true := by
        exact hrecordW ▸ hcontinueW
      unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at hcontinue
      rw [R[k.val].output_eq] at hcontinue
      simp only [ReferenceActivePhysicalStep.step] at hcontinue
      rw [hpreparedCoordinator] at hcontinue
      let current := ReferenceActivePhysicalStep.liveInput R[k.val].input registers owned beta
      cases hdispatch : CoordinatorRoundDispatch.dispatchLive current with
      | continuingChosen dispatched hstartEq continuation armSelection =>
          have hdispatchExpanded := hdispatch
          dsimp only [current] at hdispatchExpanded
          rw [hdispatchExpanded] at hcontinue
          have hbranch := hdispatchBranches
          dsimp only [current] at hbranch
          rw [hdispatchExpanded] at hbranch
          obtain ⟨chosen, hchosenPreparation, _hchosenPayload, _hchosenCutoff,
            _hchosenStarted, _hchosenArm, hlive, hchosenOutput, _⟩ :=
            hbranch hstrict
          have hchosenEq : chosen = selected :=
            Option.some.inj (hchosenOutput.symm.trans hselected)
          subst chosen
          have hliveSelected :
              CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
                selected.view.cutoff R[k.val].input.time := hlive
          have hvalid :=
            ReferenceLaterLiveNumericalReadout.selection_choiceValid selected
          obtain ⟨states, memories, hordinaryActual, hoccupiedDown,
            hinputFields, houtputFields⟩ :=
            ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
              (rate := rate) rewards C_star C_h z k selected hselected
          have hordinaryPrepared : ∀ follower,
              ((ReferenceActivePhysicalStep.prepare R[k.val].input).followers.followers
                follower).configuration = .ordinary (states follower) (memories follower) := by
            intro follower
            have h := hordinaryActual follower
            change (R[k.val].output.preparation.followers.followers follower).configuration = _ at h
            rw [R[k.val].output_eq] at h
            simpa only [ReferenceActivePhysicalStep.step] using h
          have hfields : ∀ follower,
              (states follower).status ≠ .unoccupied ∧
                (states follower).lastDown = some (selected.view.payload.downRecord follower) := by
            intro follower
            have hnotUnoccupied := hoccupied follower (states follower) (memories follower)
              (hordinaryActual follower)
            exact ⟨hnotUnoccupied, hoccupiedDown follower hnotUnoccupied⟩
          have hselectionPrepared :
              (ReferenceActivePhysicalStep.prepare R[k.val].input).coordinator.selection =
                some selected := by
            simpa only [R[k.val].output_eq, ReferenceActivePhysicalStep.step] using hselected
          let snapshot := ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states
          let input := ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput selected hvalid
          let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards
            R[k.val].input.time
          have hrowEq : ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
              R[k.val].input.rewards R[k.val].input.time = row := by
            simp only [hrewards, row]
          have hfastFacts :=
            ReferenceFirstLiveReleaseGeometry.actual_releaseRoundInput_fast_eq_selected
              selected hliveSelected hempty hvalid
          have hfast : input.fast = selected.arm := by
            simpa only [input, ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput]
              using hfastFacts.1
          have hfastOutside : selected.arm ∉ selected.view.payload.slowSet.val := by
            simpa only [input, ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput]
              using hfastFacts.2
          have hmissing : snapshot.missing = ∅ := by
            change selected.view.pendingAtChoice = ∅
            exact hempty
          have hslot : PublicDiscreteDraws.slotDraw
              (R[k.val].input.row.2 R[k.val].input.time).1 = input.slot := by rfl
          have hselectedDraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (R[k.val].input.row.2 R[k.val].input.time).1 = input.selected := by rfl
          have htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (R[k.val].input.row.2 R[k.val].input.time).1 = input.tuple := by rfl
          have hordinaryPrepared' : ∀ follower,
              ((ReferenceActivePhysicalStep.prepare R[k.val].input).followers.followers
                follower).configuration = .ordinary (states follower) (memories follower) :=
            hordinaryPrepared
          have hactions :=
            ReferenceFirstLiveReleaseGeometry.prepared_actions_eq_projected selected
              hselectionPrepared states memories hordinaryPrepared' hfields input hmissing
              (by rfl) (by rfl) (by rfl) hfast
          have hstatus : ∀ follower : ActiveRoundActions.Follower p.m,
              snapshot.status follower = .pending ∨ snapshot.status follower = .released := by
            intro follower
            change (states follower).status = .pending ∨ (states follower).status = .released
            cases hs : (states follower).status with
            | unoccupied => exact False.elim ((hfields follower).1 hs)
            | pending => exact Or.inl rfl
            | released => exact Or.inr rfl
          have hpilots : input.pilots = fun player => PublicDiscreteDraws.pilotDraw
              (K_pos p) player (R[k.val].input.row.2 R[k.val].input.time).1 := by rfl
          have hobservations : ∀ player : Fin p.m,
              ((ReferenceActivePhysicalStep.prepare (R[k.val].input)).feedback.observations
                player).val.val = ActiveRoundActions.feedback p.two_le_m snapshot input row player := by
            intro player
            have h := ReferenceFirstLiveReleaseGeometry.prepared_observation_eq_projected
              selected snapshot input player hactions
            calc
              _ = ActiveRoundActions.feedback p.two_le_m snapshot input
                  (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                    R[k.val].input.rewards R[k.val].input.time) player := h
              _ = ActiveRoundActions.feedback p.two_le_m snapshot input row player := by
                    rw [hrowEq]
          have hrelease : ∀ follower,
              ActiveFollowerLifecycle.releaseCondition rate.eta follower
                (ActiveFollowerLifecycle.publicRowOfCompleteRow
                  R[k.val].input.row R[k.val].input.time)
                ((ReferenceActivePhysicalStep.prepare (R[k.val].input)).feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m follower))
                (selected.view.payload.downRecord follower) =
              ActiveRoundActions.releaseObservation p.two_le_m snapshot input row follower := by
            intro follower
            have h := ReferenceFirstLiveReleaseGeometry.prepared_releaseCondition_eq_projected
              selected snapshot input follower hactions (by rfl) (by rfl) (by rfl) hpilots
            calc
              _ = ActiveRoundActions.releaseObservation p.two_le_m snapshot input
                  (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                    R[k.val].input.rewards R[k.val].input.time) follower := h
              _ = ActiveRoundActions.releaseObservation p.two_le_m snapshot input row follower := by
                    rw [hrowEq]
          have hflagsUp : ∀ follower : ActiveRoundActions.Follower p.m,
              (states (ReferenceFirstLiveReleaseGeometry.followerToFin follower)).status =
                  .pending →
              (ReferencePhysicalReleaseQuota.upFlag selected.view.payload R[k.val]
                (ReferenceFirstLiveReleaseGeometry.followerToFin follower) = true ↔
                input.slot = PublicDiscreteDraws.upSlot ∧ input.selected = follower ∧
                  input.tuple.val (ActiveRoundActions.coordinator p.two_le_m) =
                    selected.view.payload.assignment.auxiliary ∧
                  input.fast ≠ selected.view.payload.assignment.auxiliary ∧
                  0 < row.val selected.view.payload.assignment.auxiliary) := by
            intro follower hpending
            let projectedFollower := ReferenceFirstLiveReleaseGeometry.followerToFin follower
            have hreleaseFollower :
                ActiveFollowerLifecycle.releaseCondition rate.eta projectedFollower
                  (ActiveFollowerLifecycle.publicRowOfCompleteRow
                    R[k.val].input.row R[k.val].input.time)
                  ((ReferenceActivePhysicalStep.prepare (R[k.val].input)).feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m follower))
                  (selected.view.payload.downRecord projectedFollower) =
                ActiveRoundActions.releaseObservation p.two_le_m snapshot input row follower := by
              have hindex : projectedFollower = follower := by
                apply Fin.ext
                rfl
              simpa only [projectedFollower, hindex] using hrelease follower
            have hpendingSnapshot : snapshot.status follower = .pending := by
              change (states (ReferenceFirstLiveReleaseGeometry.followerToFin follower)).status =
                .pending
              exact hpending
            have hphysical :=
              (ReferenceFirstLiveReleaseGeometry.actual_release_flags_iff
                R[k.val] selected.view.payload projectedFollower).1
            rw [hslot] at hphysical
            exact hphysical.trans
              (ReferenceFirstLiveReleaseGeometry.actual_pending_release_event_geometry
                selected snapshot input row hmissing hstatus follower hpendingSnapshot
                hreleaseFollower).1
          have hflagsData : ∀ follower : ActiveRoundActions.Follower p.m,
              (states (ReferenceFirstLiveReleaseGeometry.followerToFin follower)).status =
                  .pending →
              (ReferencePhysicalReleaseQuota.dataFlag selected.view.payload R[k.val]
                (ReferenceFirstLiveReleaseGeometry.followerToFin follower) = true ↔
                input.slot = PublicDiscreteDraws.dataSlot ∧
                  input.pilots (ActiveRoundActions.coordinator p.two_le_m) =
                    selected.view.payload.assignment.assigned follower ∧
                  0 < row.val (selected.view.payload.assignment.assigned follower)) := by
            intro follower hpending
            let projectedFollower := ReferenceFirstLiveReleaseGeometry.followerToFin follower
            have hreleaseFollower :
                ActiveFollowerLifecycle.releaseCondition rate.eta projectedFollower
                  (ActiveFollowerLifecycle.publicRowOfCompleteRow
                    R[k.val].input.row R[k.val].input.time)
                  ((ReferenceActivePhysicalStep.prepare (R[k.val].input)).feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m follower))
                  (selected.view.payload.downRecord projectedFollower) =
                ActiveRoundActions.releaseObservation p.two_le_m snapshot input row follower := by
              have hindex : projectedFollower = follower := by
                apply Fin.ext
                rfl
              simpa only [projectedFollower, hindex] using hrelease follower
            have hpendingSnapshot : snapshot.status follower = .pending := by
              change (states (ReferenceFirstLiveReleaseGeometry.followerToFin follower)).status =
                .pending
              exact hpending
            have hphysical :=
              (ReferenceFirstLiveReleaseGeometry.actual_release_flags_iff
                R[k.val] selected.view.payload projectedFollower).2
            rw [hslot] at hphysical
            exact hphysical.trans
              (ReferenceFirstLiveReleaseGeometry.actual_pending_release_event_geometry
                selected snapshot input row hmissing hstatus follower hpendingSnapshot
                hreleaseFollower).2
          have hpendingOrdinary : ∀ follower : Fin (p.m - 1),
              follower ∈ ReferencePhysicalReleaseQuota.pendingSet
                  selected.view.payload R[k.val] ↔
                (states follower).status = .pending := by
            intro follower
            have hregisterPayloadSelected : registers.payload = selected.view.payload :=
              hregisterPayload.trans hframePayload.symm
            have hregisterPending : registers.pendingAtChoice = ∅ :=
              hframePending.symm.trans hempty
            exact ReferencePhysicalReleaseQuota.pendingAtStart_ordinary_prepare
              selected.view.payload R[k.val].input registers owned beta hstate
              hregisterPayloadSelected hregisterPending follower
              (states follower) (memories follower)
              (hordinaryPrepared follower)
          have hownObservation : ∀ player : Fin p.m,
              ((R[k.val].ownEntries player).2).val.val =
                ((ReferenceActivePhysicalStep.prepare (R[k.val].input)).feedback.observations
                  player).val.val := by
            intro player
            rw [ReferenceActivePhysicalHorizon.RoundRecord.ownEntries_formula
              R[k.val] player]
            simp only [ReferenceActivePhysicalHorizon.RoundRecord.actions,
              R[k.val].output_eq]
            rfl
          have htotal : ReleaseRoundKernel.physicalFeedbackTotal p.two_le_m snapshot input row =
              ∑ player : Fin p.m, ((R[k.val].ownEntries player).2).val.val := by
            have hfollowers (f : Fin p.m → ℝ) :
                (∑ follower : ActiveRoundActions.Follower p.m,
                  f (PublicDiscreteDraws.followerPlayer p.two_le_m follower)) =
                ∑ player ∈ Finset.univ.erase (ActiveRoundActions.coordinator p.two_le_m), f player := by
              classical
              apply Finset.sum_bij (s := Finset.univ)
                (t := Finset.univ.erase (ActiveRoundActions.coordinator p.two_le_m))
                (fun follower _ => PublicDiscreteDraws.followerPlayer p.two_le_m follower)
              · intro follower _
                exact Finset.mem_erase.mpr ⟨
                  ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m follower,
                  Finset.mem_univ _⟩
              · intro follower _ other _ heq
                exact ActiveRoundActions.followerPlayer_injective p.two_le_m heq
              · intro player hplayer
                rcases Finset.mem_erase.mp hplayer with ⟨hne, _⟩
                refine ⟨ActiveRoundActions.followerIndex p.two_le_m player hne,
                  Finset.mem_univ _, ?_⟩
                exact ActiveRoundActions.followerPlayer_followerIndex p.two_le_m player hne
              · intro follower _
                rfl
            have hsum (f : Fin p.m → ℝ) :
                (∑ player : Fin p.m, f player) =
                  f (ActiveRoundActions.coordinator p.two_le_m) +
                    ∑ follower : ActiveRoundActions.Follower p.m,
                      f (PublicDiscreteDraws.followerPlayer p.two_le_m follower) := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ _), hfollowers]
            have hfeedback (player : Fin p.m) :
                ActiveRoundActions.feedback p.two_le_m snapshot input row player =
                  ((R[k.val].ownEntries player).2).val.val := by
              calc
                ActiveRoundActions.feedback p.two_le_m snapshot input row player =
                    ((ReferenceActivePhysicalStep.prepare (R[k.val].input)).feedback.observations
                      player).val.val :=
                  (hobservations player).symm
                _ = ((R[k.val].ownEntries player).2).val.val :=
                  (hownObservation player).symm
            calc
              ReleaseRoundKernel.physicalFeedbackTotal p.two_le_m snapshot input row =
                  ActiveRoundActions.feedback p.two_le_m snapshot input row
                    (ActiveRoundActions.coordinator p.two_le_m) +
                    ∑ follower : ActiveRoundActions.Follower p.m,
                      ActiveRoundActions.feedback p.two_le_m snapshot input row
                        (PublicDiscreteDraws.followerPlayer p.two_le_m follower) := rfl
              _ = ((R[k.val].ownEntries (ActiveRoundActions.coordinator p.two_le_m)).2).val.val +
                    ∑ follower : Fin (p.m - 1),
                      ((R[k.val].ownEntries
                        (PublicDiscreteDraws.followerPlayer p.two_le_m follower)).2).val.val := by
                  rw [hfeedback (ActiveRoundActions.coordinator p.two_le_m)]
                  apply congrArg
                  apply Finset.sum_congr rfl
                  intro follower _
                  exact hfeedback (PublicDiscreteDraws.followerPlayer p.two_le_m follower)
              _ = ∑ player : Fin p.m, ((R[k.val].ownEntries player).2).val.val :=
                (hsum (fun player => ((R[k.val].ownEntries player).2).val.val)).symm
          let finToFollower : Fin (p.m - 1) → ActiveRoundActions.Follower p.m := fun i =>
            ⟨i.val, by
              simpa only [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using
                i.isLt⟩
          have hpendingStatus (follower : ActiveRoundActions.Follower p.m) :
              (ReferenceFirstLiveReleaseGeometry.followerToFin follower) ∈
                  ReferencePhysicalReleaseQuota.pendingSet selected.view.payload R[k.val] ↔
                snapshot.status follower = .pending := by
            have h := hpendingOrdinary (ReferenceFirstLiveReleaseGeometry.followerToFin follower)
            have hstatusEq : snapshot.status follower =
                (states (ReferenceFirstLiveReleaseGeometry.followerToFin follower)).status := by
              change (states follower).status =
                (states (ReferenceFirstLiveReleaseGeometry.followerToFin follower)).status
              congr 1
            simpa only [hstatusEq] using h
          have hpendingSum :
              (∑ follower : ActiveRoundActions.Follower p.m,
                if snapshot.status follower = .pending then
                  ReleaseRoundKernel.chi row
                    (selected.view.payload.assignment.assigned follower) else 0) =
              ∑ follower ∈ ReferencePhysicalReleaseQuota.pendingSet
                  selected.view.payload R[k.val],
                ReleaseRoundKernel.chi row
                  (selected.view.payload.assignment.assigned follower) := by
            classical
            calc
              _ = ∑ follower : Fin (p.m - 1),
                  if follower ∈ ReferencePhysicalReleaseQuota.pendingSet
                      selected.view.payload R[k.val] then
                    ReleaseRoundKernel.chi row
                      (selected.view.payload.assignment.assigned (finToFollower follower))
                  else 0 := by
                change (∑ follower : Fin (p.m - 1),
                  if snapshot.status (finToFollower follower) = .pending then
                    ReleaseRoundKernel.chi row
                      (selected.view.payload.assignment.assigned (finToFollower follower))
                  else 0) = _
                apply Finset.sum_congr rfl
                intro follower _
                have hiff := hpendingStatus (finToFollower follower)
                have hmem : follower ∈ ReferencePhysicalReleaseQuota.pendingSet
                    selected.view.payload R[k.val] ↔
                    ReferenceFirstLiveReleaseGeometry.followerToFin (finToFollower follower) ∈
                      ReferencePhysicalReleaseQuota.pendingSet
                        selected.view.payload R[k.val] := by
                  simp only [finToFollower, ReferenceFirstLiveReleaseGeometry.followerToFin]
                have hiff' : follower ∈ ReferencePhysicalReleaseQuota.pendingSet
                    selected.view.payload R[k.val] ↔
                    snapshot.status (finToFollower follower) = .pending := hmem.trans hiff
                exact if_congr hiff'.symm rfl rfl
              _ = ∑ follower ∈ ReferencePhysicalReleaseQuota.pendingSet
                    selected.view.payload R[k.val],
                    ReleaseRoundKernel.chi row
                      (selected.view.payload.assignment.assigned follower) := by
                rw [Finset.sum_ite_mem, Finset.univ_inter]
                apply Finset.sum_congr rfl
                intro follower hf
                rfl
          have hcollision :
              (∃ follower : ActiveRoundActions.Follower p.m,
                snapshot.status follower = .pending) ↔
                (ReferencePhysicalReleaseQuota.pendingSet
                  selected.view.payload R[k.val]).Nonempty := by
            constructor
            · rintro ⟨follower, hpending⟩
              exact ⟨ReferenceFirstLiveReleaseGeometry.followerToFin follower,
                (hpendingStatus follower).mpr hpending⟩
            · rintro ⟨follower, hmem⟩
              refine ⟨finToFollower follower, ?_⟩
              have hround :
                  ReferenceFirstLiveReleaseGeometry.followerToFin (finToFollower follower) =
                    follower := by
                apply Fin.ext
                rfl
              simpa only [hround] using (hpendingStatus (finToFollower follower)).mp hmem
          have hslowImage : selected.view.payload.slowSet.val =
              ReleaseRoundKernel.assignedImage selected.view.payload.assignment :=
            selected.view.payload.assignment_image.symm
          have hkernel := ReleaseRoundKernel.pathwise_sentinel_cost_bound
            p.two_le_m selected.view.payload.assignment selected.view.payload.slowSet
            hslowImage snapshot hmissing hstatus input row
          have hcost := hkernel
          rw [hfast, htotal, hpendingSum] at hcost
          simp only [hcollision] at hcost
          refine ⟨j, hj, hrelIndex, k, rfl, selected, states, memories, input,
            hrecordW, hselected, hempty, hliveSelected, hvalid, hordinaryActual, hfields,
            hinputFields, houtputFields, rfl, hfast, hfastOutside, hactions,
            hobservations, hrelease, hflagsUp, hflagsData, hcost⟩

      | cutoffChosen dispatched startRoundEq ledger initializationEq ledgerEq
          initializationDomain cutoffClock cutoffPending noAssignment selection =>
          have hdispatchExpanded := hdispatch
          dsimp only [current] at hdispatchExpanded
          rw [hdispatchExpanded] at hcontinue
          simp at hcontinue
      | clockFailure failure dispatchEq =>
          have hdispatchExpanded := hdispatch
          dsimp only [current] at hdispatchExpanded
          rw [hdispatchExpanded] at hcontinue
          simp at hcontinue
      | initializerFailure dispatched startRoundEq checked checkedEq =>
          have hdispatchExpanded := hdispatch
          dsimp only [current] at hdispatchExpanded
          rw [hdispatchExpanded] at hcontinue
          simp at hcontinue
      | localFailure dispatched startRoundEq reason =>
          have hdispatchExpanded := hdispatch
          dsimp only [current] at hdispatchExpanded
          rw [hdispatchExpanded] at hcontinue
          simp at hcontinue
    · simp only [ite_eq_right hb]

end Bandits.Support.ReferencePostReplacementCollectionReleaseProjection

end
