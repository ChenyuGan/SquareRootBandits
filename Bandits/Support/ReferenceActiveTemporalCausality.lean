/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon

/-!
# Temporal reads of the existing active reference computation

Internal deterministic locality for the literal operations in
`06_interruptions.tex:197-209,235-297,376-423`, with exceptional paths from
`appendix_a_local_protocol.tex:6-14`, selected-table scope from
`08_main_theorem.tex:29-42`, and continuous/affine coordinate semantics from
`appendix_b_communication.tex:25-55` (all under `sources/zip4/manuscript/`).
Current assignment coordinates are retained. The only historical row reads
are proposal scalars during delayed DOWN acceptance; the carried buffer is
used literally, including invalid entries and original positions.
This is an internal comparison at a fixed incoming state, not a probability
law, launch construction, source-facing anchor, or manuscript closure.

The exports below cover the follower operations, first-start arm/view, current
UP adapters, calendar read lifting and empty runs. General computed evidence
and nonempty-run temporal locality are not established in this module.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceActiveTemporalCausality

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
variable {row otherRow : CompletePublicTable.CompleteRow p} {t : Fin p.T}

/-- A whole inspected scan is preserved by past proposal scalars. No current
or future proposal scalar, other label, or forward bit is required. -/
theorem acceptedCutoffScan_eq_of_past_prop
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hstart : (ActiveFollowerDownAcceptance.downStart p rate M).val ≤ t.val)
    (hpast : ∀ j : Fin p.T, j.val < t.val →
      (row.2 j).1 ContinuousControlSlice.Label.prop =
        (otherRow.2 j).1 ContinuousControlSlice.Label.prop) :
    ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t hstart row =
      ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t hstart otherRow := by
  apply ActiveFollowerDownAcceptance.acceptedCutoffScan_noninterference
  intro j hj
  have hb := FollowerCutoffScan.followerCutoffScan_inspected_source_bounds p rate.eta.val
    (ActiveFollowerDownAcceptance.downStart p rate M) t hstart (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) j hj
  exact hpast j (by omega)

theorem currentDecodeStep_eq_of_current
    (i : Fin (p.m - 1)) (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hcurrent : row.2 t = otherRow.2 t) :
    ActiveFollowerDownAcceptance.currentDecodeStep p i row t observation rate state =
      ActiveFollowerDownAcceptance.currentDecodeStep p i otherRow t observation rate state := by
  apply ActiveFollowerDownAcceptance.decodeStep_depends_on_current_input
  unfold ActiveFollowerDownAcceptance.currentInputExtension ActiveFollowerDownAcceptance.currentRoundInput
  rw [hcurrent]

theorem coordinatorArmChoice_eq_of_current
    {eta : ReferencePrelaunchFollower.LearningRate}
    (payload : AssignmentStartPayload.Input p eta)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hcurrent : row.2 t = otherRow.2 t) :
    CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff t weights row =
      CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff t weights otherRow := by
  simp only [CoordinatorLocalArmChoice.coordinatorArmChoice, hcurrent]

theorem expectedDownFlatWord_eq_of_current
    {eta : ReferencePrelaunchFollower.LearningRate}
    (view : Option (ReferenceDownReception.ChoiceTimeView p eta)) (i : Fin (p.m - 1))
    (hcurrent : row.2 t = otherRow.2 t) :
    ReferenceDownReception.expectedDownFlatWord view i row t = ReferenceDownReception.expectedDownFlatWord view i otherRow t := by
  cases view with
  | none => rfl
  | some view =>
      unfold ReferenceDownReception.expectedDownFlatWord
      dsimp only
      unfold CoordinatorLocalArmChoice.coordinatorArmChoice ReferenceDownReception.selectedDownSenderBranch
      rw [hcurrent]

/-- Full reference DOWN diagnostics and outcome, including domain failures,
decoder rejection, mismatch suppression and replay failure. -/
theorem referenceDownCut_eq_of_temporal_reads
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta)) (i : Fin (p.m - 1))
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hcurrent : row.2 t = otherRow.2 t)
    (hpast : ∀ j : Fin p.T, j.val < t.val →
      (row.2 j).1 ContinuousControlSlice.Label.prop =
        (otherRow.2 j).1 ContinuousControlSlice.Label.prop) :
    ReferenceDownReception.referenceDownCut p view i row t observation rate state =
      ReferenceDownReception.referenceDownCut p view i otherRow t observation rate state := by
  have hs : ActiveFollowerDownAcceptance.downSelected p i row t =
      ActiveFollowerDownAcceptance.downSelected p i otherRow t := by
    unfold ActiveFollowerDownAcceptance.downSelected
    rw [hcurrent]
  simp only [ReferenceDownReception.referenceDownCut, hs, expectedDownFlatWord_eq_of_current view i hcurrent,
    currentDecodeStep_eq_of_current i observation state hcurrent,
    acceptedCutoffScan_eq_of_past_prop _ _ hpast]
  rw [hs]

theorem checkedUpOffer_eq_of_current
    {eta : ReferencePrelaunchFollower.LearningRate}
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (state : ReferencePrelaunchFollower.State p eta)
    (hcurrent : row.2 t = otherRow.2 t) :
    ActiveFollowerQueueOperation.checkedUpOffer eta i row activation t state =
      ActiveFollowerQueueOperation.checkedUpOffer eta i otherRow activation t state := by
  unfold ActiveFollowerQueueOperation.checkedUpOffer ActiveFollowerQueueOperation.selectedUpRound
  rw [hcurrent]

/-- The row is retained literally in PREPARE; only its computed arm and local
configuration agree; neither retained whole row is equated. -/
theorem prepare_projections_eq_of_current
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (active : activation.val ≤ t.val + 1) (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (hcurrent : row.2 t = otherRow.2 t) :
    ((DeclaredFollowerLocalRound.prepare rate i row activation t active configuration).arm,
      (DeclaredFollowerLocalRound.prepare rate i row activation t active configuration).configuration) =
      ((DeclaredFollowerLocalRound.prepare rate i otherRow activation t active configuration).arm,
        (DeclaredFollowerLocalRound.prepare rate i otherRow activation t active configuration).configuration) := by
  cases configuration with
  | dagger => rfl
  | ordinary state memory =>
      cases hstart : ActiveFollowerLifecycle.startRound rate.eta t state memory with
      | error reason => simp only [DeclaredFollowerLocalRound.prepare, hstart]
      | ok pair =>
          rcases pair with ⟨choiceState, choiceMemory⟩
          simp only [DeclaredFollowerLocalRound.prepare, hstart]
          rw [checkedUpOffer_eq_of_current i activation choiceState hcurrent]
          cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i otherRow activation t choiceState
          · rfl
          · simp only [ActiveFollowerArmChoice.followerArmChoice, hcurrent]
            cases ActiveFollowerArmChoice.followerArmChoiceCore choiceState (otherRow.2 t) i none <;> rfl
          · rename_i offered
            simp only [ActiveFollowerArmChoice.followerArmChoice, hcurrent]
            cases ActiveFollowerArmChoice.followerArmChoiceCore choiceState (otherRow.2 t) i (some offered) <;> rfl

theorem checkedLogging_eq_of_current
    {eta : ReferencePrelaunchFollower.LearningRate}
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (own : Fin p.K × ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p eta)
    (hcurrent : row.2 t = otherRow.2 t) :
    ActiveFollowerLogging.checkedLogging i row activation t own state =
      ActiveFollowerLogging.checkedLogging i otherRow activation t own state := by
  have hr : ReferencePrelaunchFollower.loggingRound i row activation t own =
      ReferencePrelaunchFollower.loggingRound i otherRow activation t own := by
    unfold ReferencePrelaunchFollower.loggingRound
    rw [hcurrent]
  have hl : ReferencePrelaunchFollower.logAt i row activation t own =
      ReferencePrelaunchFollower.logAt i otherRow activation t own := by
    unfold ReferencePrelaunchFollower.logAt
    rw [hr]
  have hu : ActiveFollowerLogging.loggingUpdate i row activation t own state =
      ActiveFollowerLogging.loggingUpdate i otherRow activation t own state := by
    unfold ActiveFollowerLogging.loggingUpdate
    rw [hl]
  unfold ActiveFollowerLogging.checkedLogging
  rw [hu]

theorem releaseAndFinish_eq_of_current
    (i : Fin (p.m - 1)) (observation : ReferencePrelaunchFollower.Observation p)
    (choiceState postRecord : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p) (hcurrent : row.2 t = otherRow.2 t) :
    DeclaredFollowerLocalRound.releaseAndFinish rate i row t observation choiceState memory postRecord =
      DeclaredFollowerLocalRound.releaseAndFinish rate i otherRow t observation choiceState memory postRecord := by
  simp only [DeclaredFollowerLocalRound.releaseAndFinish, ActiveFollowerLifecycle.publicRowOfCompleteRow, ActiveFollowerLifecycle.finishRound,
    FollowerCutoffScan.completeRowProposalBit, CompletePublicTable.completeRowLearning, hcurrent]

/-- A checked occupied service comparison consumes the actual result; its
row-dependent proof certificates are not compared as raw data. -/
theorem recordOrServiceThenDown_eq_of_current_of_occupied
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (occupied : state.status ≠ .unoccupied)
    (hcurrent : row.2 t = otherRow.2 t) :
    DeclaredFollowerLocalRound.recordOrServiceThenDown rate i row activation t active arm observation state =
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate i otherRow activation t active arm observation state := by
  classical
  have ha (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) :
      ActiveFollowerQueueOperation.rawArrival rate.eta i row t M observation =
        ActiveFollowerQueueOperation.rawArrival rate.eta i otherRow t M observation := by
    unfold ActiveFollowerQueueOperation.rawArrival ActiveFollowerQueueOperation.recorderGate
    rw [hcurrent]
  unfold DeclaredFollowerLocalRound.recordOrServiceThenDown
  simp only [occupied, dite_false]
  rcases state with ⟨lastDown, served, delta, backlog, status, batch, buffer, failed⟩
  cases status <;> cases lastDown <;>
    simp only [ActiveFollowerQueueOperation.checkedService]
  all_goals split_ifs <;> simp_all

/-- Every reference follower record stage agrees, including checked logging
failures, occupied service, and the full pre-effect DOWN diagnostic. -/
theorem recordFollower_eq_of_temporal_reads
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hcurrent : row.2 t = otherRow.2 t)
    (hpast : ∀ j : Fin p.T, j.val < t.val →
      (row.2 j).1 ContinuousControlSlice.Label.prop =
        (otherRow.2 j).1 ContinuousControlSlice.Label.prop) :
    ReferenceActivePhysicalStep.recordFollower view i row activation t active arm observation state =
      ReferenceActivePhysicalStep.recordFollower view i otherRow activation t active arm observation state := by
  classical
  by_cases hu : state.status = .unoccupied
  · simp only [ReferenceActivePhysicalStep.recordFollower, hu, dite_true,
      checkedLogging_eq_of_current i activation (arm, observation) state hcurrent,
      referenceDownCut_eq_of_temporal_reads view i observation _ hcurrent hpast]
  · simp only [ReferenceActivePhysicalStep.recordFollower, hu, dite_false,
      recordOrServiceThenDown_eq_of_current_of_occupied i activation active arm observation state hu hcurrent]

/-- Full follower continuation on equal prepared computed fields. The two
literal rows are retained separately in the prepared inputs. -/
theorem finishFollower_eq_of_temporal_reads
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (hcurrent : row.2 t = otherRow.2 t)
    (hpast : ∀ j : Fin p.T, j.val < t.val →
      (row.2 j).1 ContinuousControlSlice.Label.prop =
        (otherRow.2 j).1 ContinuousControlSlice.Label.prop) :
    ReferenceActivePhysicalStep.finishFollower view
        ⟨i, row, activation, t, active, arm, configuration⟩ observation =
      ReferenceActivePhysicalStep.finishFollower view
        ⟨i, otherRow, activation, t, active, arm, configuration⟩ observation := by
  cases configuration with
  | dagger => rfl
  | ordinary state memory =>
      simp only [ReferenceActivePhysicalStep.finishFollower,
        recordFollower_eq_of_temporal_reads view i activation active arm observation state hcurrent hpast,
        releaseAndFinish_eq_of_current i observation state _ memory hcurrent]

/-- Readout of the computed first installation and current arm operation.
This is only the arm/view projection, with no retained row in its carrier. -/
def firstReadout (launch : FirstAssignmentLaunch.Input p rate.eta)
    (control : ContinuousLearningRows.TimeControl p) :
    Fin p.K × Option (ReferenceDownReception.ChoiceTimeView p rate.eta) :=
  let installed := CoordinatorAssignmentRegisterInstall.installFirst launch
  let view : ReferenceDownReception.ChoiceTimeView p rate.eta := {
    payload := installed.registers.payload
    pendingAtChoice := installed.startRoundResult.pending
    cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p installed.startRoundResult.clock.u
    complementWeights := installed.registers.complementWeights }
  ((CoordinatorLocalArmChoice.coordinatorArmChoiceCore view.payload view.pendingAtChoice
    view.cutoff launch.sigma view.complementWeights control).getD
      (ReferenceActivePhysicalStep.coordinatorFallback p), some view)

theorem first_dispatch_readout
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hfirst : x.state.coordinator = .first) :
    ((ReferenceActivePhysicalStep.dispatch x).arm, (ReferenceActivePhysicalStep.dispatch x).downView) =
      firstReadout (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x))
        (x.row.2 x.time) := by
  classical
  rw [ReferenceActivePhysicalStep.dispatch_first x hfirst]
  dsimp only [ReferenceActivePhysicalStep.firstInput]
  unfold CoordinatorRoundDispatch.dispatchFirst
  extract_lets launch installed started payload weights cutoff hpayload hstarted hcutoff
    hweights hchoice hboundary hnonempty
  have ht : installed.registers.time = x.time := by rfl
  split
  · contradiction
  · rename_i arm hselected
    simp only [ReferenceActivePhysicalStep.DispatchCut.arm,
      ReferenceActivePhysicalStep.DispatchCut.downView,
      ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
      ht, dite_true, Option.map_some]
    unfold firstReadout
    change (arm, some _) =
      ((CoordinatorLocalArmChoice.coordinatorArmChoice payload started.pending cutoff
        installed.registers.time weights x.row).getD
          (ReferenceActivePhysicalStep.coordinatorFallback p), some _)
    change CoordinatorLocalArmChoice.coordinatorArmChoice payload started.pending cutoff
      installed.registers.time weights x.row = some arm at hselected
    rw [hselected]
    rfl

/-- Current-slice locality of first-start arm and DOWN view, including the
entire current assignment vector. -/
theorem first_dispatch_projections_eq_of_current
    (state : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (active : ∀ i, (state.activations i).val ≤ t.val + 1)
    (rewards otherRewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hfirst : state.coordinator = .first)
    (hcurrent : (rows selected).2 t = (otherRows selected).2 t) :
    let x : ReferenceActivePhysicalStep.RoundInput p rate := ⟨state, rows, selected, t, active, rewards⟩
    let y : ReferenceActivePhysicalStep.RoundInput p rate := ⟨state, otherRows, selected, t, active, otherRewards⟩
    ((ReferenceActivePhysicalStep.dispatch x).arm, (ReferenceActivePhysicalStep.dispatch x).downView) =
      ((ReferenceActivePhysicalStep.dispatch y).arm, (ReferenceActivePhysicalStep.dispatch y).downView) := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate := ⟨state, rows, selected, t, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate := ⟨state, otherRows, selected, t, active, otherRewards⟩
  change ((ReferenceActivePhysicalStep.dispatch x).arm, (ReferenceActivePhysicalStep.dispatch x).downView) =
    ((ReferenceActivePhysicalStep.dispatch y).arm, (ReferenceActivePhysicalStep.dispatch y).downView)
  rw [first_dispatch_readout x hfirst, first_dispatch_readout y hfirst]
  have hl : CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x) =
      CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput y) := by
    unfold CoordinatorRoundDispatch.firstLaunchInput ReferenceActivePhysicalStep.firstInput
      ReferenceActivePhysicalStep.RoundInput.row LaterAssignmentStartOperation.ownAssignmentVector
    dsimp only [x, y]
    rw [hcurrent]
  exact congrArg₂ firstReadout hl hcurrent

/-- Congruence on the computed prepared fields, without comparing retained
whole rows. Every compared field and read is an explicit helper input. -/
theorem finishFollower_congr_of_temporal_reads
    (left right : DeclaredFollowerLocalRound.PreparedRound p rate)
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (observation : ReferencePrelaunchFollower.Observation p)
    (hfollower : left.follower = right.follower)
    (hactivation : left.activation = right.activation)
    (htime : left.time = right.time)
    (harm : left.arm = right.arm)
    (hconfiguration : left.configuration = right.configuration)
    (hcurrent : left.row.2 left.time = right.row.2 right.time)
    (hpast : ∀ j : Fin p.T, j.val < left.time.val →
      (left.row.2 j).1 ContinuousControlSlice.Label.prop =
        (right.row.2 j).1 ContinuousControlSlice.Label.prop) :
    ReferenceActivePhysicalStep.finishFollower view left observation =
      ReferenceActivePhysicalStep.finishFollower view right observation := by
  rcases left with ⟨i, row, activation, time, active, arm, configuration⟩
  rcases right with ⟨otherI, otherRow, otherActivation, otherTime, otherActive, otherArm, otherConfiguration⟩
  dsimp only at hfollower hactivation htime harm hconfiguration hcurrent hpast
  cases hfollower
  cases hactivation
  cases htime
  cases harm
  cases hconfiguration
  exact finishFollower_eq_of_temporal_reads view i activation active arm configuration observation hcurrent hpast

/-- The actual local PREPARE followed by the reference follower continuation
is temporal-local. The incoming configuration, view and own observation are
fixed here; no successful operation or valid buffer is assumed. -/
theorem preparedFollower_eq_of_temporal_reads
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (active : activation.val ≤ t.val + 1)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (hcurrent : row.2 t = otherRow.2 t)
    (hpast : ∀ j : Fin p.T, j.val < t.val →
      (row.2 j).1 ContinuousControlSlice.Label.prop =
        (otherRow.2 j).1 ContinuousControlSlice.Label.prop) :
    ReferenceActivePhysicalStep.finishFollower view
        (DeclaredFollowerLocalRound.prepare rate i row activation t active configuration) observation =
      ReferenceActivePhysicalStep.finishFollower view
        (DeclaredFollowerLocalRound.prepare rate i otherRow activation t active configuration) observation := by
  have hl := ReferenceActivePhysicalStep.local_prepare_alignment i row activation t active configuration
  have hr := ReferenceActivePhysicalStep.local_prepare_alignment i otherRow activation t active configuration
  have hc := prepare_projections_eq_of_current i activation active configuration hcurrent
  apply finishFollower_congr_of_temporal_reads _ _ view observation
  · exact hl.2.1.trans hr.2.1.symm
  · exact hl.2.2.2.trans hr.2.2.2.symm
  · exact hl.2.2.1.trans hr.2.2.1.symm
  · exact congrArg Prod.fst hc
  · exact congrArg Prod.snd hc
  · rw [hl.1, hr.1, hl.2.2.1, hr.2.2.1]
    exact hcurrent
  · intro j hj
    rw [hl.1, hr.1]
    apply hpast j
    rwa [hl.2.2.1] at hj

/-- A fold entry lies in the requested half-open interval, including intervals
whose exclusive endpoint is the terminal horizon. -/
theorem calendarEntries_interval_bounds
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (entry : ReferenceActivePhysicalHorizon.CalendarEntry p start)
    (hentry : entry ∈ ReferenceActivePhysicalHorizon.calendarEntries start start count (le_refl start) hspan) :
    start ≤ entry.val ∧ entry.val < start + count := by
  have hm : entry.val ∈
      (ReferenceActivePhysicalHorizon.calendarEntries start start count (le_refl start) hspan).unattach :=
    List.mem_map.mpr ⟨entry, hentry, rfl⟩
  rw [ReferenceActivePhysicalHorizon.calendarEntries_time_values] at hm
  change entry.val ∈ List.range' start count 1 at hm
  obtain ⟨offset, hoffset, heq⟩ := List.mem_range'.mp hm
  constructor <;> omega

/-- Interval controls and the pre-start proposal scalars supply exactly the
one-step historical proposal agreement at each member of a nonempty interval.
No pre-start non-proposal controls are compared. -/
theorem past_prop_eq_of_interval_reads
    (start count : ℕ) (time : Fin p.T)
    (htime : start ≤ time.val ∧ time.val < start + count)
    (hcontrols : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count → row.2 j = otherRow.2 j)
    (hbefore : 0 < count → ∀ j : Fin p.T, j.val < start →
      (row.2 j).1 ContinuousControlSlice.Label.prop =
        (otherRow.2 j).1 ContinuousControlSlice.Label.prop) :
    ∀ j : Fin p.T, j.val < time.val →
      (row.2 j).1 ContinuousControlSlice.Label.prop =
        (otherRow.2 j).1 ContinuousControlSlice.Label.prop := by
  intro j hj
  by_cases hpre : j.val < start
  · exact hbefore (by omega) j hpre
  · exact congrArg (fun control => control.1 ContinuousControlSlice.Label.prop)
      (hcontrols j (by omega) (by omega))

/-- Empty existing runs require no agreement on any row coordinate or reward.
The initial state is fixed and the original all-active typing input is explicit. -/
theorem run_zero_eq
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards otherRewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start : ℕ) (hspan : start + 0 ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start 0 hspan hmode).finalState =
        (ReferenceActivePhysicalHorizon.run initial otherRows selected otherRewards start 0 hspan hmode).finalState ∧
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start 0 hspan hmode).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence =
        (ReferenceActivePhysicalHorizon.run initial otherRows selected otherRewards start 0 hspan hmode).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
  rw [ReferenceActivePhysicalHorizon.run_zero_final, ReferenceActivePhysicalHorizon.run_zero_final,
    ReferenceActivePhysicalHorizon.run_zero_records, ReferenceActivePhysicalHorizon.run_zero_records]
  exact ⟨rfl, rfl⟩

/-- The UP adapter retains the carried ledger/bank and current control only. -/
theorem upReceptionInput_eq_of_current
    (inputs : ReferenceUpReception.ReceptionLocalInputs rate)
    (hcurrent : row.2 t = otherRow.2 t) :
    ReferenceUpReception.receptionInputAtRow rate row inputs t =
      ReferenceUpReception.receptionInputAtRow rate otherRow inputs t := by
  unfold ReferenceUpReception.receptionInputAtRow CoordinatorUpMeasurability.receptionInputAtRow
  rw [hcurrent]

/-- The external alignment arguments do not add reads to the checked offer. -/
theorem currentOfferWord_eq_canonical
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (declaredRow : CompletePublicTable.CompleteRow p) (follower : Fin (p.m - 1))
    (time : Fin p.T) (hrow : prepared.row = declaredRow)
    (hfollower : prepared.follower = follower) (htime : prepared.time = time) :
    ReferenceUpReception.currentOfferWord rate declaredRow follower time prepared hrow hfollower htime =
      ReferenceUpReception.currentOfferWord rate prepared.row prepared.follower prepared.time prepared rfl rfl rfl := rfl

/-- The prepared sender's full checked UP word is preserved by its computed
configuration, player, activation, time and current control slice. -/
theorem currentOfferWord_eq_of_current
    (left right : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hfollower : left.follower = right.follower)
    (hactivation : left.activation = right.activation)
    (htime : left.time = right.time)
    (hconfiguration : left.configuration = right.configuration)
    (hcurrent : left.row.2 left.time = right.row.2 right.time) :
    ReferenceUpReception.currentOfferWord rate left.row left.follower left.time left rfl rfl rfl =
      ReferenceUpReception.currentOfferWord rate right.row right.follower right.time right rfl rfl rfl := by
  rcases left with ⟨i, row, activation, time, active, arm, configuration⟩
  rcases right with ⟨otherI, otherRow, otherActivation, otherTime, otherActive, otherArm, otherConfiguration⟩
  dsimp only at hfollower hactivation htime hconfiguration hcurrent
  cases hfollower
  cases hactivation
  cases htime
  cases hconfiguration
  cases configuration with
  | dagger => rfl
  | ordinary state memory =>
      simp only [ReferenceUpReception.currentOfferWord,
        checkedUpOffer_eq_of_current i activation state hcurrent]

/-- The literal filtered UP receiver and its raw wrong-unique flag depend on
current controls and the computed prepared sender fields. The original ledger,
bank and observation are carried in `inputs`, and all alignment inputs are
listed explicitly. No valid-input or decoder-success premise is used. -/
theorem filteredUp_eq_of_current
    (inputs : ReferenceUpReception.ReceptionLocalInputs rate)
    (left right : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hleftRow : left.row = row) (hrightRow : right.row = otherRow)
    (hleftFollower : left.follower =
      (ReferenceUpReception.receptionInputAtRow rate row inputs t).selectedFollower)
    (hrightFollower : right.follower =
      (ReferenceUpReception.receptionInputAtRow rate otherRow inputs t).selectedFollower)
    (hleftTime : left.time = (ReferenceUpReception.receptionInputAtRow rate row inputs t).time)
    (hrightTime : right.time = (ReferenceUpReception.receptionInputAtRow rate otherRow inputs t).time)
    (hinputTime : inputs.2.2.1 = t)
    (hactivation : left.activation = right.activation)
    (hconfiguration : left.configuration = right.configuration)
    (hcurrent : row.2 t = otherRow.2 t) :
    ReferenceUpReception.receiveUpFilteredAtRow rate row inputs t left
        hleftRow hleftFollower hleftTime hinputTime =
      ReferenceUpReception.receiveUpFilteredAtRow rate otherRow inputs t right
        hrightRow hrightFollower hrightTime hinputTime ∧
    ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate row inputs t left
        hleftRow hleftFollower hleftTime hinputTime =
      ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate otherRow inputs t right
        hrightRow hrightFollower hrightTime hinputTime := by
  have hi := upReceptionInput_eq_of_current (rate := rate) inputs hcurrent
  have htLeft : left.time = t := hleftTime.trans hinputTime
  have htRight : right.time = t := hrightTime.trans hinputTime
  have hs : left.follower = right.follower :=
    hleftFollower.trans ((congrArg CoordinatorUpReception.ReceptionInput.selectedFollower hi).trans
      hrightFollower.symm)
  have hc : left.row.2 left.time = right.row.2 right.time := by
    rw [hleftRow, hrightRow, htLeft, htRight]
    exact hcurrent
  have hw := currentOfferWord_eq_of_current left right hs hactivation
    (htLeft.trans htRight.symm) hconfiguration hc
  constructor
  · simp only [ReferenceUpReception.receiveUpFilteredAtRow,
      currentOfferWord_eq_canonical, hi, hw]
  · simp only [ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow,
      currentOfferWord_eq_canonical, hi, hw]
    cases (CoordinatorUpReception.decoderTransition
      (ReferenceUpReception.receptionInputAtRow rate otherRow inputs t)).2 with
    | none => rfl
    | some word => rfl

end Bandits.Support.ReferenceActiveTemporalCausality

end
