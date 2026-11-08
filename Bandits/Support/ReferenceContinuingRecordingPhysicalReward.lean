/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceContinuingRecordingFastPair

import Lean.Elab.Tactic.Omega

/-!
# Continuing physical recording actions and saved rewards

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-429`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-187,329-382`, and
`sources/zip4/manuscript/06_interruptions.tex:195-233,246-295`.

This module consumes the fixed-prefix actual marker/fast-pair producer to
identify one actual DATA recorder, its action and quantized reward, and the
current unoccupied follower's emitted saved contribution. It makes no global
recording-law, queue-truth, recovery, or source-theorem closure claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceContinuingLiveSlicePreparation
open Bandits.Support.ReferenceContinuingDataCandidateLogging
open Bandits.Support.ReferenceFollowerBufferProvenance
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.SnapshotRecordingKernel
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.SparseCalendarReplay

namespace Bandits.Support.ReferenceContinuingRecordingPhysicalReward

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- The source buffer index viewed in the assignment's existing follower carrier. -/
def bufferFollowerIndex (i : Fin (p.m - 1)) : ActiveRoundActions.Follower p.m :=
  ⟨i.val, by simpa [PublicDiscreteDraws.followerCount] using i.isLt⟩

/-- The contribution carried by the actual current `logEmission` append for
one unoccupied follower and its assigned arm. This finite sum contains only
the current record's emission, never the follower's older buffer members. -/
@[expose] def actualCurrentSavedContribution
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) : ℕ :=
  SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ) rate.eta.val
    (payload.exponent (payload.assignment.assigned (bufferFollowerIndex i)))
    (payload.assignment.assigned (bufferFollowerIndex i)) (record.input.time.val + 1)
    (ReferenceFollowerBufferProvenance.logEmission i record)

/-- On the original computed prefix, the actual marker identifies its DATA
source, action, grid feedback, and typed observation. For each unoccupied
follower, the current checked emission contributes exactly the marker's
quantized reward, with zero on every nonmarker branch. -/
theorem prefix_continuing_recording_physical_reward
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hfirst : initial.coordinator = .first)
    (hseed : ∀ i, initial.followers i = .ordinary (seed i) (seedMemory i))
    (hseedUnoccupied : ∀ i, (seed i).status = .unoccupied)
    (hseedValid : ∀ i, ActiveFollowerLifecycle.localBufferValid (seed i))
    (hseedPairwise : ∀ i, (seed i).buffer.Pairwise
      (fun a b => a.calendarRound < b.calendarRound))
    (hseedTime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ start)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r
        (ReferenceContinuingDataCandidateLogging.candidateInput initial rows selected rewards start count
          hspan hmode).time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q
        (ReferenceContinuingDataCandidateLogging.candidateInput initial rows selected rewards start count
          hspan hmode).time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val
      (ReferenceContinuingDataCandidateLogging.candidateInput initial rows selected rewards start count
        hspan hmode).time r.priorClock r.clockPending = .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r
        (ReferenceContinuingDataCandidateLogging.candidateInput initial rows selected rewards start count
          hspan hmode).time)
      (ReferenceContinuingDataCandidateLogging.candidateInput initial rows selected rewards start count
        hspan hmode).row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r
        (ReferenceContinuingDataCandidateLogging.candidateInput initial rows selected rewards start count
          hspan hmode).time).payload
      d.startResult
      (ReferenceContinuingDataCandidateLogging.candidateInput initial rows selected rewards start count
        hspan hmode).time
      (ReferenceActivePhysicalStep.liveRegistersAt r
        (ReferenceContinuingDataCandidateLogging.candidateInput initial rows selected rewards start count
          hspan hmode).time).complementWeights
      (ReferenceContinuingDataCandidateLogging.candidateInput initial rows selected rewards start count
        hspan hmode).row)
    (hc : (ReferenceActivePhysicalStep.prepare
      (ReferenceContinuingDataCandidateLogging.candidateInput initial rows selected rewards start count
        hspan hmode)).coordinator =
      .live r q base (.continuingChosen d hs c a))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ i, ((ReferenceActivePhysicalStep.prepare
      (ReferenceContinuingDataCandidateLogging.candidateInput initial rows selected rewards start count
        hspan hmode)).followers.followers i).configuration =
        .ordinary (states i) (memories i))
    (henabled : (ReferenceContinuingDataCandidateLogging.candidateInput initial rows selected rewards start
      count hspan hmode).time.val + 1 < d.startResult.clock.g) :
    let x := ReferenceContinuingDataCandidateLogging.candidateInput initial rows selected rewards start
      count hspan hmode
    let W := ReferenceContinuingLiveSlicePreparation.liveSliceWeights r x.time
    let snapshot := ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot
      r q base x.time d states
    ReferenceContinuingRecordingFastPair.prefixPhysicalFastPairLaw initial rows selected rewards
        start count hspan hmode r.payload W
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid) snapshot ∧
      ∀ u : ContinuousLearningRows.TimeControl p,
        let y := ReferenceContinuingLiveSlicePreparation.inputAtControl x u
        let record := ReferenceContinuingDataCandidateLogging.candidateRecord initial rows selected
          rewards start count hspan hmode u
        let source := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
            ((y.row.2 y.time).1))
        (∀ arm : Fin p.K,
          ReferenceContinuingRecordingFastPair.candidatePhysicalMarker initial rows selected
              rewards start count hspan hmode r.payload true u = some arm →
            ∃ selected_u : ReferenceActivePhysicalStep.Selection y,
              (ReferenceActivePhysicalStep.prepare y).coordinator.selection = some selected_u ∧
              selected_u.view.payload = r.payload ∧
              selected_u.started = d.startResult ∧
              (∀ i, ((ReferenceActivePhysicalStep.prepare y).followers.followers i).configuration =
                .ordinary (states i) (memories i)) ∧
              slotDraw u.1 = dataSlot ∧
              SnapshotRecordingKernel.owns p (.live r.payload.assignment snapshot) source arm ∧
              record.output.preparation.arms.actions source = arm ∧
              record.output.preparation.feedback.feedback source = rewards x.time arm ∧
              (record.output.preparation.feedback.observations source).val.val =
                ((rewards x.time arm).val : ℝ) / (D p : ℝ) ∧
              (d.startResult.pending = ∅ →
                record.output.preparation.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
                  (ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair initial rows
                    selected rewards start count hspan hmode r.payload true W
                    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                      a.choiceInputsValid)
                    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                      a.choiceInputsValid)
                    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                      a.choiceInputsValid) u).2.1)) ∧
        ∀ i : Fin (p.m - 1), (states i).status = .unoccupied →
          ActiveFollowerLifecycle.localBufferValid (states i) ∧
          (states i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
          (∀ saved ∈ (states i).buffer, saved.calendarRound < y.time.val + 1) ∧
          (slotDraw u.1 = dataSlot →
            ∃ logged,
              ActiveFollowerLogging.checkedLogging i record.input.row
                (record.input.state.activations i) record.input.time
                (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                (states i) = .ok logged ∧
              (record.output.followers i).downInput = some logged ∧
              logged.buffer = (states i).buffer ++
                ReferenceFollowerBufferProvenance.logEmission i record ∧
              (SparseCalendarReplay.loggingTestsPass
                (ReferencePrelaunchFollower.loggingRound i record.input.row
                  (record.input.state.activations i) record.input.time
                  (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) →
                ReferenceFollowerBufferProvenance.logEmission i record =
                  [SparseCalendarReplay.recordAt (record.input.time.val + 1)
                    (ReferencePrelaunchFollower.loggingRound i record.input.row
                      (record.input.state.activations i) record.input.time
                      (record.output.ownEntries
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i)))]) ∧
              (¬ SparseCalendarReplay.loggingTestsPass
                (ReferencePrelaunchFollower.loggingRound i record.input.row
                  (record.input.state.activations i) record.input.time
                  (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) →
                ReferenceFollowerBufferProvenance.logEmission i record = [])) ∧
            actualCurrentSavedContribution record r.payload i =
              if ReferenceContinuingRecordingFastPair.candidatePhysicalMarker initial rows selected
                  rewards start count hspan hmode r.payload true u =
                    some (r.payload.assignment.assigned (bufferFollowerIndex i)) then
                Nat.floor ((D p : ℝ) * rate.eta.val *
                  (((rewards x.time
                    (r.payload.assignment.assigned (bufferFollowerIndex i))).val : ℝ) /
                    (D p : ℝ)) /
                    CanonicalRecordingRates.xi p rate.eta.val r.payload.anchor
                      (r.payload.assignment.assigned (bufferFollowerIndex i)))
              else 0 := by
  classical
  let x := ReferenceContinuingDataCandidateLogging.candidateInput initial rows selected rewards start count
    hspan hmode
  have hxTime : x.time.val = start + count := by rfl
  let W := ReferenceContinuingLiveSlicePreparation.liveSliceWeights r x.time
  let snapshot := ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot
    r q base x.time d states
  have hseedHistory : ∀ i s memory, initial.followers i = .ordinary s memory →
      s.status = .unoccupied := by
    intro i s memory hconfiguration
    have heq : DeclaredFollowerLocalRound.LocalConfiguration.ordinary
        (seed i) (seedMemory i) = .ordinary s memory :=
      Eq.trans (Eq.symm (hseed i)) hconfiguration
    rcases DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj heq with
      ⟨hstate, _⟩
    simpa [hstate] using hseedUnoccupied i
  have hhistory := ReferenceOccupiedFieldHistory.run_prefix_occupied_field_history
    initial rows selected rewards start (count + 1) hspan hmode hfirst hseedHistory count
    (by omega)
  have hliveState : x.state.coordinator = .live r q base := by
    have hdispatch : ReferenceActivePhysicalStep.dispatch x =
        .live r q base (.continuingChosen d hs c a) := by
      calc
        ReferenceActivePhysicalStep.dispatch x =
            (ReferenceActivePhysicalStep.prepare x).coordinator :=
          (ReferenceActivePhysicalStep.prepare x).coordinator_eq.symm
        _ = .live r q base (.continuingChosen d hs c a) := hc
    cases hstate : x.state.coordinator with
    | first =>
        simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch
        cases hdispatch
    | live r' q' base' =>
        simp only [ReferenceActivePhysicalStep.dispatch, hstate,
          CoordinatorRoundDispatch.dispatch] at hdispatch
        injection hdispatch with hr hq hbase hout
        subst r'
        have hqEq : q' = q := eq_of_heq hq
        subst q'
        subst base'
        rfl
    | collection payload ledger proposal =>
        by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
          cases hcollection : CoordinatorRoundDispatch.dispatch
              (.collection (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
          all_goals
            simp [ReferenceActivePhysicalStep.dispatch, hstate, hcutoff, cutoff, clock,
              hcollection] at hdispatch
            cases hdispatch
        · simp [ReferenceActivePhysicalStep.dispatch, hstate, hcutoff] at hdispatch
    | dagger => simp [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload x.state.coordinator =
      some r.payload := by
    rw [hliveState]
    rfl
  have hstoredRun : ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        (by omega) hmode).finalState.coordinator = some r.payload := by
    simpa [x, ReferenceContinuingDataCandidateLogging.candidateInput,
      ReferenceActivePhysicalHorizon.roundInputAt] using hstored
  have hcarried : ReferenceActiveDataOwnership.carriedOccupiedFields r.payload x.state := by
    have h := hhistory.1 r.payload hstoredRun
    simpa [x, ReferenceContinuingDataCandidateLogging.candidateInput,
      ReferenceActivePhysicalHorizon.roundInputAt] using h
  have hpreparedFields : ∀ i,
      ReferenceActiveDataOwnership.occupiedFields r.payload i
        ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration := by
    intro i
    exact ReferenceActiveDataOwnership.choice_occupied_fields_preserved r.payload i x.row
      (x.state.activations i) x.time (x.active i) (x.state.followers i) (hcarried i)
  have hf : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (r.payload.downRecord i) := by
    intro i hoccupied
    have hi := hpreparedFields i
    rw [ho i] at hi
    exact hi hoccupied
  have hpairLaw := ReferenceContinuingRecordingFastPair.prefix_physical_fast_pair_eq
    initial rows selected rewards start count hspan hmode seed seedMemory hfirst hseed
    hseedUnoccupied hseedValid hseedPairwise hseedTime r q base d hs c a hc states memories ho
    henabled
  refine ⟨hpairLaw, ?_⟩
  intro u
  let y := ReferenceContinuingLiveSlicePreparation.inputAtControl x u
  let record := ReferenceContinuingDataCandidateLogging.candidateRecord initial rows selected
    rewards start count hspan hmode u
  let source := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
      ((y.row.2 y.time).1))
  have hpairAt := hpairLaw u
  have hmarkerMap :
      ReferenceContinuingRecordingFastPair.candidatePhysicalMarker initial rows selected rewards
          start count hspan hmode r.payload true u =
        SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
          rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
          r.payload.anchor_pos
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid) u.1 := by
    have hfst := congrArg Prod.fst hpairAt
    simpa [ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair,
      FastRewardSliceLaw.liveRecordingFastPair] using hfst
  have hlogFacts : ∀ i, (states i).status = .unoccupied →
      ActiveFollowerLifecycle.localBufferValid (states i) ∧
      (states i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ (states i).buffer, saved.calendarRound < y.time.val + 1 := by
    intro i hunoccupied
    have hlogging := ReferenceContinuingDataCandidateLogging.continuing_data_candidate_logging
      initial rows selected rewards start count hspan hmode i (seed i) (seedMemory i)
      (hseed i) (hseedValid i) (hseedPairwise i) (hseedTime i) states memories ho hunoccupied
    rcases hlogging with ⟨hvalid, _, hpairwise, htime, _⟩
    refine ⟨hvalid, hpairwise, ?_⟩
    intro saved hsaved
    simpa [record, ReferenceContinuingDataCandidateLogging.candidateRecord, y,
        x, ReferenceContinuingDataCandidateLogging.candidateInput,
        ReferenceContinuingLiveSlicePreparation.inputAtControl_time,
        ReferenceActivePhysicalHorizon.roundInputAt, hxTime] using htime saved hsaved
  constructor
  · intro arm hactual
    have hmap : SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
        rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W r.payload.anchor_pos
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid) u.1 = some arm := hmarkerMap.symm ▸ hactual
    rcases (SnapshotRecordingKernel.recordingMap_some_iff p
      (.live r.payload.assignment snapshot) rate.eta.val rate.eta.property rate.sourceCap
      r.payload.anchor W r.payload.anchor_pos
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid) u.1 arm).mp hmap with
      ⟨hslot, hkernelAction, howns, _hmask, _hthin⟩
    have hdata : slotDraw u.1 = dataSlot := by
      simpa only [CanonicalRecordingSlice.slotFromScalar_coordinate] using hslot
    rcases ReferenceContinuingLiveSlicePreparation.data_actions_at_control
      x r q base d hs c a hc states memories ho hf u hdata with
      ⟨c_u, a_u, hctor, hactions⟩
    have hordinary := ReferenceContinuingLiveSlicePreparation.data_preparation_at_control
      x states memories ho u hdata
    let selected_u := ReferenceContinuingLiveSlicePreparation.continuingSelection
      y r q base d hs c_u a_u
    have hselected_u := ReferenceContinuingLiveSlicePreparation.continuingSelection_eq_actual
      y r q base d hs c_u a_u (by simpa [y] using hctor)
    have hphysicalData :
        ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord record r.payload source =
          ReferenceContinuingRecordingFastPair.candidatePhysicalMarker initial rows selected
            rewards start count hspan hmode r.payload true u := by
      simp [ReferenceContinuingRecordingFastPair.candidatePhysicalMarker,
        ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord, record,
        ReferenceContinuingDataCandidateLogging.candidateRecord, y, source, hdata,
        ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
        ReferenceContinuingLiveSlicePreparation.rowAtControl_time]
    have hrecordMap :
        ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord record r.payload source =
          SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
            rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
            r.payload.anchor_pos
            (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid)
            (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid)
            (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid) u.1 := hphysicalData.trans hmarkerMap
    have hmapD : SnapshotRecordingKernel.recordingMap p
        (.live r.payload.assignment snapshot) true rate.eta.val rate.eta.property
        rate.sourceCap r.payload.anchor W r.payload.anchor_pos
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid) ((y.row.2 y.time).1) = some arm := by
      simpa [snapshot, W, y, ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
        ReferenceContinuingLiveSlicePreparation.rowAtControl_time] using hmap
    refine ⟨selected_u, ?_, ?_, ?_, ?_, hdata, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [selected_u, x, ReferenceActivePhysicalStep.step] using hselected_u
    · rfl
    · rfl
    · intro i
      simpa [record, ReferenceContinuingDataCandidateLogging.candidateRecord, y, x,
        ReferenceActivePhysicalStep.step] using
        hordinary i
    · simpa [source, y, ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
        ReferenceContinuingLiveSlicePreparation.rowAtControl_time] using howns
    · have haction := hactions source
      calc
        record.output.preparation.arms.actions source =
            (ReferenceActivePhysicalStep.prepare y).arms.actions source := by
          simp [record, ReferenceContinuingDataCandidateLogging.candidateRecord, y, x,
            ReferenceActivePhysicalStep.step]
        _ = SnapshotRecordingKernel.dataAction p
              (.live r.payload.assignment snapshot) rate.eta.val rate.eta.property
              rate.sourceCap r.payload.anchor W r.payload.anchor_pos
              (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid)
              (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid)
              (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid) u.1 source := by
          simpa [y, snapshot, W, x] using haction
        _ = arm := by
          have hsource : source = CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
              (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec u.1) := by
            simp [source, y, ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
              ReferenceContinuingLiveSlicePreparation.rowAtControl_time]
          rw [hsource]
          exact hkernelAction
    · have hfeedback := ReferenceContinuingLiveSlicePreparation.data_owner_feedback_at_control
        x r q base d hs c a hc states memories ho hf u hdata arm hmapD
      simpa [record, ReferenceContinuingDataCandidateLogging.candidateRecord, y, x,
        ReferenceContinuingDataCandidateLogging.candidateInput,
        ReferenceActivePhysicalHorizon.roundInputAt,
        ReferenceActivePhysicalStep.step] using hfeedback.1
    · have hfeedback := ReferenceContinuingLiveSlicePreparation.data_owner_feedback_at_control
        x r q base d hs c a hc states memories ho hf u hdata arm hmapD
      simpa [record, ReferenceContinuingDataCandidateLogging.candidateRecord, y, x,
        ReferenceContinuingDataCandidateLogging.candidateInput,
        ReferenceActivePhysicalHorizon.roundInputAt,
        ReferenceActivePhysicalStep.step] using hfeedback.2
    · intro hpending
      have hcoord := hactions (ActiveRoundActions.coordinator p.two_le_m)
      have hdraw : (ReferenceActivePhysicalStep.prepare y).arms.actions
          (ActiveRoundActions.coordinator p.two_le_m) =
            (SnapshotRecordingKernel.fastArmDraw p rate.eta.val rate.eta.property rate.sourceCap
              r.payload.anchor W r.payload.anchor_pos
              (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid)
              (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid)
              (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid) r.payload.assignment u.1).val := by
        have hcoord' := hcoord
        simp [SnapshotRecordingKernel.dataAction, SnapshotRecordingKernel.fastArmDraw,
          snapshot, ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot,
          hpending, x, y, W] at hcoord'
        split_ifs at hcoord'
        · simpa [SnapshotRecordingKernel.fastArmDraw, x, y, W] using hcoord'
        · rename_i hnotempty
          exact False.elim (hnotempty rfl)
      simpa [record, ReferenceContinuingDataCandidateLogging.candidateRecord, y, x,
        ReferenceActivePhysicalStep.step,
        ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair] using hdraw
  · intro i hunoccupied
    rcases hlogFacts i hunoccupied with
      ⟨hvalid, hchronological, hbefore⟩
    refine ⟨hvalid, hchronological, ?_, ?_, ?_⟩
    · intro saved hsaved
      simpa [record, ReferenceContinuingDataCandidateLogging.candidateRecord, y,
        x, ReferenceContinuingDataCandidateLogging.candidateInput,
        ReferenceContinuingLiveSlicePreparation.inputAtControl_time,
        ReferenceActivePhysicalHorizon.roundInputAt, hxTime] using hbefore saved hsaved
    · intro hdata
      have hlogging := ReferenceContinuingDataCandidateLogging.continuing_data_candidate_logging
        initial rows selected rewards start count hspan hmode i (seed i) (seedMemory i)
        (hseed i) (hseedValid i) (hseedPairwise i) (hseedTime i) states memories ho hunoccupied
      rcases hlogging with ⟨_, _, _, _, hrounds⟩
      rcases hrounds u hdata with
        ⟨logged, hcheck, hdown, happend, _, _, htests, hnot, _, _⟩
      exact ⟨logged, hcheck, hdown, happend, htests, hnot⟩
    ·
      · by_cases hdata : slotDraw u.1 = dataSlot
        · rcases ReferenceContinuingLiveSlicePreparation.data_actions_at_control
            x r q base d hs c a hc states memories ho hf u hdata with
            ⟨c_u, a_u, hctor, _⟩
          have hordinary := ReferenceContinuingLiveSlicePreparation.data_preparation_at_control
            x states memories ho u hdata
          have hlogging := ReferenceContinuingDataCandidateLogging.continuing_data_candidate_logging
            initial rows selected rewards start count hspan hmode i (seed i) (seedMemory i)
            (hseed i) (hseedValid i) (hseedPairwise i) (hseedTime i) states memories ho hunoccupied
          rcases hlogging with ⟨_, _, _, _, hrounds⟩
          rcases hrounds u hdata with
            ⟨_, _, _, _, _, _, htests, hnot, _, _⟩
          let selected_u := ReferenceContinuingLiveSlicePreparation.continuingSelection
            y r q base d hs c_u a_u
          have hselected_u :=
            ReferenceContinuingLiveSlicePreparation.continuingSelection_eq_actual
              y r q base d hs c_u a_u (by simpa [y] using hctor)
          have hselectedRecord : record.output.preparation.coordinator.selection = some selected_u := by
            simpa [record, ReferenceContinuingDataCandidateLogging.candidateRecord, y,
              selected_u, x, ReferenceActivePhysicalStep.step] using hselected_u
          have hchoice :
              (record.output.preparation.followers.followers i).configuration =
                .ordinary (states i) (memories i) := by
            simpa [record, ReferenceContinuingDataCandidateLogging.candidateRecord, y, x,
              ReferenceActivePhysicalStep.step] using
              hordinary i
          have hphysicalData :
              ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord record r.payload
                source = ReferenceContinuingRecordingFastPair.candidatePhysicalMarker initial rows
                  selected rewards start count hspan hmode r.payload true u := by
            simp [ReferenceContinuingRecordingFastPair.candidatePhysicalMarker,
              ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord, record,
              ReferenceContinuingDataCandidateLogging.candidateRecord, y, source, hdata,
              ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
              ReferenceContinuingLiveSlicePreparation.rowAtControl_time]
          have hmarkerIdentity :
              ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord record r.payload
                  source =
                SnapshotRecordingKernel.recordingMap p
                  (.live r.payload.assignment snapshot) true rate.eta.val rate.eta.property
                  rate.sourceCap r.payload.anchor W r.payload.anchor_pos
                  (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                    a.choiceInputsValid)
                  (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                    a.choiceInputsValid)
                  (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                    a.choiceInputsValid) u.1 := hphysicalData.trans hmarkerMap
          have hselectedPayload : selected_u.view.payload = r.payload := by rfl
          have hassignment : selected_u.view.payload.assignment = r.payload.assignment :=
            by rfl
          let selectedSnapshot : ActiveRoundActions.Snapshot selected_u.view.payload.assignment :=
            hassignment.symm ▸ snapshot
          have hselectedSnapshot : snapshot.status i = (states i).status := by
            rfl
          have hindex : bufferFollowerIndex i = i := by
            apply Fin.ext
            rfl
          have hmarkerSelected :
              ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord record
                  selected_u.view.payload source =
                SnapshotRecordingKernel.recordingMap p
                  (.live selected_u.view.payload.assignment selectedSnapshot) true rate.eta.val
                  rate.eta.property rate.sourceCap selected_u.view.payload.anchor W
                  selected_u.view.payload.anchor_pos
                  (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                    a.choiceInputsValid)
                  (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                    a.choiceInputsValid)
                  (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                    a.choiceInputsValid) u.1 := by
            calc
              ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord record
                    selected_u.view.payload source =
                  ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord record
                    r.payload source := by rw [hselectedPayload]
              _ = SnapshotRecordingKernel.recordingMap p
                    (.live r.payload.assignment snapshot) true rate.eta.val rate.eta.property
                    rate.sourceCap r.payload.anchor W r.payload.anchor_pos
                    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                      a.choiceInputsValid)
                    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                      a.choiceInputsValid)
                    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                      a.choiceInputsValid) u.1 := hmarkerIdentity
              _ = SnapshotRecordingKernel.recordingMap p
                    (.live selected_u.view.payload.assignment selectedSnapshot) true rate.eta.val
                    rate.eta.property rate.sourceCap selected_u.view.payload.anchor W
                    selected_u.view.payload.anchor_pos
                    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                      a.choiceInputsValid)
                    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                      a.choiceInputsValid)
                    (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                      a.choiceInputsValid) u.1 := by
                cases hassignment
                rfl
          have hC := ReferenceContinuingRecordingFastPair.currentCandidateContribution_eq_physicalMarker
            record selected_u hselectedRecord i selectedSnapshot (states i) (memories i) hchoice
            hunoccupied (by cases hassignment; exact hselectedSnapshot) W
            (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid)
            (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid)
            (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid) source
              (by
                simpa [record, ReferenceContinuingDataCandidateLogging.candidateRecord, y,
                  ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
                  ReferenceContinuingLiveSlicePreparation.rowAtControl_time] using
                    hmarkerSelected)
          have hemLog : ReferenceFollowerBufferProvenance.logEmission i record =
              ReferencePrelaunchFollower.logAt i record.input.row
                (record.input.state.activations i) record.input.time
                (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
            unfold ReferenceFollowerBufferProvenance.logEmission
            simp only [hchoice]
            simp [hunoccupied]
          have hcontribution : SparseCalendarReplay.sparseBufferContribution (p.m - 1)
                (D p : ℝ) rate.eta.val
                (r.payload.exponent (r.payload.assignment.assigned (bufferFollowerIndex i)))
                (r.payload.assignment.assigned (bufferFollowerIndex i))
                (record.input.time.val + 1)
                (ReferencePrelaunchFollower.logAt i record.input.row
                  (record.input.state.activations i) record.input.time
                  (record.output.ownEntries
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i))) =
              if ReferenceContinuingRecordingFastPair.candidatePhysicalMarker initial rows selected
                  rewards start count hspan hmode r.payload true u =
                    some (r.payload.assignment.assigned (bufferFollowerIndex i)) then
                Nat.floor ((D p : ℝ) * rate.eta.val *
                  ((record.output.ownEntries
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2.val.val : ℝ) /
                  CanonicalRecordingRates.xi p rate.eta.val r.payload.anchor
                    (r.payload.assignment.assigned (bufferFollowerIndex i)))
              else 0 := by
            simpa [hindex, hselectedPayload, hphysicalData] using hC
          unfold actualCurrentSavedContribution
          rw [hemLog, hcontribution]
          by_cases hmarked :
              ReferenceContinuingRecordingFastPair.candidatePhysicalMarker initial rows selected
                rewards start count hspan hmode r.payload true u =
                  some (r.payload.assignment.assigned (bufferFollowerIndex i))
          · have hmapAssigned : SnapshotRecordingKernel.recordingMap p
                (.live r.payload.assignment snapshot) true rate.eta.val rate.eta.property
                rate.sourceCap r.payload.anchor W r.payload.anchor_pos
                (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                  a.choiceInputsValid)
                (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                  a.choiceInputsValid)
                (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                  a.choiceInputsValid) u.1 =
                  some (r.payload.assignment.assigned (bufferFollowerIndex i)) := by
              rw [← hmarkerMap]
              exact hmarked
            rcases (SnapshotRecordingKernel.recordingMap_some_iff p
              (.live r.payload.assignment snapshot) rate.eta.val rate.eta.property rate.sourceCap
              r.payload.anchor W r.payload.anchor_pos
              (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid)
              (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid)
              (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid) u.1
              (r.payload.assignment.assigned (bufferFollowerIndex i))).mp hmapAssigned with
              ⟨hslot, _, howns, _, _⟩
            have hdata' : slotDraw u.1 = dataSlot := by
              simpa only [CanonicalRecordingSlice.slotFromScalar_coordinate] using hslot
            have hplayerNe : PublicDiscreteDraws.followerPlayer p.two_le_m i ≠
                ActiveRoundActions.coordinator p.two_le_m :=
              ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
            have hplayerIndex := ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hplayerNe
            have hownsPlayer : SnapshotRecordingKernel.owns p
                (.live r.payload.assignment snapshot)
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                (r.payload.assignment.assigned (bufferFollowerIndex i)) := by
              simp [SnapshotRecordingKernel.owns, hplayerNe, hplayerIndex, hindex]
            have hsource : source = CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
                (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec u.1) := by
              simp [source, y, ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
                ReferenceContinuingLiveSlicePreparation.rowAtControl_time]
            have hownsSource : SnapshotRecordingKernel.owns p
                (.live r.payload.assignment snapshot) source
                (r.payload.assignment.assigned (bufferFollowerIndex i)) := by
              simpa [hsource] using howns
            have hsourceEq := SnapshotRecordingKernel.owns_unique p
              (.live r.payload.assignment snapshot)
              (r.payload.assignment.assigned (bufferFollowerIndex i))
              source (PublicDiscreteDraws.followerPlayer p.two_le_m i) hownsSource hownsPlayer
            have hmapAssignedD : SnapshotRecordingKernel.recordingMap p
                (.live r.payload.assignment snapshot) true rate.eta.val rate.eta.property
                rate.sourceCap r.payload.anchor W r.payload.anchor_pos
                (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                  a.choiceInputsValid)
                (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                  a.choiceInputsValid)
                (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                  a.choiceInputsValid) ((y.row.2 y.time).1) =
                  some (r.payload.assignment.assigned (bufferFollowerIndex i)) := by
              simpa [snapshot, W, y,
                ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
                ReferenceContinuingLiveSlicePreparation.rowAtControl_time] using hmapAssigned
            have hfeedback :=
              ReferenceContinuingLiveSlicePreparation.data_owner_feedback_at_control
                x r q base d hs c a hc states memories ho hf u hdata'
                (r.payload.assignment.assigned (bufferFollowerIndex i)) hmapAssignedD
            have hobservation :
                (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2.val.val =
                  ((rewards x.time
                    (r.payload.assignment.assigned (bufferFollowerIndex i))).val : ℝ) /
                    (D p : ℝ) := by
              have hfeedbackPlayer : (ReferenceActivePhysicalStep.prepare y).feedback.feedback
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
                  rewards x.time (r.payload.assignment.assigned (bufferFollowerIndex i)) := by
                have hfeedbackSource : (ReferenceActivePhysicalStep.prepare y).feedback.feedback source =
                    x.rewards x.time (r.payload.assignment.assigned (bufferFollowerIndex i)) := by
                  simpa [source, y, ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
                    ReferenceContinuingLiveSlicePreparation.inputAtControl_time,
                    ReferenceContinuingLiveSlicePreparation.rowAtControl_time] using hfeedback.1
                rw [hsourceEq] at hfeedbackSource
                simpa [x, ReferenceContinuingDataCandidateLogging.candidateInput,
                  ReferenceActivePhysicalHorizon.roundInputAt] using hfeedbackSource
              calc
                (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2.val.val =
                    (ActualInitializationPhysicalStep.observationOfGrid p
                      ((ReferenceActivePhysicalStep.prepare y).feedback.feedback
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val.val := by
                  rw [record.output_eq, ReferenceActivePhysicalStep.step_own_entry]
                  simp [record, x, y, ReferenceContinuingDataCandidateLogging.candidateRecord,
                    ReferenceActivePhysicalStep.step,
                    ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
                    ReferenceContinuingLiveSlicePreparation.rowAtControl_time]
                _ = (((ReferenceActivePhysicalStep.prepare y).feedback.feedback
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val : ℝ) /
                    (D p : ℝ) := ActualInitializationPhysicalStep.observationOfGrid_value p _
                _ = ((rewards x.time
                      (r.payload.assignment.assigned (bufferFollowerIndex i))).val : ℝ) /
                    (D p : ℝ) := by rw [hfeedbackPlayer]
            simp [hmarked, hobservation, x,
              ReferenceContinuingDataCandidateLogging.candidateInput]
          · simp [hmarked]
        · have hnotTests : ¬ SparseCalendarReplay.loggingTestsPass
              (ReferencePrelaunchFollower.loggingRound i record.input.row
                (record.input.state.activations i) record.input.time
                (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) := by
            intro htestsNow
            have hdata' :=
              (ReferencePrelaunchFollower.loggingTestsPass_iff i record.input.row
                (record.input.state.activations i) record.input.time
                (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))).mp
                htestsNow |>.2.1
            apply hdata
            simpa [record, ReferenceContinuingDataCandidateLogging.candidateRecord, y,
              ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
              ReferenceContinuingLiveSlicePreparation.rowAtControl_time] using hdata'
          have hempty : ReferenceFollowerBufferProvenance.logEmission i record = [] := by
            classical
            unfold ReferenceFollowerBufferProvenance.logEmission
            cases hconfiguration :
                (record.output.preparation.followers.followers i).configuration with
            | dagger => simp [hconfiguration]
            | ordinary state memory =>
                by_cases hstate : state.status = .unoccupied
                · simp [hconfiguration, hstate, ReferencePrelaunchFollower.logAt, hnotTests]
                · simp [hconfiguration, hstate]
          have hmarkerNone :
              ReferenceContinuingRecordingFastPair.candidatePhysicalMarker initial rows selected
                rewards start count hspan hmode r.payload true u = none := by
            simp [ReferenceContinuingRecordingFastPair.candidatePhysicalMarker,
              ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord,
              ReferenceContinuingDataCandidateLogging.candidateRecord, y, hdata,
              ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
              ReferenceContinuingLiveSlicePreparation.rowAtControl_time]
          unfold actualCurrentSavedContribution
          rw [hempty, hmarkerNone]
          simp [SparseCalendarReplay.sparseBufferContribution]

/-- Actual-launch specialization using the original source arrays, selected row,
and the launch replay's seed witness. The result remains conditional on the
same continuing-live execution telescope as the fixed-prefix consumer. -/
theorem actualLaunchedBoundary_continuing_recording_physical_reward
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ i,
      ∀ hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed,
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (count : ℕ)
    (span : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      (count + 1) ≤ p.T) :
    let initial := ReferenceContinuingDataCandidateLogging.actualLaunchState source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let active := ReferenceContinuingDataCandidateLogging.actualLaunch_allActiveAtStart
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let seedWitness := fun i : Fin (p.m - 1) =>
      ReferenceContinuingDataCandidateLogging.actualLaunchSeedWitness source rewards rate
        C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    let boundary := ReferenceOccupiedFieldHistory.ofActualLaunchedBoundary_occupied_field_history
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched count span
    let x := ReferenceContinuingDataCandidateLogging.candidateInput initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count span active
    ∀ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
      (base : Fin (p.m - 1) → ℕ)
      (d : CoordinatorStartRoundCutoffDispatch.Output
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
      (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock r.clockPending =
        .ok d.startResult)
      (c : CoordinatorLiveChoiceRecorderStep.Continuation
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
      (a : CoordinatorRoundDispatch.ArmSelection
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult x.time
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
      (hc : (ReferenceActivePhysicalStep.prepare x).coordinator =
        .live r q base (.continuingChosen d hs c a))
      (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
      (ho : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
        .ordinary (states i) (memories i))
      (henabled : x.time.val + 1 < d.startResult.clock.g),
      let W := ReferenceContinuingLiveSlicePreparation.liveSliceWeights r x.time
      let snapshot := ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot r q base x.time d states
      ReferenceContinuingRecordingFastPair.prefixPhysicalFastPairLaw initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count span active
          r.payload W
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid) snapshot ∧
        ∀ u : ContinuousLearningRows.TimeControl p,
          let y := ReferenceContinuingLiveSlicePreparation.inputAtControl x u
          let record := ReferenceContinuingDataCandidateLogging.candidateRecord initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count span active u
          let recorderSource := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
            (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec ((y.row.2 y.time).1))
          (∀ arm : Fin p.K,
            ReferenceContinuingRecordingFastPair.candidatePhysicalMarker initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count span active
                r.payload true u = some arm →
              ∃ selected_u : ReferenceActivePhysicalStep.Selection y,
                (ReferenceActivePhysicalStep.prepare y).coordinator.selection = some selected_u ∧
                selected_u.view.payload = r.payload ∧ selected_u.started = d.startResult ∧
                (∀ i, ((ReferenceActivePhysicalStep.prepare y).followers.followers i).configuration =
                  .ordinary (states i) (memories i)) ∧
                slotDraw u.1 = dataSlot ∧
                SnapshotRecordingKernel.owns p (.live r.payload.assignment snapshot) recorderSource arm ∧
                record.output.preparation.arms.actions recorderSource = arm ∧
                record.output.preparation.feedback.feedback recorderSource = rewards x.time arm ∧
                (record.output.preparation.feedback.observations recorderSource).val.val =
                  ((rewards x.time arm).val : ℝ) / (D p : ℝ) ∧
                (d.startResult.pending = ∅ →
                  record.output.preparation.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
                    (ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair initial source.1.2
                      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count span
                      active r.payload true W
                      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                        a.choiceInputsValid)
                      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                        a.choiceInputsValid)
                      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                        a.choiceInputsValid) u).2.1)) ∧
          ∀ i : Fin (p.m - 1), (states i).status = .unoccupied →
            ActiveFollowerLifecycle.localBufferValid (states i) ∧
            (states i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
            (∀ saved ∈ (states i).buffer, saved.calendarRound < y.time.val + 1) ∧
            (slotDraw u.1 = dataSlot →
              ∃ logged,
                ActiveFollowerLogging.checkedLogging i record.input.row
                  (record.input.state.activations i) record.input.time
                  (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                  (states i) = .ok logged ∧
                (record.output.followers i).downInput = some logged ∧
                logged.buffer = (states i).buffer ++
                  ReferenceFollowerBufferProvenance.logEmission i record ∧
                (SparseCalendarReplay.loggingTestsPass
                  (ReferencePrelaunchFollower.loggingRound i record.input.row
                    (record.input.state.activations i) record.input.time
                    (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) →
                  ReferenceFollowerBufferProvenance.logEmission i record =
                    [SparseCalendarReplay.recordAt (record.input.time.val + 1)
                      (ReferencePrelaunchFollower.loggingRound i record.input.row
                        (record.input.state.activations i) record.input.time
                        (record.output.ownEntries
                          (PublicDiscreteDraws.followerPlayer p.two_le_m i)))]) ∧
                (¬ SparseCalendarReplay.loggingTestsPass
                  (ReferencePrelaunchFollower.loggingRound i record.input.row
                    (record.input.state.activations i) record.input.time
                    (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) →
                  ReferenceFollowerBufferProvenance.logEmission i record = [])) ∧
              actualCurrentSavedContribution record r.payload i =
                if ReferenceContinuingRecordingFastPair.candidatePhysicalMarker initial source.1.2
                    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count span
                    active r.payload true u =
                      some (r.payload.assignment.assigned (bufferFollowerIndex i)) then
                  Nat.floor ((D p : ℝ) * rate.eta.val *
                    (((rewards x.time
                      (r.payload.assignment.assigned (bufferFollowerIndex i))).val : ℝ) / (D p : ℝ)) /
                    CanonicalRecordingRates.xi p rate.eta.val r.payload.anchor
                      (r.payload.assignment.assigned (bufferFollowerIndex i)))
                else 0 := by
  classical
  have hsourcePair :=
    ReferenceContinuingRecordingFastPair.actualLaunchedBoundary_physical_fast_pair_eq
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched count span
  intro initial start active seedWitness boundary x r q base d hs c a hc states memories ho henabled
  have hseedUnoccupied : ∀ i, (seedWitness i).state.status = .unoccupied := by
    intro i
    obtain ⟨state, memory, hordinary, _, hunoccupied⟩ := boundary.2.1 i
    have hstate : state = (seedWitness i).state :=
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hordinary.symm.trans (seedWitness i).ordinary)).1
    simpa [hstate] using hunoccupied
  have hlaunchPair := hsourcePair r q base d hs c a hc states memories ho henabled
  have hgeneric := prefix_continuing_recording_physical_reward
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count span active
    (fun i => (seedWitness i).state) (fun i => (seedWitness i).memory)
    boundary.1 (fun i => (seedWitness i).ordinary) hseedUnoccupied
    (fun i => (seedWitness i).valid) (fun i => (seedWitness i).pairwise)
    (fun i saved hsaved => (seedWitness i).saved_before_start saved hsaved)
    r q base d hs c a hc states memories ho henabled
  exact ⟨hlaunchPair, hgeneric.2⟩

end Bandits.Support.ReferenceContinuingRecordingPhysicalReward

end
