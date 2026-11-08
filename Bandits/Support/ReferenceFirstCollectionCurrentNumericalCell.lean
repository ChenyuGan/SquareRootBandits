/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentPhysicalConditionalLaw
public import Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix

/-!
# The optional numerical cell of the original first collection invocation

The observations below read the existing complete physical history. Absence of
an observation is distinct from a present observation with no recorded arm.
These are internal deterministic and measurability results, not a recording
law or a statement about common queues.

Sources: `sources/zip4/manuscript/05_binary_transport.tex:352-431`,
`06_interruptions.tex:355-426`, `04_slow_fast_learner.tex:140-188`, and
`appendix_a_local_protocol.tex:28-79` in the same manuscript directory.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionCurrentNumericalCell


variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local instance outcomeMeasurableSpace :
    MeasurableSpace (AssignmentParameterFibreKernel.Outcome p) := ⊤

local instance outcomeDiscreteMeasurableSpace :
    DiscreteMeasurableSpace (AssignmentParameterFibreKernel.Outcome p) :=
  ⟨fun _ => trivial⟩

local instance outcomeOptionMeasurableSpace :
    MeasurableSpace (Option (AssignmentParameterFibreKernel.Outcome p)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance optionalMarkerMeasurableSpace : MeasurableSpace (Option (Option (Fin p.K))) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance currentCodeMeasurableSpace : MeasurableSpace
    (Option (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate))) :=
  @LaterAssignmentStartMeasurability.optionMeasurableSpace _
    ReferenceActiveHorizonMeasurability.roundRecordCodeMeasurableSpace

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- The literal later-live readout at the actual calendar record. -/
def currentCell (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Option (RecordedQueueRun.RoundInput p.K) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).bind
    (fun r => ReferenceLaterLiveNumericalReadout.laterLiveReadout (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r)

/-- Erase only the propositional certificates of the same optional cell. -/
def currentCoordinates (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :=
  (currentCell rate rewards C_star C_h t z).map ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates

/-- Keep the absent-cell and present-without-marker cases separate. -/
def currentMarker (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :=
  (currentCell rate rewards C_star C_h t z).map (fun c => c.recordedArm)

/-- Pair the numerical observation with the full error-bearing physical output. -/
def jointCurrent (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :=
  (currentCoordinates rate rewards C_star C_h t z,
    ReferenceFirstCollectionCurrentPhysicalConditionalLaw.physicalCurrent rate rewards C_star C_h control0 t z)

private theorem preparation_eq (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate) :
    r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
  rw [r.output_eq]
  rfl

/-- Membership supplies one original index, record, and actual prechoice parameter. -/
theorem firstCell_record (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) :
    ∃ (n : ℕ) (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate) (theta : ReferenceFirstCollectionSamplerCall.Theta p),
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[n]? = some r ∧
      r.input.time = t ∧ ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta) ∧
      r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.rewards = rewards ∧
      ∀ j < n, ∀ q, (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j]? = some q →
        ReferenceLaterSamplerParameterMeasurability.parameters? q.input = none := by
  classical
  obtain ⟨⟨u', t', theta⟩, hfirst, heq⟩ := Option.map_eq_some_iff.mp hz
  have hu : u' = u := congrArg Prod.fst heq
  have ht : t' = t := congrArg Prod.snd heq
  subst u'
  subst t'
  obtain ⟨n, r, hr, ht, hc, hearlier⟩ :=
    (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec rewards C_star C_h z u t theta).mp hfirst
  have htime := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time rate z rewards C_star C_h n r hr
  rw [ht] at htime
  have hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val := by omega
  have hindex : t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = n := by omega
  have har : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r := by
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hs, hindex]
    exact hr
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t z r har
  exact ⟨n, r, theta, hr, ht, har, hc, hf.1, hf.2.1, hf.2.2.2, hearlier⟩

/-- A collection input is strictly beyond the first live prefix of this same run. -/
theorem collection_after_firstLive (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[n]? = some r)
    (old : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hcoord : r.input.state.coordinator = .collection old ledger saved) :
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).length < n := by
  classical
  have hn := (List.getElem?_eq_some_iff.mp hr).1
  let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length := ⟨n, hn⟩
  have hget : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get k = r :=
    (List.getElem?_eq_some_iff.mp hr).2
  obtain ⟨hc, span, hrecord⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h z k
  rw [hget] at hrecord
  dsimp only [k] at span hrecord
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h hc
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch rate z rewards C_star C_h initial
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate z rewards C_star C_h hc)
  have hseed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
    intro i state memory hi
    have he := (seed.configuration i).symm.trans hi
    cases he
    exact ⟨seed.unoccupied i, seed.lastDown_none i⟩
  by_contra hnot
  have hstate := ReferenceFirstLiveConfirmationHistory.run_firstLive_prefix_state
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    s (p.T - s) (by omega) seed.activeAtStart seed.coordinatorFirst hseed
    n (by rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] at hn; omega) (by
      rw [← hrecords]
      exact Nat.le_of_not_gt hnot)
  have he : r.input.state = (ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s n
      (by omega) seed.activeAtStart).finalState := by
    rw [hrecord]
    rfl
  rw [ReferenceFirstLiveConfirmationHistory.FirstLiveState, ← he, hcoord] at hstate
  exact hstate

private theorem takeWhile_first_false {A : Type*} (f : A → Bool)
    (xs : List A) (n : ℕ) (r : A) (hr : xs[n]? = some r)
    (hfalse : f r = false)
    (hearlier : ∀ j < n, ∀ q, xs[j]? = some q → f q = true) :
    (xs.takeWhile f).length = n := by
  induction xs generalizing n with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at hr
  | cons head rest ih =>
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
          subst r
          simp only [List.takeWhile_cons, hfalse, Bool.false_eq_true,
            ↓reduceIte, List.length_nil]
      | succ n =>
          have hh : f head = true := hearlier 0 (by omega) head rfl
          have ht := ih n (by simpa only [List.getElem?_cons_succ] using hr)
            (fun j hj q hq => hearlier (j + 1) (by omega) q
              (by simpa only [List.getElem?_cons_succ] using hq))
          simpa only [List.takeWhile_cons, hh, ↓reduceIte, List.length_cons]
            using congrArg Nat.succ ht

/-- The actual first successful collection choice is the original window endpoint. -/
theorem firstCall_replacement_index (z : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate) (u : Fin p.T) (theta : ReferenceFirstCollectionSamplerCall.Theta p)
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[n]? = some r)
    (hcall : ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta))
    (hearlier : ∀ j < n, ∀ q,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[j]? = some q →
      ReferenceLaterSamplerParameterMeasurability.parameters? q.input = none)
    (hchosen : ReferenceCollectionPhaseHistory.laterChosen r.input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    n = w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  obtain ⟨old, ledger, saved, hcoord, _⟩ := (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcall
  have hwn : w < n := collection_after_firstLive rate rewards C_star C_h z n r hr
    old ledger saved hcoord
  have hn : n < R.length := (List.getElem?_eq_some_iff.mp hr).1
  let tail := R.drop (w + 1)
  have htail : tail[n - (w + 1)]? = some r := by
    simpa only [tail, List.getElem?_drop, Nat.add_sub_of_le (by omega : w + 1 ≤ n)] using hr
  have hscan : (tail.takeWhile fun q =>
      !ReferenceCollectionPhaseHistory.laterChosen q.input).length = n - (w + 1) := by
    apply takeWhile_first_false _ tail _ r htail
    · simp only [hchosen, Bool.not_true]
    · intro j hj q hq
      have hg : R[w + 1 + j]? = some q := by
        simpa only [tail, List.getElem?_drop] using hq
      have hnone := hearlier (w + 1 + j) (by omega) q hg
      change ReferenceLaterAssignmentFibreStep.parameters? q.input = none at hnone
      have hfalse : ReferenceCollectionPhaseHistory.laterChosen q.input = false := by
        cases hb : ReferenceCollectionPhaseHistory.laterChosen q.input with
        | false => rfl
        | true =>
            have hp := ReferenceFirstCollectionRenewalRecordingFeedback.laterChosen_parameters_present q.input hb
            rw [hnone] at hp
            cases hp
      simp only [hfalse, Bool.not_false]
  have hhead : ((R.drop w).take 1).length = 1 := by
    simp only [List.length_take, List.length_drop]
    omega
  have hwindow : (ReferenceCollectionPhaseHistory.collectionWindow R w).length =
      1 + (n - (w + 1)) := by
    simp only [ReferenceCollectionPhaseHistory.collectionWindow, List.length_append, hhead]
    exact congrArg (1 + ·) hscan
  change n = w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  omega


/-- The first invocation retains its actual failure alternatives. On an actual
later choice the original record supplies the new numerical input and the
current follower logs, without any hypothesis about the observation tail. -/
theorem firstCell_realization (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    ∃ (n : ℕ) (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
      (theta : ReferenceFirstCollectionSamplerCall.Theta p),
      R[n]? = some r ∧ r.input.time = t ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta) ∧
      r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.rewards = rewards ∧
      (match r.output.preparation.coordinator with
      | .collection _ _ _ _
          (.laterChosen _ _ started _ instruction _ output _ clockData installed selection) =>
          n = v ∧ installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
          ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
            currentCell rate rewards C_star C_h t z = some cell.input ∧
            ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some cell.input ∧
            ReferenceActivePhysicalStep.selectionAt r.input installed.registers.payload
              started instruction.time installed.registers.complementWeights selection =
                some cell.selected ∧
            cell.selected.view.payload = installed.registers.payload ∧
            installed.registers.payload = output.payload ∧
            cell.selected.view.pendingAtChoice = Finset.univ ∧
            cell.selected.view.payload.sigma = r.input.time ∧
            (∀ i, (cell.states i).status = .unoccupied) ∧
            (∀ i, r.input.state.followers i =
                .ordinary (cell.states i) (cell.memories i) ∧
              ActiveFollowerLifecycle.startRound rate.eta r.input.time
                (cell.states i) (cell.memories i) = .ok (cell.states i, cell.memories i)) ∧
            cell.input.enabled = true ∧
            cell.input.rate = installed.registers.payload.rate ∧
            cell.input.reward = (fun a => ((rewards t a).val : ℝ) / (D p : ℝ)) ∧
            cell.input.recordedArm = ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
              r cell.selected.view.payload true ∧
            (∀ a, RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a =
              if cell.input.recordedArm = some a then
                Nat.floor ((D p : ℝ) * rate.eta.val *
                  (((rewards t a).val : ℝ) / (D p : ℝ)) / cell.input.rate a) else 0) ∧
            (∀ i, ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
                r cell.selected.view.payload i =
              RecordedQueueRun.quantizedArrival
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input
                (cell.selected.view.payload.assignment.assigned i)) ∧
            (∃ out, r.output.coordinator.recording = some out ∧
              ∀ a, a ∉ cell.selected.view.payload.slowSet.1 →
                ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                  (ReferenceActiveHorizonMeasurability.roundRecordCode r) a =
                  some (RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a)) ∧
            (∀ i, ∃ logged,
              ActiveFollowerLogging.checkedLogging i r.input.row (r.input.state.activations i)
                r.input.time (r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                (cell.states i) = .ok logged ∧
              (r.output.followers i).downInput = some logged ∧
              logged.buffer = (cell.states i).buffer ++
                ReferenceFollowerBufferProvenance.logEmission i r) ∧
            (∀ a, cell.input.recordedArm = some a →
              ∃ owner : Fin p.m,
                SnapshotRecordingKernel.owns p
                  (.live cell.selected.view.payload.assignment
                    (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a ∧
                (∀ other, SnapshotRecordingKernel.owns p
                  (.live cell.selected.view.payload.assignment
                    (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) other a →
                  other = owner) ∧
                r.output.preparation.arms.actions owner = a ∧
                r.gridFeedback owner = rewards r.input.time a ∧
                (r.output.ownEntries owner).2.val.val =
                  ((rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
            (∀ a, (∃! owner : Fin p.m, SnapshotRecordingKernel.owns p
                  (.live cell.selected.view.payload.assignment
                    (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a) ∧
              ((a ∉ cell.selected.view.payload.slowSet.1 ∧
                ∃ out, r.output.coordinator.recording = some out ∧
                  ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                    (ReferenceActiveHorizonMeasurability.roundRecordCode r) a =
                    some (RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a)) ∨
                ∃ i : Fin (p.m - 1), cell.selected.view.payload.assignment.assigned i = a ∧
                  (∀ j, cell.selected.view.payload.assignment.assigned j = a → j = i) ∧
                  ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
                    r cell.selected.view.payload i =
                    RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a))
      | _ => currentCell rate rewards C_star C_h t z = none) := by
  classical
  dsimp only
  obtain ⟨n, r, theta, hr, ht, har, hcall, hrows, hJ, hrew, hearlier⟩ :=
    firstCell_record rate rewards C_star C_h u t z hz
  refine ⟨n, r, theta, hr, ht, har, hcall, hrows, hJ, hrew, ?_⟩
  have hcurrent : currentCell rate rewards C_star C_h t z =
      ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r := by
    simp only [currentCell, har, Option.bind_some]
  obtain ⟨old, incomingLedger, saved, hcoord, _hcutoff, hparam⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcall
  have hp := ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch r.input
  change ReferenceLaterAssignmentFibreStep.parameters? r.input =
    ReferenceLaterAssignmentFibreStep.dispatchParameters?
      (ReferenceActivePhysicalStep.prepare r.input).coordinator at hp
  rw [← preparation_eq rate r] at hp
  change ReferenceLaterAssignmentFibreStep.parameters? r.input = some theta at hparam
  rw [hparam] at hp
  cases hcut : r.output.preparation.coordinator with
  | first outcome =>
      rw [hcut] at hp
      simp only [ReferenceLaterAssignmentFibreStep.dispatchParameters?, reduceCtorEq] at hp
  | live registers owned base outcome =>
      rw [hcut] at hp
      simp only [ReferenceLaterAssignmentFibreStep.dispatchParameters?, reduceCtorEq] at hp
  | invalidCollectionCutoff =>
      rw [hcut] at hp
      simp only [ReferenceLaterAssignmentFibreStep.dispatchParameters?, reduceCtorEq] at hp
  | dagger =>
      rw [hcut] at hp
      simp only [ReferenceLaterAssignmentFibreStep.dispatchParameters?, reduceCtorEq] at hp
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hi output hlocal clockData installed selection =>
          have hchosen : ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
            simp only [ReferenceCollectionPhaseHistory.laterChosen, ← preparation_eq rate r, hcut]
          have hindex := firstCall_replacement_index rate rewards C_star C_h z n r u theta
            hr hcall hearlier hchosen
          have seed :=
            ReferenceFirstReplacementFollowerLoggingSeed.complete_first_replacement_follower_logging_seed
              rate z rewards C_star C_h
          dsimp only at seed hindex
          rw [← hindex, hr] at seed
          dsimp only at seed
          rw [hcut] at seed
          dsimp only at seed
          obtain ⟨hinstalled, _holdSigma, _hdate, _hrows, _hselected, _hrewards,
            hsigmaVal, hfollowers⟩ := seed
          have hsigma : installed.registers.payload.sigma = r.input.time := Fin.ext hsigmaVal
          have frame := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r
          rw [hcut] at frame
          dsimp only at frame
          obtain ⟨htime, hlive, _hgrid⟩ := frame
          have heffect := CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val
            r.input.time clock ledger.pending started instruction core.clock_parameter_valid
            core.clock_registers_valid core.clock_start_time_valid hstart hi
          have hpending : started.pending = Finset.univ := heffect.2.2.2.2.2.2.1
          have hselSome : (ReferenceActivePhysicalStep.selectionAt r.input
              installed.registers.payload started instruction.time
              installed.registers.complementWeights selection).isSome = true := by
            simp [ReferenceActivePhysicalStep.selectionAt, htime]
          let selected := (ReferenceActivePhysicalStep.selectionAt r.input
            installed.registers.payload started instruction.time
            installed.registers.complementWeights selection).get hselSome
          have hsel : r.output.preparation.coordinator.selection = some selected := by
            rw [hcut]
            exact (Option.some_get _).symm
          have hview : selected.view.payload = installed.registers.payload := by
            simp [selected, ReferenceActivePhysicalStep.selectionAt, htime]
            rfl
          have hcutoff : selected.view.cutoff =
              CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u := by
            simp [selected, ReferenceActivePhysicalStep.selectionAt, htime]
          have hpend : selected.view.pendingAtChoice = Finset.univ := by
            have he : selected.view.pendingAtChoice = started.pending := by
              simp [selected, ReferenceActivePhysicalStep.selectionAt, htime]
              rfl
            exact he.trans hpending
          have hord : ReferenceLaterLiveNumericalReadout.preparedOrdinary r := by
            intro i
            obtain ⟨state, memory, logged, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc, _⟩ :=
              hfollowers i
            simp only [ReferenceLaterLiveNumericalReadout.ordinaryData, hc, Option.isSome_some]
          have hwlt := collection_after_firstLive rate rewards C_star C_h z n r hr
            old incomingLedger saved hcoord
          have hdate := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
            rate z rewards C_star C_h n r hr
          have hdomain : ReferenceLaterLiveNumericalReadout.laterLiveDomain
              (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r := by
            refine ⟨selected, hsel, ?_, ?_, hord⟩
            · rw [hview, hsigma]
              omega
            · rw [hview, hcutoff]
              exact hlive
          have hsome := (ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain _ r).mpr hdomain
          let c := (ReferenceLaterLiveNumericalReadout.laterLiveReadout
            (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r).get hsome
          have hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout
              (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r = some c :=
            (Option.some_get _).symm
          have hn := (List.getElem?_eq_some_iff.mp hr).1
          let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h).length := ⟨n, hn⟩
          have hk : (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h).get k = r := (List.getElem?_eq_some_iff.mp hr).2
          have hphysical := ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
            rate rewards C_star C_h z k c (by rw [hk]; exact hc)
          rw [hk] at hphysical
          dsimp only at hphysical
          obtain ⟨cell, hcell, henabled, _hlive, _henabled, _hrows, _hJ, _hrew,
            hmarker, _hfields, howner, _hoccupied, hunoccupied, _hlogging, hcoordinator,
            hstatus⟩ := hphysical
          rw [hcut] at hstatus
          dsimp only at hstatus
          have hselectedEq : cell.selected = selected := Option.some.inj
            (cell.selection_actual.symm.trans hsel)
          have hselectionAt : ReferenceActivePhysicalStep.selectionAt r.input
              installed.registers.payload started instruction.time
              installed.registers.complementWeights selection = some cell.selected := by
            rw [hselectedEq]
            exact (Option.some_get _).symm
          have hnumerical := ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical
            (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r c hc
          obtain ⟨_, selected', hs', hreward, hrate, hfloor⟩ := hnumerical
          have hselected' : selected' = cell.selected :=
            Option.some.inj (hs'.symm.trans cell.selection_actual)
          subst selected'
          have hcarry : ∀ i, r.input.state.followers i =
                .ordinary (cell.states i) (cell.memories i) ∧
              ActiveFollowerLifecycle.startRound rate.eta r.input.time
                (cell.states i) (cell.memories i) = .ok (cell.states i, cell.memories i) := by
            intro i
            obtain ⟨state, memory, _logged, hin, _hu, _hdomain, _hbuffer, _hdecoder, _hbatch,
              _hmass, _hsaved, _hkeys, _hgrid, _horder, _hbefore, _hold,
              hstartFollower, _hprepared, hconfiguration, _⟩ := hfollowers i
            obtain ⟨hs, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
              ((cell.ordinary i).symm.trans hconfiguration)
            rw [hs, hm]
            exact ⟨hin, hstartFollower⟩
          have hpayload : cell.selected.view.payload = installed.registers.payload := by
            rw [hselectedEq, hview]
          have hnewPayload : installed.registers.payload = output.payload := by
            rw [hinstalled]
            rfl
          refine ⟨hindex, hinstalled, cell, ?_, ?_, hselectionAt, hpayload, hnewPayload,
            ?_, ?_, hstatus, hcarry, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hcurrent, hc, hcell]
          · rw [hc, hcell]
          · rw [hselectedEq]
            exact hpend
          · rw [hselectedEq, hview]
            exact hsigma
          · rw [hcell]
            exact henabled
          · rw [hcell, hrate, hselectedEq, hview]
            rfl
          · rw [hcell, hreward, hrew, ht]
          · rw [hcell]
            exact hmarker
          · intro a
            rw [hcell, hrate]
            simpa only [hrew, ht] using hfloor a
          · intro i
            rw [hcell]
            exact hunoccupied i (hstatus i)
          · rw [hcell]
            exact hcoordinator
          · intro i
            obtain ⟨state, memory, logged, _hin, hu, _hdomain, _hbuffer, _hdecoder, _hbatch,
              _hmass, _hsaved, _hkeys, _hgrid, _horder, _hbefore, _hold,
              _hstart, _hprepared, hconfiguration, _hrow, _hi, _ht, _hactivation,
              _harm, hlog, hbuf, _hrest⟩ := hfollowers i
            have hstate : cell.states i = state := by
              have he := (cell.ordinary i).symm.trans hconfiguration
              exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj he).1
            have hown : (r.output.preparation.followers.followers i).arm =
                r.output.preparation.arms.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) :=
              _harm.symm
            have hentry : ((r.output.preparation.followers.followers i).arm,
                r.output.preparation.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
                r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
              rw [hown, preparation_eq rate r, r.output_eq]
              exact (ReferenceActivePhysicalStep.step_own_entry _ _).symm
            have hlog' : ActiveFollowerLogging.checkedLogging i r.input.row
                (r.input.state.activations i) r.input.time
                (r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                (cell.states i) = .ok logged := by
              rw [hstate]
              simpa only [hentry] using hlog
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdownInput, _⟩ := _hrest
            refine ⟨logged, hlog', ?_, ?_⟩
            · exact hdownInput
            · rw [ReferenceFirstLiveUnoccupiedEmission.logEmission_eq_logAt_unoccupied
                r cell i (hstatus i), hstate]
              simpa only [hentry] using hbuf
          · rw [hcell]
            exact howner
          · intro a
            have hall := ReferenceLaterLiveNumericalReadout.laterLiveReadout_all_arm_numerical
              rate rewards C_star C_h z k c (by rw [hk]; exact hc) a
            rw [hk] at hall
            dsimp only at hall
            obtain ⟨other, _hotherInput, hunique, hbranch⟩ := hall
            have hotherSelected : other.selected = cell.selected :=
              Option.some.inj (other.selection_actual.symm.trans cell.selection_actual)
            have hotherStates : other.states = cell.states := by
              funext i
              exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
                ((other.ordinary i).symm.trans (cell.ordinary i))).1
            rw [hotherSelected, hotherStates] at hunique hbranch
            refine ⟨hunique, ?_⟩
            rw [hcell]
            simpa only [hstatus, ite_true] using hbranch
      | continuing core snapshot hnone selection =>
          rw [hcut] at hp
          simp only [ReferenceLaterAssignmentFibreStep.dispatchParameters?,
            ReferenceLaterAssignmentFibreStep.outcomeParameters?, reduceCtorEq] at hp
      | _ =>
          rw [hcurrent]
          simp only [ReferenceLaterLiveNumericalReadout.laterLiveReadout, hcut,
            ReferenceActivePhysicalStep.DispatchCut.selection]


/-- The exact domain equivalence is asserted on the original first-call cell. -/
theorem currentCell_isSome_iff (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) :
    (currentCell rate rewards C_star C_h t z).isSome = true ↔
      ∃ r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
  classical
  obtain ⟨n, r, theta, hr, ht, har, hcall, hrows, hJ, hrew, hb⟩ :=
    firstCell_realization rate rewards C_star C_h u t z hz
  simp only [har, Option.some.injEq, exists_eq_left']
  cases hcut : r.output.preparation.coordinator with
  | first outcome =>
      rw [hcut] at hb
      simp only [hb, Option.isSome_none, Bool.false_eq_true,
        ReferenceCollectionPhaseHistory.laterChosen, ← preparation_eq rate r, hcut]
  | live registers owned base outcome =>
      rw [hcut] at hb
      simp only [hb, Option.isSome_none, Bool.false_eq_true,
        ReferenceCollectionPhaseHistory.laterChosen, ← preparation_eq rate r, hcut]
  | invalidCollectionCutoff =>
      rw [hcut] at hb
      simp only [hb, Option.isSome_none, Bool.false_eq_true,
        ReferenceCollectionPhaseHistory.laterChosen, ← preparation_eq rate r, hcut]
  | dagger =>
      rw [hcut] at hb
      simp only [hb, Option.isSome_none, Bool.false_eq_true,
        ReferenceCollectionPhaseHistory.laterChosen, ← preparation_eq rate r, hcut]
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | laterChosen core consistent started hstart instruction hi output hlocal clockData installed selection =>
          rw [hcut] at hb
          obtain ⟨_, _, cell, hcell, _⟩ := hb
          simp only [hcell, Option.isSome_some, ReferenceCollectionPhaseHistory.laterChosen,
            ← preparation_eq rate r, hcut]
      | _ =>
          rw [hcut] at hb
          simp only [hb, Option.isSome_none, Bool.false_eq_true,
            ReferenceCollectionPhaseHistory.laterChosen, ← preparation_eq rate r, hcut]

private theorem measurable_option_map {α β : Type}
    [MeasurableSpace α] [MeasurableSpace β] (f : α → β) (hf : Measurable f) :
    Measurable (fun q : Option α => q.map f) := by
  apply measurable_comap_iff.mpr
  have heq : (fun q : Option α => Equiv.optionEquivSumPUnit β (q.map f)) =
      (Sum.map f id) ∘ Equiv.optionEquivSumPUnit α := by
    funext q
    cases q <;> rfl
  change Measurable (fun q : Option α => Equiv.optionEquivSumPUnit β (q.map f))
  rw [heq]
  exact (hf.sumMap measurable_id).comp (comap_measurable _)

/-- A calendar lookup keeps the unfiltered optional entry at the original date. -/
theorem currentCoordinates_calendar (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    currentCoordinates rate rewards C_star C_h t z =
      if ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val then
        Sum.elim (fun _ : Unit => none) (fun entry => entry.2)
          (ReferenceActiveHorizonMeasurability.listObservationAt
            (ReferenceLaterLiveCalendarMeasurability.laterLiveNumericalCalendar
              rate rewards C_star C_h z)
            (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
      else none := by
  classical
  unfold currentCoordinates currentCell ReferenceSourcePrefixHistoryFiltration.actualRecord
  split_ifs with hs
  · simp only [ReferenceLaterLiveCalendarMeasurability.laterLiveNumericalCalendar,
      ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar,
      ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_map]
    cases (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[
      t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]? <;> rfl
  · rfl

/-- Normal product/Borel measurability, obtained from the existing numerical calendar. -/
theorem currentCoordinates_measurable (t : Fin p.T) :
    Measurable (currentCoordinates rate rewards C_star C_h t) := by
  classical
  have hcalendar := ReferenceLaterLiveCalendarMeasurability.measurable_laterLiveNumericalCalendar
    rate rewards C_star C_h
  have hcoords := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp
    hcalendar
  have hstart := ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
    rate rewards C_star C_h
  have hindex : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) :=
    (measurable_of_countable (fun n : ℕ => t.val - n)).comp hstart
  have hlookup : Measurable (fun q : BootstrapPrivateRoundStreams.SourceInput p × ℕ =>
      ReferenceActiveHorizonMeasurability.listObservationAt
        (ReferenceLaterLiveCalendarMeasurability.laterLiveNumericalCalendar
          rate rewards C_star C_h q.1) q.2) := by
    apply measurable_from_prod_countable_left
    intro n
    exact (measurable_pi_apply n).comp (measurable_snd.comp hcoords)
  have hentry := hlookup.comp (measurable_id.prodMk hindex)
  have hforget : Measurable (Sum.elim (fun _ : Unit =>
      (none : Option (ReferenceLaterLiveCalendarMeasurability.NumericalCoordinates (p := p))))
      (fun entry : Fin p.T × Option
        (ReferenceLaterLiveCalendarMeasurability.NumericalCoordinates (p := p)) => entry.2)) :=
    measurable_const.sumElim measurable_snd
  have hbranch := hforget.comp hentry
  have heq : currentCoordinates rate rewards C_star C_h t = fun z =>
      if ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val then
        Sum.elim (fun _ : Unit => none) (fun entry => entry.2)
          (ReferenceActiveHorizonMeasurability.listObservationAt
            (ReferenceLaterLiveCalendarMeasurability.laterLiveNumericalCalendar
              rate rewards C_star C_h z)
            (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
      else none := by
    funext z
    exact currentCoordinates_calendar rate rewards C_star C_h t z
  rw [heq]
  exact hbranch.ite (measurableSet_le hstart measurable_const) measurable_const

/-- The marker projection preserves both optional layers, including a zero-floor arm. -/
theorem currentMarker_eq_coordinates (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    currentMarker rate rewards C_star C_h t z =
      (currentCoordinates rate rewards C_star C_h t z).map (fun c => c.2.1) := by
  simp only [currentMarker, currentCoordinates, Option.map_map, Function.comp_def,
    ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates]

theorem currentMarker_measurable (t : Fin p.T) :
    Measurable (currentMarker rate rewards C_star C_h t) := by
  have hm := (measurable_option_map
    (fun c : ReferenceLaterLiveCalendarMeasurability.NumericalCoordinates (p := p) => c.2.1)
    (measurable_fst.comp measurable_snd)).comp
      (currentCoordinates_measurable rate rewards C_star C_h t)
  convert hm using 1
  funext z
  exact currentMarker_eq_coordinates rate rewards C_star C_h t z

/-- The physical component keeps every actual diagnostic even when the numerical cell is absent. -/
theorem jointCurrent_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) : Measurable (jointCurrent rate rewards C_star C_h control0 t) :=
  (currentCoordinates_measurable rate rewards C_star C_h t).prodMk
    (ReferenceFirstCollectionCurrentPhysicalConditionalLaw.physicalCurrent_measurable
      rate rewards C_star C_h control0 t)


/-- Absence of the numerical observation preserves the entire physical output. -/
theorem jointCurrent_of_none (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (h : currentCell rate rewards C_star C_h t z = none) :
    jointCurrent rate rewards C_star C_h control0 t z =
      (none, ReferenceFirstCollectionCurrentPhysicalConditionalLaw.physicalCurrent
        rate rewards C_star C_h control0 t z) := by
  simp only [jointCurrent, currentCoordinates, h, Option.map_none]

/-- A present raw cell is paired with the full physical output, including any
subsequent recording, service, decoder, or finish diagnostics. -/
theorem jointCurrent_of_some (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (c : RecordedQueueRun.RoundInput p.K)
    (h : currentCell rate rewards C_star C_h t z = some c) :
    jointCurrent rate rewards C_star C_h control0 t z =
      (some (ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates c),
        ReferenceFirstCollectionCurrentPhysicalConditionalLaw.physicalCurrent
          rate rewards C_star C_h control0 t z) := by
  simp only [jointCurrent, currentCoordinates, h, Option.map_some]

end Bandits.Support.ReferenceFirstCollectionCurrentNumericalCell

end
