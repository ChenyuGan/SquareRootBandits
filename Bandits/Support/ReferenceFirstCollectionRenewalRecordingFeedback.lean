/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalNumericalServiceJoin
public import Bandits.Support.ReferenceFirstReplacementFollowerLoggingSeed

/-!
# Actual first-renewal recording and table feedback

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-70,246-299,399-423`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The first prechoice call is aligned with the first successful replacement
in the original physical suffix. The retained OLD follower reply is never
identified with the newly installed DOWN word. All statements are internal
physical recording results, not manuscript or regret closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalRecordingFeedback

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem selected_parameters_present
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hrec : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out) :
    (LaterAssignmentStartMeasurability.selectedSamplerParameters? old
      ⟨ledger, instruction, consistent⟩).isSome = true := by
  rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match]
  have hpair : (⟨AssignmentScoreReconstruction.reconstructLaterStart ledger instruction, rfl⟩ :
      LaterAssignmentStartOperation.ReconstructionCall old ledger instruction) =
      ⟨.success ledger instruction out, hrec⟩ := by
    apply LaterAssignmentStartOperation.ReconstructionCall.ext
    exact hrec
  unfold LaterAssignmentStartOperation.decideReconstruction
  rw [hpair]
  rfl

/-- A successful physical replacement exposes a present prechoice selector.
This reads the public dispatch characterization, including its reconstruction
call, rather than assuming equality with a separate sampler witness. -/
theorem laterChosen_parameters_present
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (h : ReferenceCollectionPhaseHistory.laterChosen x = true) :
    (ReferenceLaterAssignmentFibreStep.parameters? x).isSome = true := by
  have hp := ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch x
  change ReferenceLaterAssignmentFibreStep.parameters? x =
    ReferenceLaterAssignmentFibreStep.dispatchParameters?
      (ReferenceActivePhysicalStep.prepare x).coordinator at hp
  cases he : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [ReferenceCollectionPhaseHistory.laterChosen, he,
        Bool.false_eq_true] at h
      rename_i core consistent started hstart instruction hi output hlocal clockData installed selection
      rw [he] at hp
      rw [hp]
      simp only [ReferenceLaterAssignmentFibreStep.dispatchParameters?,
        ReferenceLaterAssignmentFibreStep.outcomeParameters?]
      exact selected_parameters_present _ _ instruction consistent
        output.reconstruction output.reconstruction_eq
  | first outcome =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at h
  | live r q base outcome =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at h
  | invalidCollectionCutoff =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at h
  | dagger =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen, he, Bool.false_eq_true] at h

/-- A finite predicate scan ends exactly at its first false cell. -/
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
          have hhead : f head = true := hearlier 0 (by omega) head rfl
          have hrest := ih n
            (by simpa only [List.getElem?_cons_succ] using hr)
            (fun j hj q hq => hearlier (j + 1) (by omega) q
              (by simpa only [List.getElem?_cons_succ] using hq))
          simpa only [List.takeWhile_cons, hhead, ↓reduceIte, List.length_cons]
            using congrArg Nat.succ hrest

/-- Original suffix lookup fixes the physical calendar time, even in failed,
terminal and post-stop branches. -/
theorem complete_record_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (n : ℕ) (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
    (hr : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[n]? = some r) :
    r.input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + n := by
  have hn := (List.getElem?_eq_some_iff.mp hr).1
  rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] at hn
  have ht := congrArg (fun xs : List ℕ => xs[n]?)
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
      rate source rewards C_star C_h)
  rw [List.getElem?_map, hr] at ht
  simpa only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range' hn,
    ↓reduceIte, Nat.one_mul, Option.map_some, Option.some.injEq] using ht

/-- The actual first call's record is the literal first replacement record.
The public empty-boundary producer excludes exhausted/terminal alternatives;
the original first-call specification excludes all earlier replacements.
The successful-dispatch input is explicit local data, not an AE hypothesis. -/
theorem actual_call_first_replacement_record
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source
      rate rewards C_star C_h u t)
    (d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
      rate rewards C_star C_h u t z)
    (hchosen : ReferenceCollectionPhaseHistory.laterChosen d.record.input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z.val rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    R[v]? = some d.record := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z.val rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h
  obtain ⟨n, r, hr, ht, _hcall, hearlier⟩ :=
    (ReferenceFirstCollectionSamplerCall.firstCollectionCall_spec rewards C_star C_h z.val u t
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
        rate rewards C_star C_h u t z)).mp
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.firstCollectionCall_eq
        rate rewards C_star C_h u t z)
  obtain ⟨j, hd⟩ := List.mem_iff_getElem?.mp d.record_mem
  have hnTime := complete_record_time rate z.val rewards C_star C_h n r hr
  have hjTime := complete_record_time rate z.val rewards C_star C_h j d.record hd
  rw [ht] at hnTime
  rw [d.time_eq] at hjTime
  have hj : j = n := by omega
  subst j
  have heq : r = d.record := Option.some.inj (hr.symm.trans hd)
  subst r
  have hn : n < R.length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨hc, hs, _hk, f, _e, _houtcome, _hnext, _hp, _hl, _hsaved, htime⟩ :=
    ReferenceFirstCollectionRenewalCallFirstEmptyBoundary.actual_renewal_call_first_empty_boundary
      rate rewards C_star C_h u t z d
  have hrecords : R =
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z.val rewards C_star C_h hc (p.T - s) hs).records := by
    exact ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z.val rewards C_star C_h
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate z.val rewards C_star C_h hc) (Option.some_get _).symm
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  have hwn : w < n := by
    have hpos := f.stream.positiveLength
    change s + (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z.val rewards C_star C_h hc (p.T - s) hs).records).length +
      f.stream.ell = t.val at htime
    rw [← hrecords] at htime
    change s + w + f.stream.ell = t.val at htime
    change t.val = s + n at hnTime
    omega
  let tail := R.drop (w + 1)
  have htail : tail[n - (w + 1)]? = some d.record := by
    simpa only [tail, List.getElem?_drop, Nat.add_sub_of_le (by omega : w + 1 ≤ n)]
      using hr
  have hscan : (tail.takeWhile fun q =>
      !ReferenceCollectionPhaseHistory.laterChosen q.input).length = n - (w + 1) := by
    apply takeWhile_first_false _ tail _ d.record htail
    · simp only [hchosen, Bool.not_true]
    · intro k hk q hq
      have hget : R[w + 1 + k]? = some q := by
        simpa only [tail, List.getElem?_drop] using hq
      have hnone := hearlier (w + 1 + k) (by omega) q hget
      change ReferenceLaterAssignmentFibreStep.parameters? q.input = none at hnone
      have hfalse : ReferenceCollectionPhaseHistory.laterChosen q.input = false := by
        cases hb : ReferenceCollectionPhaseHistory.laterChosen q.input with
        | false => rfl
        | true =>
            have hpresent := laterChosen_parameters_present q.input hb
            rw [hnone] at hpresent
            cases hpresent
      simp only [hfalse, Bool.not_false]
  have hhead : ((R.drop w).take 1).length = 1 := by
    simp only [List.length_take, List.length_drop]
    omega
  have hwindow : (ReferenceCollectionPhaseHistory.collectionWindow R w).length =
      1 + (n - (w + 1)) := by
    simp only [ReferenceCollectionPhaseHistory.collectionWindow, List.length_append, hhead]
    exact congrArg (1 + ·) hscan
  change R[w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length]? = some d.record
  have hv : w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length = n := by omega
  rw [hv]
  exact hr

section ActualDispatch

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source
      rate rewards C_star C_h u t)
    (d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
      rate rewards C_star C_h u t z)

variable (consistent : LaterAssignmentStartOperation.LocalConsistency d.old
      (CoordinatorRoundDispatch.collectionOperationLedger
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
        rate u d.record.input d.old d.ledger d.saved) d.core.payload_n_eq))
    (output : LaterAssignmentStartOperation.SuccessfulStart d.old
      (CoordinatorRoundDispatch.collectionOperationLedger
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
        rate u d.record.input d.old d.ledger d.saved) d.core.payload_n_eq) d.instruction d.record.input.row)
    (hlocal : output.localConsistency = consistent)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
    (installed : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData)
    (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      d.started d.instruction.time installed.registers.complementWeights d.record.input.row)

/-- Pointwise ordinary-state production on the explicit actual call and
successful dispatch. Every local state comes from the original replacement
logging seed at the record just identified above. The OLD reply alternative
is not used to manufacture occupied fields for the NEW assignment. -/
theorem actual_call_prepared_followers
    (hcut : (ReferenceActivePhysicalStep.prepare d.record.input).coordinator =
      .collection d.old d.ledger (ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u) u
        (.laterChosen d.core consistent d.started d.clock_eq d.instruction
          d.instruction_eq output hlocal clockData installed selection)) :
    installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
    d.record.input.rows = z.val.1.2 ∧
    d.record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z.val ∧
    d.record.input.rewards = rewards ∧
    ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      ∀ i, d.record.input.state.followers i = .ordinary (states i) (memories i) ∧
        (states i).status = .unoccupied ∧
        ((ReferenceActivePhysicalStep.prepare d.record.input).followers.followers i).configuration =
          .ordinary (states i) (memories i) := by
  classical
  have hchosen : ReferenceCollectionPhaseHistory.laterChosen d.record.input = true := by
    simp only [ReferenceCollectionPhaseHistory.laterChosen, hcut]
  have hrecord := actual_call_first_replacement_record rate rewards C_star C_h u t z d hchosen
  have seed := ReferenceFirstReplacementFollowerLoggingSeed.complete_first_replacement_follower_logging_seed
    rate z.val rewards C_star C_h
  dsimp only at seed hrecord
  rw [hrecord] at seed
  dsimp only at seed
  have hprepare : d.record.output.preparation = ReferenceActivePhysicalStep.prepare d.record.input := by
    rw [d.record.output_eq]
    rfl
  rw [hprepare, hcut] at seed
  dsimp only at seed
  obtain ⟨hinstalled, _holdSigma, _htime, hrows, hselected, hrewards, _hsigma, hfollowers⟩ := seed
  refine ⟨hinstalled, hrows, hselected, hrewards, ?_⟩
  have hex : ∀ i : Fin (p.m - 1),
      ∃ old memory, d.record.input.state.followers i = .ordinary old memory ∧
        old.status = .unoccupied ∧
        ((ReferenceActivePhysicalStep.prepare d.record.input).followers.followers i).configuration =
          .ordinary old memory := by
    intro i
    obtain ⟨old, memory, _logged, hin, hu, _hdomain, _hbuffer, _hdecoder, _hbatch,
      _hmass, _hsaved, _hkeys, _hgrid, _horder, _hbefore, _hold,
      _hstart, _hprepared, hconfiguration, _hrest⟩ := hfollowers i
    exact ⟨old, memory, hin, hu, hconfiguration⟩
  choose states memories hs using hex
  exact ⟨states, memories, hs⟩

/-- A successful literal gate has the DATA/source/ownership/mask tests and
its actual played arm. In particular an enabled zero observation cannot be
confused with the ordinary no-gate output. -/
private theorem run_gate_facts
    {eta : ReferencePrelaunchFollower.LearningRate}
    {payload : AssignmentStartPayload.Input p eta}
    (I : CoordinatorRecorderComplementBridge.Input payload)
    (valid : CoordinatorRecorderComplementBridge.LocalInputsValid I)
    (recording : CoordinatorRecordingOperation.Output p)
    (hrun : CoordinatorRecorderComplementBridge.run I = some recording)
    (j : Fin p.K) (hgate : recording.gateArm = some j) :
    CoordinatorRecorderComplementBridge.selectedSlot I = PublicDiscreteDraws.dataSlot ∧
    CoordinatorRecorderComplementBridge.selectedRecorder I =
      ActiveRoundActions.coordinator p.two_le_m ∧
    ¬ CoordinatorRecorderComplementBridge.isFrozen I ∧
    CoordinatorRecorderComplementBridge.ownsArm I ∧
    CoordinatorRecorderComplementBridge.ownMaskPasses I ∧ j = I.ownArm := by
  classical
  have hnonzero : recording ≠ CoordinatorRecordingOperation.zeroOutput p := by
    intro he
    rw [he] at hgate
    cases hgate
  have hnotzero : CoordinatorRecorderComplementBridge.run I ≠
      some (CoordinatorRecordingOperation.zeroOutput p) := by
    intro he
    exact hnonzero (Option.some.inj (hrun.symm.trans he))
  have hd : CoordinatorRecorderComplementBridge.selectedSlot I = PublicDiscreteDraws.dataSlot := by
    by_contra hn
    exact hnotzero (CoordinatorRecorderComplementBridge.run_zero_of_not_data I valid hn)
  have hs : CoordinatorRecorderComplementBridge.selectedRecorder I =
      ActiveRoundActions.coordinator p.two_le_m := by
    by_contra hn
    exact hnotzero (CoordinatorRecorderComplementBridge.run_zero_of_other_source I valid hd hn)
  have hf : ¬ CoordinatorRecorderComplementBridge.isFrozen I := by
    intro h
    exact hnotzero (CoordinatorRecorderComplementBridge.run_zero_of_frozen I valid hd hs h)
  have ho : CoordinatorRecorderComplementBridge.ownsArm I := by
    by_contra hn
    exact hnotzero (CoordinatorRecorderComplementBridge.run_zero_of_unowned I valid hd hs hf hn)
  have hm : CoordinatorRecorderComplementBridge.ownMaskPasses I := by
    by_contra hn
    exact hnotzero (CoordinatorRecorderComplementBridge.run_zero_of_mask_rejected I valid hd hs hf ho hn)
  have hthin : CoordinatorRecorderComplementBridge.thinScalar I ≤
      CoordinatorRecorderComplementBridge.threshold I valid := by
    by_contra hn
    exact hnotzero
      (CoordinatorRecorderComplementBridge.run_zero_of_thinning_rejected I valid hd hs hf ho hm hn)
  obtain ⟨recording', hr', hg', _⟩ :=
    CoordinatorRecorderComplementBridge.run_gate_and_floor I valid hd hs hf ho hm hthin
  have heq : recording = recording' := Option.some.inj (hrun.symm.trans hr')
  exact ⟨hd, hs, hf, ho, hm, Option.some.inj (hgate.symm.trans (heq ▸ hg'))⟩

/-- Pointwise same-witness recorder and feedback identification. The only
conditional inputs beyond the explicit actual call are its successful
dispatch, its installation's actual clock result, and this recorder's run
equation. No ordinary-state, feedback, collision, numerical truth, moment or
freshness hypothesis is supplied. The AE result below produces these inputs
from N's same witness. -/
theorem actual_call_recording_feedback
    (hcut : (ReferenceActivePhysicalStep.prepare d.record.input).coordinator =
      .collection d.old d.ledger
        (ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u) u
        (.laterChosen d.core consistent d.started d.clock_eq d.instruction
          d.instruction_eq output hlocal clockData installed selection))
    (hresult : clockData.result = d.started)
    (recording : CoordinatorRecordingOperation.Output p)
    (hrun : CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.liveRecordingInput
          (ReferenceActivePhysicalStep.prepare d.record.input) installed.registers d.started) =
      some recording) :
    installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
    ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      (∀ i, d.record.input.state.followers i = .ordinary (states i) (memories i) ∧
        (states i).status = .unoccupied ∧
        ((ReferenceActivePhysicalStep.prepare d.record.input).followers.followers i).configuration =
          .ordinary (states i) (memories i)) ∧
      CoordinatorLocalArmChoice.assignmentIsLive installed.registers.payload
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
        d.record.input.time ∧
      d.started.pending = Finset.univ ∧ d.started.clock.u = none ∧
      installed.registers.payload.sigma = t ∧
      ¬ CoordinatorRecorderComplementBridge.isFrozen
        (ReferenceActivePhysicalStep.liveRecordingInput
          (ReferenceActivePhysicalStep.prepare d.record.input) installed.registers d.started) ∧
      d.record.output.coordinator.recording = some recording ∧
      recording.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
        (AssignmentScoreReconstruction.currentWeight d.out)
        (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j))
        recording.gateArm ∧
      ∀ j, recording.gateArm = some j →
        PublicDiscreteDraws.slotDraw (d.record.input.row.2 d.record.input.time).1 =
          PublicDiscreteDraws.dataSlot ∧
        PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
            (d.record.input.row.2 d.record.input.time).1 =
          ActiveRoundActions.coordinator p.two_le_m ∧
        d.record.output.preparation.arms.actions
            (ActiveRoundActions.coordinator p.two_le_m) = j ∧
        j ∉ installed.registers.payload.slowSet.val ∧
        CanonicalRecordingSlice.recordingMask (K_pos p)
          (ActiveRoundActions.coordinator p.two_le_m) j
          (d.record.input.row.2 d.record.input.time).1 ∧
        FiniteBanditModel.collisionFreeFor d.record.output.preparation.arms.actions
          (ActiveRoundActions.coordinator p.two_le_m) ∧
        d.record.output.preparation.feedback.feedback
            (ActiveRoundActions.coordinator p.two_le_m) = rewards t j ∧
        d.record.output.preparation.coordinatorObservation = rewards t j ∧
        (d.record.output.preparation.feedback.observations
            (ActiveRoundActions.coordinator p.two_le_m)).val.val =
          RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j) := by
  classical
  obtain ⟨hinstalled, _hrows, _hselected, hrewards, states, memories, hstates⟩ :=
    actual_call_prepared_followers rate rewards C_star C_h u t z d
      consistent output hlocal clockData installed selection hcut
  have hordinary i := (hstates i).2.2
  have hfields i (h : (states i).status ≠ .unoccupied) :
      (states i).lastDown = some (installed.registers.payload.downRecord i) :=
    (h (hstates i).2.1).elim
  have hcompat := CoordinatorAssignmentRegisterInstall.later_start_round_compatibility output clockData
  rw [hresult] at hcompat
  obtain ⟨_hkind, hsigma, hu, _hg, _hproposal, hpending, _hledger, _hclass, _hexpected⟩ := hcompat
  have hpayload : installed.registers.payload = output.payload := by
    rw [hinstalled]
    rfl
  have hnew : installed.registers.payload.sigma = d.record.input.time :=
    (congrArg AssignmentStartPayload.Input.sigma hpayload).trans
      (output.payload_start.trans d.instruction_time)
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive installed.registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
      d.record.input.time := by
    rw [hu]
    change installed.registers.payload.sigma.val + 1 ≤ d.record.input.time.val + 1 ∧
      d.record.input.time.val + 1 < p.T + 1
    rw [hnew]
    exact ⟨le_rfl, Nat.add_lt_add_right d.record.input.time.isLt 1⟩
  let P := ReferenceActivePhysicalStep.prepare d.record.input
  let I := ReferenceActivePhysicalStep.liveRecordingInput P installed.registers d.started
  have hgrid := d.started.gridDomain
  unfold CoordinatorPhaseClock.clockGridDomain at hgrid
  rw [hsigma] at hgrid
  change d.instruction.time.val + 1 < d.started.clock.g ∧ d.started.clock.g ≤ p.T + 1 at hgrid
  have hnotFrozen : ¬ CoordinatorRecorderComplementBridge.isFrozen I := by
    intro h
    have hbound : d.record.input.time.val + 1 ≥ d.started.clock.g := h.2
    rw [d.instruction_time] at hgrid
    omega
  obtain ⟨actualRecording, hactualRun, hactualField, hgate, hraw⟩ :=
    ReferenceCoordinatorLiveRecording.later_recording_identification d.record.input
      d.old d.ledger (ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u) u
      d.core consistent d.started d.clock_eq d.instruction d.instruction_eq output hlocal
      clockData installed selection hcut states memories hordinary hfields hlive
  have hsame : actualRecording = recording := Option.some.inj (hactualRun.symm.trans hrun)
  subst actualRecording
  have hrecording : d.record.output.coordinator.recording = some recording := by
    rw [d.record.output_eq]
    exact hactualField
  have hreconstruction : output.reconstruction = d.out := by
    have h := output.reconstruction_eq.symm.trans d.reconstruction_eq
    injection h with _ _ heq
  have hanchor : installed.registers.payload.anchor =
      AssignmentScoreReconstruction.currentWeight d.out := by
    rw [hinstalled, CoordinatorAssignmentRegisterInstall.later_payload_anchor_renewal
      output clockData d.renewal, hreconstruction]
    rfl
  have hrawTable : recording.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
      (AssignmentScoreReconstruction.currentWeight d.out)
      (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j))
      recording.gateArm := by
    rw [← hgate] at hraw
    rw [hanchor, hrewards, d.time_eq] at hraw
    exact hraw
  refine ⟨hinstalled, states, memories, hstates, hlive, hpending, hu,
    hnew.trans d.time_eq, hnotFrozen, hrecording, hrawTable, ?_⟩
  intro j hj
  let valid := ReferenceCoordinatorLiveRecording.liveRecordingInput_valid P
    installed.registers d.started d.instruction.time selection
  obtain ⟨hd, hs, _hf, ho, hm, hjarm⟩ := run_gate_facts I valid recording hrun j hj
  let selected : ReferenceActivePhysicalStep.Selection d.record.input := {
    view := {
      payload := installed.registers.payload
      pendingAtChoice := d.started.pending
      cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u
      complementWeights := installed.registers.complementWeights }
    started := d.started
    pending_eq := rfl
    cutoff_eq := rfl
    arm := selection.arm
    choice_eq := by simpa only [d.instruction_time] using selection.armChoice_eq }
  have hselected : P.coordinator.selection = some selected := by
    dsimp only [P]
    rw [hcut]
    simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, d.instruction_time, dite_true]
    rfl
  have hdata : PublicDiscreteDraws.slotDraw (d.record.input.row.2 d.record.input.time).1 =
      PublicDiscreteDraws.dataSlot := hd
  have haction : P.arms.actions (ActiveRoundActions.coordinator p.two_le_m) = j := by
    rw [ReferenceActivePhysicalStep.PreparedRound.action_coordinator]
    exact hjarm.symm
  have howns : SnapshotRecordingKernel.owns p
      (.live selected.view.payload.assignment
        (ReferenceActiveDataOwnership.choiceSnapshot selected states))
      (ActiveRoundActions.coordinator p.two_le_m) j := by
    rw [hjarm]
    exact ho
  have hmask : CanonicalRecordingSlice.recordingMask (K_pos p)
      (ActiveRoundActions.coordinator p.two_le_m) j
      (d.record.input.row.2 d.record.input.time).1 := by
    rw [hjarm]
    exact hm
  have hfree := ReferenceActiveDataOwnership.actual_data_owner_collisionFree d.record.input
    selected hselected states memories hordinary hfields hlive hdata
    (ActiveRoundActions.coordinator p.two_le_m) j haction howns hmask
  have hfeedback := ReferenceActiveDataOwnership.actual_data_owner_feedback d.record.input
    selected hselected states memories hordinary hfields hlive hdata
    (ActiveRoundActions.coordinator p.two_le_m) j haction howns hmask
  have hfast : j ∉ installed.registers.payload.slowSet.val := by
    rw [hjarm]
    change I.ownArm ∉
      (SnapshotRecordingKernel.assignmentSlowSet p installed.registers.payload.assignment).val at ho
    rw [CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload] at ho
    exact ho
  have hprepare : d.record.output.preparation = P := by
    rw [d.record.output_eq]
    rfl
  have hentry : d.record.input.rewards d.record.input.time j = rewards t j := by
    rw [hrewards, d.time_eq]
  have hgridFeedback := hfeedback.1.trans hentry
  have htypedFeedback := hfeedback.2.trans
    (congrArg (fun value : Fin (D p + 1) => (value.val : ℝ) / (D p : ℝ)) hentry)
  refine ⟨hdata, hs, ?_, hfast, hmask, ?_, ?_, ?_, ?_⟩
  · rw [hprepare]
    exact haction
  · rw [hprepare]
    exact hfree
  · rw [hprepare]
    exact hgridFeedback
  · rw [hprepare]
    exact hgridFeedback
  · rw [hprepare]
    exact htypedFeedback

end ActualDispatch

/-- On the SAME original finite unnormalized pair law, the actual first
renewal recorder used by the successful service has literal table feedback.
The only root inputs are dimensions, rate, the WHOLE rewards, unrestricted
shared constants, and calendar indices. Null cells are retained. No moments,
freshness, post-update overflow test, or matching-trace premise is added.

Named consumers: original-law renewal complement recording moments, then
actual renewed queue/drift after control-factor and coefficient acceptance.
This is neither those probability results nor manuscript closure. -/
theorem ae_pairLaw_actual_recording_feedback
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    ∀ᵐ b : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalBase
        rate rewards C_star C_h u t ×
      ReferenceFirstCollectionRenewalInstallationCoupling.Source
        rate rewards C_star C_h u t ∂
        ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
          rate rewards C_star C_h u t,
    let U := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
      rate rewards C_star C_h u t b.1.1 b.1.2
    ∃ d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
        rate rewards C_star C_h u t b.2,
      let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
        rate u d.record.input d.old d.ledger d.saved
      let ell := CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
      let par := LaterAssignmentStartMeasurability.selectedSamplerParameters
        x.payload ell d.instruction d.out d.reconstruction_eq
      let clock := ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u
      ∃ (consistent : LaterAssignmentStartOperation.LocalConsistency x.payload ell)
        (output : LaterAssignmentStartOperation.SuccessfulStart
          x.payload ell d.instruction x.row)
        (hlocal : output.localConsistency = consistent)
        (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
        (installed : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData)
        (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
          d.started d.instruction.time installed.registers.complementWeights d.record.input.row)
        (recording : CoordinatorRecordingOperation.Output p)
        (serviced : CoordinatorLiveServiceFinish.ServicedRegisters
          installed.registers installed.ownedRegisters),
        LaterAssignmentStartOperation.laterAssignmentStart
          x.payload ell d.instruction x.row consistent = .success output hlocal ∧
        LaterAssignmentStartOperation.ownAssignmentVector
          d.record.input.row d.instruction.time = output.assignmentVector ∧
        output.reconstruction = d.out ∧
        AssignmentParameterFibreKernel.successfulSlowSet p par output.assignmentVector =
          some output.slowSet ∧
        output.slowSet = U ∧ installed.registers.payload.slowSet = U ∧
        clockData.result = d.started ∧
        installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
        installed.registers.payload.anchor =
          AssignmentScoreReconstruction.currentWeight d.out ∧
        CoordinatorRoundDispatch.dispatchCollection x =
          .laterChosen d.core consistent d.started d.clock_eq d.instruction
            d.instruction_eq output hlocal clockData installed selection ∧
        d.record.output.preparation = ReferenceActivePhysicalStep.prepare d.record.input ∧
        (ReferenceActivePhysicalStep.prepare d.record.input).coordinator =
          .collection d.old d.ledger clock u
            (.laterChosen d.core consistent d.started d.clock_eq d.instruction
              d.instruction_eq output hlocal clockData installed selection) ∧
        d.record.output.coordinator = ReferenceActivePhysicalStep.livePostChoice
          (ReferenceActivePhysicalStep.prepare d.record.input) installed.registers
          installed.ownedRegisters installed.retainedBaseScore d.started ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.liveRecordingInput
            (ReferenceActivePhysicalStep.prepare d.record.input) installed.registers d.started) =
          some recording ∧
        CoordinatorLiveServiceFinish.servicePass installed.registers
          installed.ownedRegisters recording = .ok serviced ∧
        d.record.output.coordinator.recording = some recording ∧
        ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
          (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
          (∀ i, d.record.input.state.followers i = .ordinary (states i) (memories i) ∧
            (states i).status = .unoccupied ∧
            ((ReferenceActivePhysicalStep.prepare d.record.input).followers.followers i).configuration =
              .ordinary (states i) (memories i)) ∧
          CoordinatorLocalArmChoice.assignmentIsLive installed.registers.payload
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
            d.record.input.time ∧
          d.started.pending = Finset.univ ∧ d.started.clock.u = none ∧
          installed.registers.payload.sigma = t ∧
          ¬ CoordinatorRecorderComplementBridge.isFrozen
            (ReferenceActivePhysicalStep.liveRecordingInput
              (ReferenceActivePhysicalStep.prepare d.record.input) installed.registers d.started) ∧
          recording.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
            (AssignmentScoreReconstruction.currentWeight d.out)
            (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j))
            recording.gateArm ∧
          ∀ j, recording.gateArm = some j →
            PublicDiscreteDraws.slotDraw (d.record.input.row.2 d.record.input.time).1 =
              PublicDiscreteDraws.dataSlot ∧
            PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
                (d.record.input.row.2 d.record.input.time).1 =
              ActiveRoundActions.coordinator p.two_le_m ∧
            d.record.output.preparation.arms.actions
                (ActiveRoundActions.coordinator p.two_le_m) = j ∧
            j ∉ installed.registers.payload.slowSet.val ∧
            CanonicalRecordingSlice.recordingMask (K_pos p)
              (ActiveRoundActions.coordinator p.two_le_m) j
              (d.record.input.row.2 d.record.input.time).1 ∧
            FiniteBanditModel.collisionFreeFor d.record.output.preparation.arms.actions
              (ActiveRoundActions.coordinator p.two_le_m) ∧
            d.record.output.preparation.feedback.feedback
                (ActiveRoundActions.coordinator p.two_le_m) = rewards t j ∧
            d.record.output.preparation.coordinatorObservation = rewards t j ∧
            (d.record.output.preparation.feedback.observations
                (ActiveRoundActions.coordinator p.two_le_m)).val.val =
              RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j) := by
  classical
  filter_upwards
    [ReferenceFirstCollectionRenewalNumericalServiceJoin.ae_pairLaw_actual_numerical_service_join
      rate rewards C_star C_h u t] with b hb
  dsimp only at hb ⊢
  rcases hb with ⟨d, consistent, output, hlocal, hstart, hv, hreconstruction,
    hsample, hslow, _hpayloadSlow, htail⟩
  let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
    rate u d.record.input d.old d.ledger d.saved
  let ell := CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
  let clock := ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
    priorClock := x.clock
    pending := x.ledger.pending
    proposalParameterValid := d.core.clock_parameter_valid
    priorClockValid := d.core.clock_registers_valid
    startTimeValid := by
      simpa only [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput, d.instruction_time] using
        d.core.clock_start_time_valid
    result := d.started
    startRound_eq := by
      simpa only [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput,
        ReferenceActivePhysicalStep.collectionClock, d.instruction_time] using d.clock_eq
    assignmentStart_eq := d.instruction_eq
    priorSigma_eq := d.core.clock_sigma_eq
    priorGrid_eq_freezeAt := by
      calc
        x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
        _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
        _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
  let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
  rcases htail with ⟨_hinstalledPayload, _hinstalledVector, _hinstalledReconstruction,
    hanchor, _hqueues, _hbase, hinstalledSlow, selection, _hselection, hdispatch,
    hpreparation, hpreparationCoordinator, _hselectedArm, hpostChoice, _hnextChoice,
    recording, serviced, _pending, _finished, hrecord, hservice, _hrest⟩
  have hcut : (ReferenceActivePhysicalStep.prepare d.record.input).coordinator =
      .collection d.old d.ledger clock u
        (.laterChosen d.core consistent d.started d.clock_eq d.instruction
          d.instruction_eq output hlocal clockData installed selection) := by
    rw [← hpreparation, hpreparationCoordinator, hdispatch]
  obtain ⟨hinstalled, states, memories, hstates, hlive, hpending, hu, hsigma,
    hnotFrozen, hrecordingField, hraw, hfeedback⟩ :=
    actual_call_recording_feedback rate rewards C_star C_h u t b.2 d consistent
      output hlocal clockData installed selection hcut rfl recording hrecord
  have hsampleOutput := hsample
  rw [hv] at hsampleOutput
  exact ⟨d, consistent, output, hlocal, clockData, installed, selection, recording,
    serviced, hstart, hv, hreconstruction, hsampleOutput, hslow, hinstalledSlow,
    rfl, hinstalled, hanchor, hdispatch, hpreparation, hcut, hpostChoice, hrecord, hservice,
    hrecordingField, states, memories, hstates, hlive, hpending, hu, hsigma,
    hnotFrozen, hraw, hfeedback⟩

end Bandits.Support.ReferenceFirstCollectionRenewalRecordingFeedback
