/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteSignedFirstBadCalendar
public import Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw

/-!
# Original-calendar physical operations with the proposal scalar erased

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-75,246-299,425-431,493-536`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

Only the selected coordinator row's current `prop` scalar is replaced. The
physical record projection retains absence, the DOWN view, continuation
arguments, actions, grid feedback, and own entries. No read-call or stopped-read
factorization is asserted here.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open scoped Classical

namespace Bandits.Support.ReferenceOriginalCalendarProposalFreePhysicalOperations

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters}

/-- Replace only the named proposal scalar in one current control slice. -/
def replaceCurrentProp (control : ContinuousLearningRows.TimeControl p)
    (value : ContinuousControlSlice.Scalar) : ContinuousLearningRows.TimeControl p :=
  (Function.update control.1 ContinuousControlSlice.Label.prop value, control.2)

private theorem slotLabel_ne_prop (m K : ℕ) :
    ContinuousControlSlice.Label.slot (m := m) (K := K) ≠
      ContinuousControlSlice.Label.prop := by
  intro h
  have h' : ContinuousControlSlice.NamedLabel.slot =
      ContinuousControlSlice.NamedLabel.prop := Sum.inl_injective h
  exact (by decide : ContinuousControlSlice.NamedLabel.slot ≠
    ContinuousControlSlice.NamedLabel.prop) h'

private theorem selLabel_ne_prop (m K : ℕ) :
    ContinuousControlSlice.Label.sel (m := m) (K := K) ≠
      ContinuousControlSlice.Label.prop := by
  intro h
  have h' : ContinuousControlSlice.NamedLabel.sel =
      ContinuousControlSlice.NamedLabel.prop := Sum.inl_injective h
  exact (by decide : ContinuousControlSlice.NamedLabel.sel ≠
    ContinuousControlSlice.NamedLabel.prop) h'

private theorem recLabel_ne_prop (m K : ℕ) :
    ContinuousControlSlice.Label.rec (m := m) (K := K) ≠
      ContinuousControlSlice.Label.prop := by
  intro h
  have h' : ContinuousControlSlice.NamedLabel.recorder =
      ContinuousControlSlice.NamedLabel.prop := Sum.inl_injective h
  exact (by decide : ContinuousControlSlice.NamedLabel.recorder ≠
    ContinuousControlSlice.NamedLabel.prop) h'

private theorem fastLabel_ne_prop (m K : ℕ) :
    ContinuousControlSlice.Label.fast (m := m) (K := K) ≠
      ContinuousControlSlice.Label.prop := by
  intro h
  have h' : ContinuousControlSlice.NamedLabel.fast =
      ContinuousControlSlice.NamedLabel.prop := Sum.inl_injective h
  exact (by decide : ContinuousControlSlice.NamedLabel.fast ≠
    ContinuousControlSlice.NamedLabel.prop) h'

private theorem thinLabel_ne_prop (m K : ℕ) :
    ContinuousControlSlice.Label.thin (m := m) (K := K) ≠
      ContinuousControlSlice.Label.prop := by
  intro h
  have h' : ContinuousControlSlice.NamedLabel.thin =
      ContinuousControlSlice.NamedLabel.prop := Sum.inl_injective h
  exact (by decide : ContinuousControlSlice.NamedLabel.thin ≠
    ContinuousControlSlice.NamedLabel.prop) h'

private theorem tupleLabel_ne_prop (m K : ℕ) (i : Fin m) :
    ContinuousControlSlice.Label.tuple (m := m) (K := K) i ≠
      ContinuousControlSlice.Label.prop (m := m) (K := K) := by
  intro h
  change (Sum.inr (Sum.inl i) : ContinuousControlSlice.Label m K) =
    Sum.inl ContinuousControlSlice.NamedLabel.prop at h
  exact Sum.inr_ne_inl h

private theorem pilotLabel_ne_prop (m K : ℕ) (i : Fin m) :
    ContinuousControlSlice.Label.pilot (m := m) (K := K) i ≠
      ContinuousControlSlice.Label.prop (m := m) (K := K) := by
  intro h
  change (Sum.inr (Sum.inr (Sum.inl i)) : ContinuousControlSlice.Label m K) =
    Sum.inl ContinuousControlSlice.NamedLabel.prop at h
  exact Sum.inr_ne_inl h

theorem replaceCurrentProp_coordinate (control : ContinuousLearningRows.TimeControl p)
    (value : ContinuousControlSlice.Scalar) (label : ContinuousControlSlice.Label p.m p.K)
    (hlabel : label ≠ ContinuousControlSlice.Label.prop) :
    (replaceCurrentProp control value).1 label = control.1 label := by
  simp [replaceCurrentProp, Function.update_of_ne hlabel]

theorem replaceCurrentProp_affine (control : ContinuousLearningRows.TimeControl p)
    (value : ContinuousControlSlice.Scalar) :
    (replaceCurrentProp control value).2 = control.2 := rfl

/-- The selected follower's checked UP offer does not inspect `prop`. -/
theorem checkedUpOffer_prop_erasure (eta : ReferencePrelaunchFollower.LearningRate)
    (i : Fin (p.m - 1))
    (row row' : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (state : ReferencePrelaunchFollower.State p eta)
    (value : ContinuousControlSlice.Scalar)
    (hcurrent : row'.2 time = replaceCurrentProp (row.2 time) value) :
    ActiveFollowerQueueOperation.checkedUpOffer eta i row' activation time state =
      ActiveFollowerQueueOperation.checkedUpOffer eta i row activation time state := by
  have hslot : PublicDiscreteDraws.slotDraw (row'.2 time).1 =
      PublicDiscreteDraws.slotDraw (row.2 time).1 := by
    simp only [hcurrent, PublicDiscreteDraws.slotDraw,
      ContinuousControlSlice.coordinate, replaceCurrentProp]
    rw [Function.update_of_ne (slotLabel_ne_prop p.m p.K)]
  have hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (row'.2 time).1 = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (row.2 time).1 := by
    simp only [hcurrent, PublicDiscreteDraws.selectedFollowerDraw,
      ContinuousControlSlice.coordinate, replaceCurrentProp]
    rw [Function.update_of_ne (selLabel_ne_prop p.m p.K)]
  have hup : ActiveFollowerQueueOperation.selectedUpRound i row' activation time =
      ActiveFollowerQueueOperation.selectedUpRound i row activation time := by
    unfold ActiveFollowerQueueOperation.selectedUpRound
    rw [hslot, hselected]
  unfold ActiveFollowerQueueOperation.checkedUpOffer
  rw [hup]

/-- Every follower arm branch is unchanged by the current proposal scalar. -/
theorem followerArmChoiceCore_prop_erasure {eta : ReferencePrelaunchFollower.LearningRate}
    (state : ReferencePrelaunchFollower.State p eta)
    (control : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
      (offered : Option (OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p eta)))
    (value : ContinuousControlSlice.Scalar) :
    ActiveFollowerArmChoice.followerArmChoiceCore state (replaceCurrentProp control value) i offered =
      ActiveFollowerArmChoice.followerArmChoiceCore state control i offered := by
  have hslot : PublicDiscreteDraws.slotDraw (replaceCurrentProp control value).1 =
      PublicDiscreteDraws.slotDraw control.1 := by
    simp only [PublicDiscreteDraws.slotDraw, ContinuousControlSlice.coordinate,
      replaceCurrentProp]
    rw [Function.update_of_ne (slotLabel_ne_prop p.m p.K)]
  have hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (replaceCurrentProp control value).1 =
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1 := by
    simp only [PublicDiscreteDraws.selectedFollowerDraw, ContinuousControlSlice.coordinate,
      replaceCurrentProp]
    rw [Function.update_of_ne (selLabel_ne_prop p.m p.K)]
  have htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K
        (replaceCurrentProp control value).1 =
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K control.1 := by
    apply OrderedTupleSampler.sample_eq_of_tupleInputs_eq p.two_le_m p.m_lt_K
    intro j
    simp only [replaceCurrentProp]
    rw [Function.update_of_ne (tupleLabel_ne_prop p.m p.K j)]
  have hpilot : PublicDiscreteDraws.pilotDraw (K_pos p)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) (replaceCurrentProp control value).1 =
      PublicDiscreteDraws.pilotDraw (K_pos p)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) control.1 := by
    simp only [PublicDiscreteDraws.pilotDraw, ContinuousControlSlice.coordinate,
      replaceCurrentProp]
    rw [Function.update_of_ne (pilotLabel_ne_prop p.m p.K
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))]
  have hsample : (replaceCurrentProp control value).2 (1, i) = control.2 (1, i) := rfl
  exact ActiveFollowerArmChoice.followerArmChoiceCore_eq_of_same_local_draws state
    (replaceCurrentProp control value) control i offered hslot hselected htuple hpilot hsample

/-- The complete coordinator arm-choice core ignores only the `prop` scalar. -/
theorem coordinatorArmChoiceCore_prop_erasure {eta : ReferencePrelaunchFollower.LearningRate}
    (payload : AssignmentStartPayload.Input p eta)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (control : ContinuousLearningRows.TimeControl p)
    (value : ContinuousControlSlice.Scalar) :
    CoordinatorLocalArmChoice.coordinatorArmChoiceCore payload pending cutoff time weights
        (replaceCurrentProp control value) =
      CoordinatorLocalArmChoice.coordinatorArmChoiceCore payload pending cutoff time weights control := by
  have hslot : PublicDiscreteDraws.slotDraw (replaceCurrentProp control value).1 =
      PublicDiscreteDraws.slotDraw control.1 := by
    simp only [PublicDiscreteDraws.slotDraw, ContinuousControlSlice.coordinate,
      replaceCurrentProp]
    rw [Function.update_of_ne (slotLabel_ne_prop p.m p.K)]
  have hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (replaceCurrentProp control value).1 =
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1 := by
    simp only [PublicDiscreteDraws.selectedFollowerDraw, ContinuousControlSlice.coordinate,
      replaceCurrentProp]
    rw [Function.update_of_ne (selLabel_ne_prop p.m p.K)]
  have hfast : ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
        (replaceCurrentProp control value).1 =
      ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast control.1 := by
    simp only [ContinuousControlSlice.coordinate, replaceCurrentProp]
    rw [Function.update_of_ne (fastLabel_ne_prop p.m p.K)]
  have hpilot : PublicDiscreteDraws.pilotDraw (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) (replaceCurrentProp control value).1 =
      PublicDiscreteDraws.pilotDraw (K_pos p) (ActiveRoundActions.coordinator p.two_le_m) control.1 := by
    simp only [PublicDiscreteDraws.pilotDraw, ContinuousControlSlice.coordinate,
      replaceCurrentProp]
    rw [Function.update_of_ne (pilotLabel_ne_prop p.m p.K
      (ActiveRoundActions.coordinator p.two_le_m))]
  have htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K
        (replaceCurrentProp control value).1 = OrderedTupleSampler.sample p.two_le_m p.m_lt_K control.1 := by
    apply OrderedTupleSampler.sample_eq_of_tupleInputs_eq p.two_le_m p.m_lt_K
    intro i
    simp only [replaceCurrentProp]
    rw [Function.update_of_ne (tupleLabel_ne_prop p.m p.K i)]
  have hsample (i : ActiveRoundActions.Follower p.m) :
      (replaceCurrentProp control value).2 (0, i) = control.2 (0, i) := rfl
  have hhash (i : ActiveRoundActions.Follower p.m) :
      CoordinatorLocalArmChoice.currentDownHash payload (replaceCurrentProp control value) i =
        CoordinatorLocalArmChoice.currentDownHash payload control i := by
    simp only [CoordinatorLocalArmChoice.currentDownHash]
    rw [CoordinatorLocalArmChoice.downChannel]
    rw [hsample i]
  have hfastDraw (valid : CoordinatorLocalArmChoice.ChoiceInputsValid payload cutoff time weights) :
      CoordinatorLocalArmChoice.localFastDraw payload cutoff time weights valid
          (replaceCurrentProp control value) =
        CoordinatorLocalArmChoice.localFastDraw payload cutoff time weights valid control := by
    simp only [CoordinatorLocalArmChoice.localFastDraw]
    rw [hfast]
  simp only [CoordinatorLocalArmChoice.coordinatorArmChoiceCore, hslot, hselected,
    hpilot, htuple, hfastDraw, hhash]

/-- The complete-row coordinator choice inherits the core's `prop` erasure. -/
theorem coordinatorArmChoice_prop_erasure {eta : ReferencePrelaunchFollower.LearningRate}
    (payload : AssignmentStartPayload.Input p eta)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (row row' : CompletePublicTable.CompleteRow p)
    (value : ContinuousControlSlice.Scalar)
    (hcurrent : row'.2 time = replaceCurrentProp (row.2 time) value) :
    CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff time weights row' =
      CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff time weights row := by
  change CoordinatorLocalArmChoice.coordinatorArmChoiceCore payload pending cutoff time weights
      (row'.2 time) =
    CoordinatorLocalArmChoice.coordinatorArmChoiceCore payload pending cutoff time weights
      (row.2 time)
  rw [hcurrent]
  exact coordinatorArmChoiceCore_prop_erasure payload pending cutoff time weights
    (row.2 time) value

/-- The checked coordinator recorder preserves all of its branches under this
single-scalar replacement, including failed domains and recorded zero. -/
theorem coordinatorRecordingRun_prop_erasure (input : CoordinatorRecordingOperation.Input p)
    (row' : CompletePublicTable.CompleteRow p) (value : ContinuousControlSlice.Scalar)
    (hcurrent : row'.2 input.time = replaceCurrentProp (input.row.2 input.time) value) :
    CoordinatorRecordingOperation.run input =
      CoordinatorRecordingOperation.run { input with row := row' } := by
  have hslot : (row'.2 input.time).1 ContinuousControlSlice.Label.slot =
      (input.row.2 input.time).1 ContinuousControlSlice.Label.slot := by
    rw [hcurrent]
    exact replaceCurrentProp_coordinate (input.row.2 input.time) value _
      (slotLabel_ne_prop p.m p.K)
  have hrec : (row'.2 input.time).1 ContinuousControlSlice.Label.rec =
      (input.row.2 input.time).1 ContinuousControlSlice.Label.rec := by
    rw [hcurrent]
    exact replaceCurrentProp_coordinate (input.row.2 input.time) value _
      (recLabel_ne_prop p.m p.K)
  have hthin : (row'.2 input.time).1 ContinuousControlSlice.Label.thin =
      (input.row.2 input.time).1 ContinuousControlSlice.Label.thin := by
    rw [hcurrent]
    exact replaceCurrentProp_coordinate (input.row.2 input.time) value _
      (thinLabel_ne_prop p.m p.K)
  have hpilot (i : Fin p.m) :
      (row'.2 input.time).1 (ContinuousControlSlice.Label.pilot i) =
        (input.row.2 input.time).1 (ContinuousControlSlice.Label.pilot i) := by
    rw [hcurrent]
    exact replaceCurrentProp_coordinate (input.row.2 input.time) value _
      (pilotLabel_ne_prop p.m p.K i)
  have hmask : CoordinatorRecordingOperation.ownMaskPasses { input with row := row' } ↔
      CoordinatorRecordingOperation.ownMaskPasses input := by
    unfold CoordinatorRecordingOperation.ownMaskPasses CanonicalRecordingSlice.recordingMask
    simp only [PublicDiscreteDraws.pilotDraw, ContinuousControlSlice.coordinate,
      ContinuousLearningRows.sliceAt]
    simp only [hpilot]
  have hvalid : CoordinatorRecordingOperation.InputsValid input ↔
      CoordinatorRecordingOperation.InputsValid { input with row := row' } := by
    constructor <;> intro h
    · exact ⟨h.sigma_le_terminal, h.boundary_le_terminal, h.eta_pos, h.eta_source_cap,
        h.anchor_pos, h.current_pos, h.anchor_le_current, h.current_le_twice_anchor⟩
    · exact ⟨h.sigma_le_terminal, h.boundary_le_terminal, h.eta_pos, h.eta_source_cap,
        h.anchor_pos, h.current_pos, h.anchor_le_current, h.current_le_twice_anchor⟩
  have hraw (h : CoordinatorRecordingOperation.InputsValid input) :
      CoordinatorRecordingOperation.coordinatorRawGateMass { input with row := row' }
          (hvalid.mp h) = CoordinatorRecordingOperation.coordinatorRawGateMass input h := rfl
  have hfrozen : CoordinatorRecordingOperation.isFrozen { input with row := row' } ↔
      CoordinatorRecordingOperation.isFrozen input := Iff.rfl
  have hfloor : CoordinatorRecordingOperation.floorArrival { input with row := row' } =
      CoordinatorRecordingOperation.floorArrival input := rfl
  by_cases h : CoordinatorRecordingOperation.InputsValid input
  · simp only [CoordinatorRecordingOperation.run, dite_eq_left h,
      dite_eq_left (hvalid.mp h)]
    simp only [CoordinatorRecordingOperation.executeValid,
      CoordinatorRecordingOperation.selectedSlot, CoordinatorRecordingOperation.selectedRecorder,
      ContinuousLearningRows.sliceAt, ContinuousControlSlice.coordinate,
      hslot, hrec, hmask, hraw h, hthin, hfrozen, hfloor]
    rfl
  · simp only [CoordinatorRecordingOperation.run, dite_eq_right h,
      dite_eq_right (mt hvalid.mpr h)]

/-- Applying the literal service pass to the recorder's produced optional
value preserves every `ServicedRegisters` field, including the enabled-zero
recording branch. The option is retained when recording rejects. -/
theorem coordinatorServicePass_prop_erasure
    (eta : ReferencePrelaunchFollower.LearningRate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (input : CoordinatorRecordingOperation.Input p)
    (row' : CompletePublicTable.CompleteRow p)
    (value : ContinuousControlSlice.Scalar)
    (hcurrent : row'.2 input.time =
      replaceCurrentProp (input.row.2 input.time) value) :
    (CoordinatorRecordingOperation.run input).map
        (CoordinatorLiveServiceFinish.servicePass registers owned) =
      (CoordinatorRecordingOperation.run { input with row := row' }).map
        (CoordinatorLiveServiceFinish.servicePass registers owned) := by
  exact congrArg (fun result =>
    result.map (CoordinatorLiveServiceFinish.servicePass registers owned))
      (coordinatorRecordingRun_prop_erasure input row' value hcurrent)

/-- Confirmation has no dependence on the current proposal scalar. -/
theorem confirmationUpdateCore_prop_erasure {eta : ReferencePrelaunchFollower.LearningRate}
    (payload : AssignmentStartPayload.Input p eta)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)) (time : Fin p.T)
    (observation : Fin (D p + 1)) (control : ContinuousLearningRows.TimeControl p)
    (value : ContinuousControlSlice.Scalar) :
    CoordinatorLocalArmChoice.confirmationUpdateCore payload pending cutoff time
        (replaceCurrentProp control value) observation =
      CoordinatorLocalArmChoice.confirmationUpdateCore payload pending cutoff time control observation := by
  have hslot : PublicDiscreteDraws.slotDraw (replaceCurrentProp control value).1 =
      PublicDiscreteDraws.slotDraw control.1 := by
    simp only [PublicDiscreteDraws.slotDraw, ContinuousControlSlice.coordinate,
      replaceCurrentProp]
    rw [Function.update_of_ne (slotLabel_ne_prop p.m p.K)]
  have hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (replaceCurrentProp control value).1 =
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1 := by
    simp only [PublicDiscreteDraws.selectedFollowerDraw, ContinuousControlSlice.coordinate,
      replaceCurrentProp]
    rw [Function.update_of_ne (selLabel_ne_prop p.m p.K)]
  have hsample : (replaceCurrentProp control value).2
      (0, PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (replaceCurrentProp control value).1) =
      control.2 (0, PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (replaceCurrentProp control value).1) := rfl
  exact CoordinatorLocalArmChoice.confirmationUpdateCore_eq_of_same_local_reads
    payload pending cutoff time (replaceCurrentProp control value) control observation
    hslot hselected hsample

private theorem followerPrepareArm_prop_erasure (eta : ActiveFollowerDownAcceptance.RateInput p)
    (i : Fin (p.m - 1)) (row row' : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (active : activation.val ≤ time.val + 1)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p eta)
    (value : ContinuousControlSlice.Scalar)
    (hcurrent : row'.2 time = replaceCurrentProp (row.2 time) value) :
    (DeclaredFollowerLocalRound.prepare eta i row' activation time active configuration).arm =
      (DeclaredFollowerLocalRound.prepare eta i row activation time active configuration).arm := by
  classical
  have hoff (state : ReferencePrelaunchFollower.State p eta.eta) :
      ActiveFollowerQueueOperation.checkedUpOffer eta.eta i row' activation time state =
        ActiveFollowerQueueOperation.checkedUpOffer eta.eta i row activation time state :=
    checkedUpOffer_prop_erasure eta.eta i row row' activation time state value hcurrent
  have hchoice (state : ReferencePrelaunchFollower.State p eta.eta)
      (offered : Option (OrdinaryMessageCodec.UpRecord
        (ReferencePrelaunchFollower.codecParams p eta.eta))) :
      ActiveFollowerArmChoice.followerArmChoice state row' time i offered =
        ActiveFollowerArmChoice.followerArmChoice state row time i offered := by
    change ActiveFollowerArmChoice.followerArmChoiceCore state (row'.2 time) i offered =
      ActiveFollowerArmChoice.followerArmChoiceCore state (row.2 time) i offered
    rw [hcurrent]
    exact followerArmChoiceCore_prop_erasure state (row.2 time) i offered value
  cases configuration with
  | dagger => rfl
  | ordinary state memory =>
      simp only [DeclaredFollowerLocalRound.prepare]
      cases ActiveFollowerLifecycle.startRound eta.eta time state memory with
      | error reason => rfl
      | ok result =>
          rcases result with ⟨choiceState, choiceMemory⟩
          have hOfferEq := hoff choiceState
          cases hoffResult : ActiveFollowerQueueOperation.checkedUpOffer eta.eta i row
              activation time choiceState with
          | failure => simp [hOfferEq, hoffResult]
          | noOffer =>
              cases hchoiceResult : ActiveFollowerArmChoice.followerArmChoice choiceState
                  row time i none with
              | none => simp [hOfferEq, hoffResult, hchoiceResult, hchoice]
              | some arm => simp [hOfferEq, hoffResult, hchoiceResult, hchoice]
          | offer offered =>
              cases hchoiceResult : ActiveFollowerArmChoice.followerArmChoice choiceState
                  row time i (some offered) with
              | none => simp [hOfferEq, hoffResult, hchoiceResult, hchoice]
              | some arm => simp [hOfferEq, hoffResult, hchoiceResult, hchoice]

private theorem actualRecord_presence_eq
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (time : Fin p.T) (source source' : SourceInput p)
    (hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h time source =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h time source') :
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h time source).isSome =
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h time source').isSome := by
  unfold ReferenceSourcePrefixHistoryFiltration.incoming at hin
  have h := congrArg Option.isSome hin
  simpa only [Option.isSome_map] using h

private theorem assignmentLabel_ne_prop (i : Fin (p.K + 1)) :
    ContinuousControlSlice.Label.assign (m := p.m) (K := p.K) i ≠
      ContinuousControlSlice.Label.prop (m := p.m) (K := p.K) := by
  intro h
  change Sum.inr (Sum.inr (Sum.inr i)) = Sum.inl ContinuousControlSlice.NamedLabel.prop at h
  exact Sum.inr_ne_inl h

private theorem selectedRow_assignmentVector_currentProp
    (time : Fin p.T) (source : SourceInput p)
    (value : ContinuousControlSlice.Scalar) :
    let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
    let changed := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p time source
      (replaceCurrentProp ((source.1.2 selected).2 time) value)
    ∀ t, LaterAssignmentStartOperation.ownAssignmentVector (source.1.2 selected) t =
      LaterAssignmentStartOperation.ownAssignmentVector (changed.1.2 selected) t := by
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let changed := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p time source
    (replaceCurrentProp ((source.1.2 selected).2 time) value)
  dsimp only
  intro t
  have hslice (s : Fin p.T) (hs : s ≠ time) :
      (changed.1.2 selected).2 s = (source.1.2 selected).2 s := by
    simp [changed, selected, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
      hs]
  have hsliceCurrent : (changed.1.2 selected).2 time =
      replaceCurrentProp ((source.1.2 selected).2 time) value := by
    simp [changed, selected, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  funext i
  rw [LaterAssignmentStartOperation.ownAssignmentVector_apply,
    LaterAssignmentStartOperation.ownAssignmentVector_apply]
  by_cases ht : t = time
  · subst t
    rw [hsliceCurrent]
    exact replaceCurrentProp_coordinate ((source.1.2 selected).2 time) value _
      (assignmentLabel_ne_prop i)
  · rw [hslice t ht]

private theorem roundInput_eq_of_fields
    {rate : RateInput p}
    {x y : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : x.state = y.state) (hrows : x.rows = y.rows)
    (hselected : x.selected = y.selected) (htime : x.time = y.time)
    (hrewards : x.rewards = y.rewards) : x = y := by
  cases x with
  | mk xstate xrows xselected xtime xactive xrewards =>
    cases y with
    | mk ystate yrows yselected ytime yactive yrewards =>
      dsimp at hstate hrows hselected htime hrewards
      subst ystate
      subst yrows
      subst yselected
      subst ytime
      subst yrewards
      have : xactive = yactive := Subsingleton.elim _ _
      subst yactive
      rfl

/-- Conditional physical-operation congruence at one current control slice.
The caller proves the incoming state and full assignment-vector equality from
the original source; this helper retains every dispatcher tail, action,
feedback coordinate, and own entry. -/
private theorem physicalProjection_eq_of_current_prop
    (rate : RateInput p)
    (state : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (value : ContinuousControlSlice.Scalar)
    (hcurrent : (otherRows selected).2 time =
      replaceCurrentProp ((rows selected).2 time) value)
    (hv : ∀ time, LaterAssignmentStartOperation.ownAssignmentVector (rows selected) time =
      LaterAssignmentStartOperation.ownAssignmentVector (otherRows selected) time) :
    let x : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, rows, selected, time, active, rewards⟩
    let y : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, otherRows, selected, time, active, rewards⟩
    ((ReferenceActiveDispatchTemporal.dispatchData x).2,
      (ReferenceActivePhysicalStep.prepare x).arms.actions,
      (ReferenceActivePhysicalStep.prepare x).feedback.feedback,
      (ReferenceActivePhysicalStep.step x).ownEntries) =
    ((ReferenceActiveDispatchTemporal.dispatchData y).2,
      (ReferenceActivePhysicalStep.prepare y).arms.actions,
      (ReferenceActivePhysicalStep.prepare y).feedback.feedback,
      (ReferenceActivePhysicalStep.step y).ownEntries) := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, otherRows, selected, time, active, rewards⟩
  have htail := ReferenceAffineDispatchPairInvariance.dispatch_tail_eq_of_assignment
    (state := state) (rows := rows) (otherRows := otherRows)
    (J := selected) (t := time) (active := active)
    (rewards := rewards) (otherRewards := rewards) hv
  have hview : (ReferenceActivePhysicalStep.dispatch x).downView =
      (ReferenceActivePhysicalStep.dispatch y).downView := by
    change (ReferenceActiveDispatchTemporal.dispatchData x).2.1 =
      (ReferenceActiveDispatchTemporal.dispatchData y).2.1
    exact congrArg Prod.fst htail
  have harm : (ReferenceActivePhysicalStep.dispatch x).arm =
      (ReferenceActivePhysicalStep.dispatch y).arm := by
    cases hx : (ReferenceActivePhysicalStep.dispatch x).selection with
    | none =>
        cases hy : (ReferenceActivePhysicalStep.dispatch y).selection with
        | none => simp [ReferenceActivePhysicalStep.DispatchCut.arm, hx, hy]
        | some selectedY =>
            simp only [ReferenceActivePhysicalStep.DispatchCut.downView, hx, hy,
              Option.map_none, Option.map_some] at hview
            cases hview
    | some selectedX =>
        cases hy : (ReferenceActivePhysicalStep.dispatch y).selection with
        | none =>
            simp only [ReferenceActivePhysicalStep.DispatchCut.downView, hx, hy,
              Option.map_none, Option.map_some] at hview
            cases hview
        | some selectedY =>
            have hselectedView : selectedX.view = selectedY.view := by
              have hviews : some selectedX.view = some selectedY.view := by
                simpa only [ReferenceActivePhysicalStep.DispatchCut.downView, hx, hy,
                  Option.map_some] using hview
              exact Option.some.inj hviews
            have hchoice := coordinatorArmChoice_prop_erasure selectedX.view.payload
              selectedX.view.pendingAtChoice selectedX.view.cutoff x.time
              selectedX.view.complementWeights x.row y.row value hcurrent
            have hchoiceY := selectedY.choice_eq
            rw [← hselectedView] at hchoiceY
            rw [hchoice] at hchoiceY
            rw [selectedX.choice_eq] at hchoiceY
            have harm' : selectedX.arm = selectedY.arm := Option.some.inj hchoiceY
            simpa only [ReferenceActivePhysicalStep.DispatchCut.arm, hx, hy] using harm'
  let preparedX := ReferenceActivePhysicalStep.prepare x
  let preparedY := ReferenceActivePhysicalStep.prepare y
  have hcoordinatorAction :
      preparedX.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
        preparedY.arms.actions (ActiveRoundActions.coordinator p.two_le_m) := by
    rw [preparedX.action_coordinator, preparedY.action_coordinator]
    exact harm
  have hactions : preparedX.arms.actions = preparedY.arms.actions := by
    funext player
    by_cases hcoord : player = ActiveRoundActions.coordinator p.two_le_m
    · subst player
      exact hcoordinatorAction
    · let i := ActiveRoundActions.followerIndex p.two_le_m player hcoord
      have hplayer := ActiveRoundActions.followerPlayer_followerIndex p.two_le_m player hcoord
      rw [← hplayer, preparedX.action_follower i, preparedY.action_follower i]
      exact (followerPrepareArm_prop_erasure rate i x.row y.row
        (x.state.activations i) x.time (x.active i) (x.state.followers i)
        value hcurrent).symm
  have hfeedback : preparedX.feedback.feedback = preparedY.feedback.feedback := by
    funext player
    rw [preparedX.feedback_rule player, preparedY.feedback_rule player, hactions]
  have hentries : (ReferenceActivePhysicalStep.step x).ownEntries =
      (ReferenceActivePhysicalStep.step y).ownEntries := by
    funext player
    rw [ReferenceActivePhysicalStep.step_own_entry x player,
      ReferenceActivePhysicalStep.step_own_entry y player, hactions, hfeedback]
  exact Prod.ext htail (Prod.ext hactions (Prod.ext hfeedback hentries))

/-- The actual optional record projection is unchanged when only the current
original selected-row proposal scalar is replaced. Record presence comes from
the strict-prefix incoming state, while physical operations are compared from
their constructed inputs and all-time assignment reads. -/
theorem actualRecord_physicalOperations_prop_replacement
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin p.T) (z : SourceInput p)
    (value : ContinuousControlSlice.Scalar) :
    let J := ActualInitializationPhysicalStep.selectedRowIndex p z
    let c := (z.1.2 J).2 q
    let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z
      (replaceCurrentProp c value)
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).map
      (fun r => ((ReferenceActiveDispatchTemporal.dispatchData r.input).2,
        r.actions, r.gridFeedback, r.ownEntries)) =
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z').map
      (fun r => ((ReferenceActiveDispatchTemporal.dispatchData r.input).2,
        r.actions, r.gridFeedback, r.ownEntries)) := by
  let J := ActualInitializationPhysicalStep.selectedRowIndex p z
  let c := (z.1.2 J).2 q
  let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p q z
    (replaceCurrentProp c value)
  change (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).map
      (fun r => ((ReferenceActiveDispatchTemporal.dispatchData r.input).2,
        r.actions, r.gridFeedback, r.ownEntries)) =
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z').map
      (fun r => ((ReferenceActiveDispatchTemporal.dispatchData r.input).2,
        r.actions, r.gridFeedback, r.ownEntries))
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z' := by
    calc
      _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix c q.val z) :=
        ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h c q z
      _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix c q.val z') := by
        exact congrArg (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q)
          (ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current c q z
            (replaceCurrentProp c value)).symm
      _ = ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z' :=
        (ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h c q z').symm
  have hpresent := actualRecord_presence_eq rate rewards C_star C_h q z z' hin
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z with
  | none =>
      have hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z' = none := by
        cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z' with
        | none => rfl
        | some r' =>
            have : False := by
              simp only [hr, hrecord, Option.isSome_none, Option.isSome_some] at hpresent
              cases hpresent
            cases this
      rw [hr']
  | some r =>
      have hsome' : (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z').isSome = true := by
        rw [← hpresent, hr]
        rfl
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome'
      have hfields := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
        rate rewards C_star C_h q z r hr
      have hfields' := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
        rate rewards C_star C_h q z' r' hr'
      have hstate := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecords_state_congr
        rate rewards C_star C_h q z z' r r' hr hr' hin
      have htime : r.input.time = r'.input.time :=
        hfields.2.2.1.trans hfields'.2.2.1.symm
      have hrewards : r.input.rewards = r'.input.rewards :=
        hfields.2.2.2.trans hfields'.2.2.2.symm
      have hJ' : ActualInitializationPhysicalStep.selectedRowIndex p z' = J := by
        change PrivateSourceStreams.coordinatorIndex p z'.2.1.2 =
          PrivateSourceStreams.coordinatorIndex p z.2.1.2
        rfl
      have hcurrent : (z'.1.2 J).2 q = replaceCurrentProp ((z.1.2 J).2 q) value := by
        simp [z', c, J, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
      have hassign : ∀ t, LaterAssignmentStartOperation.ownAssignmentVector
          (z.1.2 J) t = LaterAssignmentStartOperation.ownAssignmentVector (z'.1.2 J) t :=
        selectedRow_assignmentVector_currentProp q z value
      have hactive : ∀ i, (r.input.state.activations i).val ≤ q.val + 1 := by
        intro i
        simpa only [hfields.2.2.1] using r.input.active i
      let x : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨r.input.state, z.1.2, J, q, hactive, rewards⟩
      let y : ReferenceActivePhysicalStep.RoundInput p rate :=
        ⟨r.input.state, z'.1.2, J, q, hactive, rewards⟩
      have hx : r.input = x := roundInput_eq_of_fields rfl hfields.1
        (by simpa only [J] using hfields.2.1) hfields.2.2.1 hfields.2.2.2
      have hy : r'.input = y := roundInput_eq_of_fields hstate.symm hfields'.1
        (by
          calc
            r'.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z' := hfields'.2.1
            _ = J := hJ') hfields'.2.2.1 hfields'.2.2.2
      have hphysical := physicalProjection_eq_of_current_prop rate r.input.state
        z.1.2 z'.1.2 J q hactive rewards value hcurrent hassign
      have hinputProjection :
          ((ReferenceActiveDispatchTemporal.dispatchData r.input).2,
            (ReferenceActivePhysicalStep.prepare r.input).arms.actions,
            (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback,
            (ReferenceActivePhysicalStep.step r.input).ownEntries) =
          ((ReferenceActiveDispatchTemporal.dispatchData r'.input).2,
            (ReferenceActivePhysicalStep.prepare r'.input).arms.actions,
            (ReferenceActivePhysicalStep.prepare r'.input).feedback.feedback,
            (ReferenceActivePhysicalStep.step r'.input).ownEntries) := by
        change ((ReferenceActiveDispatchTemporal.dispatchData x).2,
            (ReferenceActivePhysicalStep.prepare x).arms.actions,
            (ReferenceActivePhysicalStep.prepare x).feedback.feedback,
            (ReferenceActivePhysicalStep.step x).ownEntries) =
          ((ReferenceActiveDispatchTemporal.dispatchData y).2,
            (ReferenceActivePhysicalStep.prepare y).arms.actions,
            (ReferenceActivePhysicalStep.prepare y).feedback.feedback,
            (ReferenceActivePhysicalStep.step y).ownEntries) at hphysical
        rw [← hx, ← hy] at hphysical
        exact hphysical
      have hrecordProjection :
          ((ReferenceActiveDispatchTemporal.dispatchData r.input).2,
            r.actions, r.gridFeedback, r.ownEntries) =
          ((ReferenceActiveDispatchTemporal.dispatchData r'.input).2,
            r'.actions, r'.gridFeedback, r'.ownEntries) := by
        have hleft : ((ReferenceActiveDispatchTemporal.dispatchData r.input).2,
            r.actions, r.gridFeedback, r.ownEntries) =
            ((ReferenceActiveDispatchTemporal.dispatchData r.input).2,
              (ReferenceActivePhysicalStep.prepare r.input).arms.actions,
              (ReferenceActivePhysicalStep.prepare r.input).feedback.feedback,
              (ReferenceActivePhysicalStep.step r.input).ownEntries) := by
          change ((ReferenceActiveDispatchTemporal.dispatchData r.input).2,
              r.output.preparation.arms.actions,
              r.output.preparation.feedback.feedback, r.output.ownEntries) = _
          rw [r.output_eq]
          rfl
        have hright : ((ReferenceActiveDispatchTemporal.dispatchData r'.input).2,
            r'.actions, r'.gridFeedback, r'.ownEntries) =
            ((ReferenceActiveDispatchTemporal.dispatchData r'.input).2,
              (ReferenceActivePhysicalStep.prepare r'.input).arms.actions,
              (ReferenceActivePhysicalStep.prepare r'.input).feedback.feedback,
              (ReferenceActivePhysicalStep.step r'.input).ownEntries) := by
          change ((ReferenceActiveDispatchTemporal.dispatchData r'.input).2,
              r'.output.preparation.arms.actions,
              r'.output.preparation.feedback.feedback, r'.output.ownEntries) = _
          rw [r'.output_eq]
          rfl
        exact hleft.trans (hinputProjection.trans hright.symm)
      rw [hr']
      simp only [Option.map_some]
      exact congrArg some hrecordProjection

end Bandits.Support.ReferenceOriginalCalendarProposalFreePhysicalOperations

end
