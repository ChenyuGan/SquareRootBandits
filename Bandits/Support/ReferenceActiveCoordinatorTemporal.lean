/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStep

/-!
# Conditional temporal locality of coordinator operations

Sources: `sources/zip4/manuscript/06_interruptions.tex:197-209,235-297,376-423`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

These are conditional equalities of the accepted local operations on two
preparations of the same state, selected row index, time, and reward table
interface. They preserve every check, rejection, suppression, and failure
branch. The current operation comparisons do not assert equality of complete
rounds, histories, probabilities, or horizon executions.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceActiveCoordinatorTemporal

open Bandits.Support.ReferenceActivePhysicalStep

private theorem recorder_run_eq_of_current_control
    {p : Parameters} {rate : RateInput p} {payload : Payload rate}
    (left right : Bandits.Support.CoordinatorRecorderComplementBridge.Input payload)
    (hcurrent : left.row.2 left.time = right.row.2 right.time)
    (hweights : left.currentWeights = right.currentWeights)
    (htime : left.time = right.time)
    (hboundary : left.gridBoundary = right.gridBoundary)
    (harm : left.ownArm = right.ownArm)
    (hobs : left.observation = right.observation)
    (hmode : left.mode = right.mode) :
    Bandits.Support.CoordinatorRecorderComplementBridge.run left =
      Bandits.Support.CoordinatorRecorderComplementBridge.run right := by
  let base := Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput left
  let leftValue : Bandits.Support.CoordinatorRecordingMeasurability.RecorderDomain p :=
    (left.row, (left.ownArm, left.observation))
  let rightValue : Bandits.Support.CoordinatorRecordingMeasurability.RecorderDomain p :=
    (right.row, (right.ownArm, right.observation))
  have hleft : Bandits.Support.CoordinatorRecordingMeasurability.inputAt base leftValue =
      Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput left := by
    rfl
  have hright : Bandits.Support.CoordinatorRecordingMeasurability.inputAt base rightValue =
      Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput right := by
    cases left with
    | mk leftWeights leftTime leftBoundary leftRow leftArm leftObservation leftMode =>
      cases right with
      | mk rightWeights rightTime rightBoundary rightRow rightArm rightObservation rightMode =>
        have hweights' : leftWeights = rightWeights := by
          change leftWeights = rightWeights at hweights
          exact hweights
        have htime' : leftTime = rightTime := by
          change leftTime = rightTime at htime
          exact htime
        have hboundary' : leftBoundary = rightBoundary := by
          change leftBoundary = rightBoundary at hboundary
          exact hboundary
        have hmode' : leftMode = rightMode := by
          change leftMode = rightMode at hmode
          exact hmode
        have hweightsExt' :
            Bandits.Support.CoordinatorRecorderComplementBridge.extendedCurrentWeights
                ({ currentWeights := rightWeights, time := rightTime,
                    gridBoundary := rightBoundary, row := leftRow, ownArm := leftArm,
                    observation := leftObservation, mode := rightMode } :
                  Bandits.Support.CoordinatorRecorderComplementBridge.Input payload) =
              Bandits.Support.CoordinatorRecorderComplementBridge.extendedCurrentWeights
                ({ currentWeights := rightWeights, time := rightTime,
                    gridBoundary := rightBoundary, row := rightRow, ownArm := rightArm,
                    observation := rightObservation, mode := rightMode } :
                  Bandits.Support.CoordinatorRecorderComplementBridge.Input payload) := rfl
        simp only [base, rightValue,
          Bandits.Support.CoordinatorRecordingMeasurability.inputAt,
          Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
          Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights,
          hweightsExt', hweights', htime', hboundary', hmode',
          Bandits.Support.CoordinatorRecorderComplementBridge.operationMode]
  have hcurrent' := hcurrent
  rw [← htime] at hcurrent'
  have hslice :
      Bandits.Support.ContinuousLearningRows.sliceAt left.time left.row.2 =
        Bandits.Support.ContinuousLearningRows.sliceAt left.time right.row.2 := by
    change (left.row.2 left.time).1 = (right.row.2 left.time).1
    exact congrArg Prod.fst hcurrent'
  have hslice' :
      Bandits.Support.ContinuousLearningRows.sliceAt base.time left.row.2 =
        Bandits.Support.ContinuousLearningRows.sliceAt base.time right.row.2 := by
    simpa [base,
      Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput,
      Bandits.Support.CoordinatorRecorderComplementBridge.recorderInputWithWeights] using hslice
  have hrun :=
    Bandits.Support.CoordinatorRecordingMeasurability.run_eq_of_current_slice_eq
      base leftValue rightValue hslice' harm hobs
  calc
    Bandits.Support.CoordinatorRecorderComplementBridge.run left =
        Bandits.Support.CoordinatorRecordingOperation.run
          (Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput left) :=
      Bandits.Support.CoordinatorRecorderComplementBridge.run_eq_accepted left
    _ = Bandits.Support.CoordinatorRecordingOperation.run
          (Bandits.Support.CoordinatorRecordingMeasurability.inputAt base leftValue) := by
      rw [hleft]
    _ = Bandits.Support.CoordinatorRecordingOperation.run
          (Bandits.Support.CoordinatorRecordingMeasurability.inputAt base rightValue) := hrun
    _ = Bandits.Support.CoordinatorRecordingOperation.run
          (Bandits.Support.CoordinatorRecorderComplementBridge.recorderInput right) := by
      rw [hright]
    _ = Bandits.Support.CoordinatorRecorderComplementBridge.run right :=
      (Bandits.Support.CoordinatorRecorderComplementBridge.run_eq_accepted right).symm

private theorem finishRound_eq_of_current_control
    {p : Parameters} (eta : ℝ) (time : Fin p.T)
    (clock : Bandits.Support.CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1)))
    (left right : Bandits.Support.CompletePublicTable.CompleteRow p)
    (hcurrent : left.2 time = right.2 time) :
    Bandits.Support.CoordinatorPhaseClock.finishRound p eta time clock pending left =
      Bandits.Support.CoordinatorPhaseClock.finishRound p eta time clock pending right := by
  have hprop :
      (left.2 time).1 (Bandits.Support.ContinuousControlSlice.Label.prop) =
        (right.2 time).1 (Bandits.Support.ContinuousControlSlice.Label.prop) :=
    congrArg (fun control : Bandits.Support.ContinuousLearningRows.TimeControl p =>
      Bandits.Support.ContinuousControlSlice.coordinate
        Bandits.Support.ContinuousControlSlice.Label.prop control.1) hcurrent
  have hpropVal := congrArg Subtype.val hprop
  have hbit :
      Bandits.Support.FollowerCutoffScan.completeRowProposalBit p eta left time =
        Bandits.Support.FollowerCutoffScan.completeRowProposalBit p eta right time := by
    simp only [Bandits.Support.FollowerCutoffScan.completeRowProposalBit_eq,
      Bandits.Support.CompletePublicTable.completeRowLearning]
    exact congrArg (fun value : ℝ => decide (value < 4 * (p.m : ℝ) * eta)) hpropVal
  unfold Bandits.Support.CoordinatorPhaseClock.finishRound
  rw [hbit]

/-- The same literal live post-choice tail has the same complete observation
when its actual arm, current grid observation, and full current control agree.
Every recorder, service, confirmation, and finish failure branch is retained.
-/
theorem livePostChoice_eq_of_current
    {p : Parameters} {rate : RateInput p}
    (state : State p rate)
    (rows otherRows : Bandits.Support.CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards otherRewards : Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable p)
    (r : Bandits.Support.CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : Bandits.Support.CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (started : Bandits.Support.CoordinatorPhaseClock.StartRoundResult p) :
    let x : RoundInput p rate := ⟨state, rows, selected, time, active, rewards⟩
    let y : RoundInput p rate := ⟨state, otherRows, selected, time, active, otherRewards⟩
    let P : PreparedRound x := prepare x
    let Q : PreparedRound y := prepare y
    (hc : (rows selected).2 time = (otherRows selected).2 time) →
    (ha : P.coordinator.arm = Q.coordinator.arm) →
    (ho : P.coordinatorObservation = Q.coordinatorObservation) →
      livePostChoice P r q base started = livePostChoice Q r q base started := by
  intro x y P Q hc ha ho
  have hrecord :
      Bandits.Support.CoordinatorRecorderComplementBridge.run
        (liveRecordingInput P r started) =
      Bandits.Support.CoordinatorRecorderComplementBridge.run
        (liveRecordingInput Q r started) := by
    apply recorder_run_eq_of_current_control
    · exact hc
    · rfl
    · rfl
    · rfl
    · exact ha
    · exact ho
    · rfl
  let pendingAtChoice :
      Finset (Bandits.Support.ActiveRoundActions.Follower p.m) := by
    simpa [Bandits.Support.ActiveRoundActions.Follower,
      Bandits.Support.PublicDiscreteDraws.followerCount] using started.pending
  have hpending : pendingAtChoice = started.pending := rfl
  have hconfirmation :
      Bandits.Support.CoordinatorLocalArmChoice.confirmationUpdate r.payload pendingAtChoice
        (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        time (rows selected) P.coordinatorObservation =
      Bandits.Support.CoordinatorLocalArmChoice.confirmationUpdate r.payload pendingAtChoice
        (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        time (otherRows selected) Q.coordinatorObservation := by
    exact Bandits.Support.CoordinatorLocalArmChoice.confirmationUpdate_eq_of_same_current_timeControl
      r.payload pendingAtChoice
      (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      time (rows selected) (otherRows selected) P.coordinatorObservation hc |>.trans (by rw [ho])
  unfold livePostChoice
  cases hrun : Bandits.Support.CoordinatorRecorderComplementBridge.run
      (liveRecordingInput P r started) with
  | none =>
      have hrunRight := hrecord.symm.trans hrun
      simp only [hrunRight, x, y]
  | some recording =>
      have hrunRight := hrecord.symm.trans hrun
      simp only [hrunRight]
      cases hservice :
          Bandits.Support.CoordinatorLiveServiceFinish.servicePass r q recording with
      | error reason => simp only [x, y]
      | ok serviced =>
          simp only [x, y, Bandits.Support.ReferenceActivePhysicalStep.RoundInput.row]
            at hconfirmation ⊢
          rw [← hpending] at ⊢
          rw [hconfirmation]
          cases hconfirm :
              Bandits.Support.CoordinatorLocalArmChoice.confirmationUpdate r.payload pendingAtChoice
                (Bandits.Support.CoordinatorLiveChoiceRecorderStep.cutoffFromClock
                  p started.clock.u)
                time (otherRows selected) Q.coordinatorObservation with
          | none => rfl
          | some pending =>
            dsimp only at ⊢
            have hfinish := finishRound_eq_of_current_control rate.eta.val time
              started.clock pending (rows selected) (otherRows selected) hc
            rw [hfinish]

private theorem checkedUpOffer_eq_of_current
    {p : Parameters} {eta : Bandits.Support.ReferencePrelaunchFollower.LearningRate}
    (i : Fin (p.m - 1))
    (activation : Bandits.Support.ReferencePrelaunchFollower.Activation p)
    (followerState : Bandits.Support.ReferencePrelaunchFollower.State p eta)
    (row otherRow : Bandits.Support.CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (hcurrent : row.2 time = otherRow.2 time) :
    Bandits.Support.ActiveFollowerQueueOperation.checkedUpOffer eta i row activation time
        followerState =
      Bandits.Support.ActiveFollowerQueueOperation.checkedUpOffer eta i otherRow activation time
        followerState := by
  unfold Bandits.Support.ActiveFollowerQueueOperation.checkedUpOffer
    Bandits.Support.ActiveFollowerQueueOperation.selectedUpRound
  rw [hcurrent]

private theorem currentOfferWord_eq_of_same_current_control
    {p : Parameters} {rate : RateInput p}
    (left right : Bandits.Support.DeclaredFollowerLocalRound.PreparedRound p rate)
    (hfollower : left.follower = right.follower)
    (hactivation : left.activation = right.activation)
    (htime : left.time = right.time)
    (hconfiguration : left.configuration = right.configuration)
    (hcurrent : left.row.2 left.time = right.row.2 right.time) :
    Bandits.Support.ReferenceUpReception.currentOfferWord rate left.row left.follower
      left.time left rfl rfl rfl =
    Bandits.Support.ReferenceUpReception.currentOfferWord rate right.row right.follower
      right.time right rfl rfl rfl := by
  rcases left with ⟨i, row, activation, time, active, arm, configuration⟩
  rcases right with ⟨otherI, otherRow, otherActivation, otherTime, otherActive,
    otherArm, otherConfiguration⟩
  dsimp only at hfollower hactivation htime hconfiguration hcurrent
  cases hfollower
  cases hactivation
  cases htime
  cases hconfiguration
  cases configuration with
  | dagger => rfl
  | ordinary followerState memory =>
      simp only [Bandits.Support.ReferenceUpReception.currentOfferWord,
        checkedUpOffer_eq_of_current i activation followerState row otherRow time hcurrent]

private theorem currentOfferWord_eq_canonical
    {p : Parameters} {rate : RateInput p}
    (prepared : Bandits.Support.DeclaredFollowerLocalRound.PreparedRound p rate)
    (declaredRow : Bandits.Support.CompletePublicTable.CompleteRow p)
    (follower : Fin (p.m - 1)) (time : Fin p.T)
    (hrow : prepared.row = declaredRow)
    (hfollower : prepared.follower = follower) (htime : prepared.time = time) :
    Bandits.Support.ReferenceUpReception.currentOfferWord rate declaredRow follower time
      prepared hrow hfollower htime =
    Bandits.Support.ReferenceUpReception.currentOfferWord rate prepared.row prepared.follower
      prepared.time prepared rfl rfl rfl := rfl

/-- The actual filtered receiver agrees when its complete current reception
input and the selected prepared sender configuration agree. Its checked result
and every raw/parsed diagnostic field are compared, including rejected and
suppressed offers. -/
theorem receiveUp_eq_of_current
    {p : Parameters} {rate : RateInput p}
    (state : State p rate)
    (rows otherRows : Bandits.Support.CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards otherRewards : Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable p)
    (ledger : Ledger rate) :
    let x : RoundInput p rate := ⟨state, rows, selected, time, active, rewards⟩
    let y : RoundInput p rate := ⟨state, otherRows, selected, time, active, otherRewards⟩
    let P : PreparedRound x := prepare x
    let Q : PreparedRound y := prepare y
    (hc : (rows selected).2 time = (otherRows selected).2 time) →
    (ho : P.coordinatorObservation = Q.coordinatorObservation) →
    (hs : (P.followers.followers (upSenderIndex x)).configuration =
      (Q.followers.followers (upSenderIndex x)).configuration) →
      receiveUp P ledger = receiveUp Q ledger := by
  intro x y P Q hc ho hs
  have hi : upSenderIndex x = upSenderIndex y := by
    unfold upSenderIndex RoundInput.row
    exact congrArg Bandits.Support.CoordinatorUpMeasurability.selectedFollowerIndex hc
  have hcxy : x.row.2 time = y.row.2 time := hc
  let leftSender := P.followers.followers (upSenderIndex x)
  let rightSender := Q.followers.followers (upSenderIndex y)
  have hleftAlignment := P.follower_alignment (upSenderIndex x)
  have hrightAlignment := Q.follower_alignment (upSenderIndex y)
  have hfollower : leftSender.follower = rightSender.follower := by
    calc
      leftSender.follower = upSenderIndex x := hleftAlignment.2.1
      _ = upSenderIndex y := hi
      _ = rightSender.follower := hrightAlignment.2.1.symm
  have hactivation : leftSender.activation = rightSender.activation := by
    calc
      leftSender.activation = state.activations (upSenderIndex x) := hleftAlignment.2.2.2
      _ = state.activations (upSenderIndex y) := by rw [hi]
      _ = rightSender.activation := hrightAlignment.2.2.2.symm
  have htime : leftSender.time = rightSender.time := by
    exact hleftAlignment.2.2.1.trans hrightAlignment.2.2.1.symm
  have hconfiguration : leftSender.configuration = rightSender.configuration := by
    simpa [leftSender, rightSender, hi.symm] using hs
  have hsenderCurrent : leftSender.row.2 leftSender.time =
      rightSender.row.2 rightSender.time := by
    rw [hleftAlignment.1, hleftAlignment.2.2.1,
      hrightAlignment.1, hrightAlignment.2.2.1]
    exact hcxy
  have hword : upExpected P = upExpected Q := by
    have h := currentOfferWord_eq_of_same_current_control leftSender rightSender
      hfollower hactivation htime hconfiguration hsenderCurrent
    have hleftCanonical :
        Bandits.Support.ReferenceUpReception.currentOfferWord rate x.row
          (upSenderIndex x) x.time leftSender hleftAlignment.1
          hleftAlignment.2.1 hleftAlignment.2.2.1 =
        Bandits.Support.ReferenceUpReception.currentOfferWord rate leftSender.row
          leftSender.follower leftSender.time leftSender rfl rfl rfl := rfl
    have hrightCanonical :
        Bandits.Support.ReferenceUpReception.currentOfferWord rate y.row
          (upSenderIndex y) y.time rightSender hrightAlignment.1
          hrightAlignment.2.1 hrightAlignment.2.2.1 =
        Bandits.Support.ReferenceUpReception.currentOfferWord rate rightSender.row
          rightSender.follower rightSender.time rightSender rfl rfl rfl := rfl
    unfold upExpected
    calc
      _ = Bandits.Support.ReferenceUpReception.currentOfferWord rate leftSender.row
            leftSender.follower leftSender.time leftSender rfl rfl rfl := hleftCanonical
      _ = Bandits.Support.ReferenceUpReception.currentOfferWord rate rightSender.row
            rightSender.follower rightSender.time rightSender rfl rfl rfl := h
      _ = _ := hrightCanonical.symm
  have hinputs : upInputs P ledger = upInputs Q ledger := by
    change (ledger, (state.upDecoderBank, (time, P.coordinatorObservation))) =
      (ledger, (state.upDecoderBank, (time, Q.coordinatorObservation)))
    exact congrArg (fun observation =>
      (ledger, (state.upDecoderBank, (time, observation)))) ho
  let inputs := upInputs P ledger
  have hinput :
      Bandits.Support.ReferenceUpReception.receptionInputAtRow rate x.row inputs time =
        Bandits.Support.ReferenceUpReception.receptionInputAtRow rate y.row inputs time := by
    unfold Bandits.Support.ReferenceUpReception.receptionInputAtRow
      Bandits.Support.CoordinatorUpMeasurability.receptionInputAtRow
    rw [hcxy]
  have hleftFollower : leftSender.follower =
      (Bandits.Support.ReferenceUpReception.receptionInputAtRow rate x.row inputs time).selectedFollower := by
    rw [Bandits.Support.ReferenceUpReception.receptionInputAtRow_selectedFollower]
    simpa [upSenderIndex, RoundInput.row, x, leftSender] using hleftAlignment.2.1
  have hrightFollower : rightSender.follower =
      (Bandits.Support.ReferenceUpReception.receptionInputAtRow rate y.row inputs time).selectedFollower := by
    rw [Bandits.Support.ReferenceUpReception.receptionInputAtRow_selectedFollower]
    simpa [upSenderIndex, RoundInput.row, y, rightSender] using hrightAlignment.2.1
  have hinputTime : inputs.2.2.1 = time := rfl
  have hleftTime : leftSender.time =
      (Bandits.Support.ReferenceUpReception.receptionInputAtRow rate x.row inputs time).time := by
    rw [Bandits.Support.ReferenceUpReception.receptionInputAtRow_inputTime]
    simpa [inputs, upInputs, x] using hleftAlignment.2.2.1
  have hrightTime : rightSender.time =
      (Bandits.Support.ReferenceUpReception.receptionInputAtRow rate y.row inputs time).time := by
    rw [Bandits.Support.ReferenceUpReception.receptionInputAtRow_inputTime]
    simpa [inputs, upInputs, y] using hrightAlignment.2.2.1
  have hsameFollower : leftSender.follower = rightSender.follower :=
    hleftFollower.trans
      ((congrArg Bandits.Support.CoordinatorUpReception.ReceptionInput.selectedFollower hinput).trans
        hrightFollower.symm)
  have hsameTime : leftSender.time = rightSender.time :=
    hleftTime.trans ((congrArg Bandits.Support.CoordinatorUpReception.ReceptionInput.time hinput).trans
      hrightTime.symm)
  have hwordPrepared := currentOfferWord_eq_of_same_current_control leftSender rightSender
    hsameFollower hactivation hsameTime hconfiguration hsenderCurrent
  have hfiltered :
      Bandits.Support.ReferenceUpReception.receiveUpFilteredAtRow rate x.row inputs time leftSender
          hleftAlignment.1 hleftFollower hleftTime hinputTime =
        Bandits.Support.ReferenceUpReception.receiveUpFilteredAtRow rate y.row inputs time rightSender
          hrightAlignment.1 hrightFollower hrightTime hinputTime := by
    simp only [Bandits.Support.ReferenceUpReception.receiveUpFilteredAtRow,
      currentOfferWord_eq_canonical, hinput, hwordPrepared]
  have hwrong :
      Bandits.Support.ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate x.row inputs time
          leftSender hleftAlignment.1 hleftFollower hleftTime hinputTime =
        Bandits.Support.ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate y.row inputs time
          rightSender hrightAlignment.1 hrightFollower hrightTime hinputTime := by
    simp only [Bandits.Support.ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow,
      currentOfferWord_eq_canonical, hinput, hwordPrepared]
    cases (Bandits.Support.CoordinatorUpReception.decoderTransition
      (Bandits.Support.ReferenceUpReception.receptionInputAtRow rate x.row inputs time)).2 <;> rfl
  have hresult : (receiveUp P ledger).result = (receiveUp Q ledger).result := by
    change Bandits.Support.ReferenceUpReception.receiveUpFilteredAtRow rate x.row
        (upInputs P ledger) time leftSender hleftAlignment.1 hleftFollower hleftTime hinputTime =
      Bandits.Support.ReferenceUpReception.receiveUpFilteredAtRow rate y.row
        (upInputs Q ledger) time rightSender hrightAlignment.1 hrightFollower hrightTime hinputTime
    simpa only [hinputs.symm] using hfiltered
  have hinputRows :
      Bandits.Support.ReferenceUpReception.receptionInputAtRow rate (rows selected) inputs time =
        Bandits.Support.ReferenceUpReception.receptionInputAtRow rate (otherRows selected) inputs time := by
    simpa [x, y, RoundInput.row] using hinput
  have hwrongRows :
      Bandits.Support.ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate
          (rows selected) inputs time (P.followers.followers (upSenderIndex x))
          (hleftAlignment.1) (hleftFollower) (hleftTime) hinputTime =
        Bandits.Support.ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate
          (otherRows selected) inputs time (Q.followers.followers (upSenderIndex y))
          (hrightAlignment.1) (hrightFollower) (hrightTime) hinputTime := by
    simpa [x, y, RoundInput.row, inputs, leftSender, rightSender] using hwrong
  have hdiagnostic : (receiveUp P ledger).diagnostic = (receiveUp Q ledger).diagnostic := by
    simp only [receiveUp]
    simp only [x, y, RoundInput.row, inputs,
      hinputs.symm, hinputRows.symm, hword.symm, hwrongRows]
    rfl
  cases hleft : receiveUp P ledger with
  | mk leftResult leftDiagnostic =>
      cases hright : receiveUp Q ledger with
      | mk rightResult rightDiagnostic =>
          have hresult' : leftResult = rightResult := by
            simpa [hleft, hright] using hresult
          have hdiagnostic' : leftDiagnostic = rightDiagnostic := by
            simpa [hleft, hright] using hdiagnostic
          cases hresult'
          cases hdiagnostic'
          rfl

/-- The actual collection post-choice tail agrees from the same current
arm, current observation, and selected prepared sender configuration. Recorder
rejection, start-domain failure, rejected starts, both receiver outcomes, and
both finish failures remain the literal accepted branches. -/
theorem collectionPostChoice_eq_of_current
    {p : Parameters} {rate : RateInput p}
    (state : State p rate)
    (rows otherRows : Bandits.Support.CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards otherRewards : Bandits.Support.ActualInitializationPhysicalStep.GridRewardTable p)
    (payload : Payload rate) (ledger : Ledger rate)
    (started : Bandits.Support.CoordinatorPhaseClock.StartRoundResult p)
    (weights : Bandits.Support.CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    let x : RoundInput p rate := ⟨state, rows, selected, time, active, rewards⟩
    let y : RoundInput p rate := ⟨state, otherRows, selected, time, active, otherRewards⟩
    let P : PreparedRound x := prepare x
    let Q : PreparedRound y := prepare y
    (hc : (rows selected).2 time = (otherRows selected).2 time) →
    (ha : P.coordinator.arm = Q.coordinator.arm) →
    (ho : P.coordinatorObservation = Q.coordinatorObservation) →
    (hs : (P.followers.followers (upSenderIndex x)).configuration =
      (Q.followers.followers (upSenderIndex x)).configuration) →
      collectionPostChoice P payload ledger started weights =
        collectionPostChoice Q payload ledger started weights := by
  intro x y P Q hc ha ho hs
  have hrecord :
      Bandits.Support.CoordinatorRecorderComplementBridge.run
        (collectionRecordingInput P payload started weights) =
      Bandits.Support.CoordinatorRecorderComplementBridge.run
        (collectionRecordingInput Q payload started weights) := by
    apply recorder_run_eq_of_current_control
    · exact hc
    · rfl
    · rfl
    · rfl
    · exact ha
    · exact ho
    · rfl
  have hfinish : ∀ (recording : Bandits.Support.CoordinatorRecordingOperation.Output p)
      (cut : UpCut p rate),
      collectionFinish (x := x) payload started recording cut =
        collectionFinish (x := y) payload started recording cut := by
    intro recording cut
    cases cut with
    | mk result diagnostic =>
      cases result with
      | invalid =>
          simp [collectionFinish, coordinatorFailure, x, y]
      | success output =>
          rcases output with ⟨nextLedger, bank⟩
          simp only [collectionFinish]
          cases hledger : Bandits.Support.CoordinatorCollectionLedger.finishRound nextLedger with
          | invalid => rfl
          | rejected _ => rfl
          | success finished =>
              have hclock0 := finishRound_eq_of_current_control rate.eta.val time
                started.clock finished.pending (rows selected) (otherRows selected) hc
              have hclock :
                  Bandits.Support.CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                    started.clock finished.pending x.row =
                  Bandits.Support.CoordinatorPhaseClock.finishRound p rate.eta.val y.time
                    started.clock finished.pending y.row := by
                simpa [x, y, Bandits.Support.ReferenceActivePhysicalStep.RoundInput.row] using hclock0
              dsimp
              rw [hclock]
      | rejected output =>
          rcases output with ⟨nextLedger, bank⟩
          simp only [collectionFinish]
          cases hledger : Bandits.Support.CoordinatorCollectionLedger.finishRound nextLedger with
          | invalid => rfl
          | rejected _ => rfl
          | success finished =>
              have hclock0 := finishRound_eq_of_current_control rate.eta.val time
                started.clock finished.pending (rows selected) (otherRows selected) hc
              have hclock :
                  Bandits.Support.CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                    started.clock finished.pending x.row =
                  Bandits.Support.CoordinatorPhaseClock.finishRound p rate.eta.val y.time
                    started.clock finished.pending y.row := by
                simpa [x, y, Bandits.Support.ReferenceActivePhysicalStep.RoundInput.row] using hclock0
              dsimp
              rw [hclock]
  unfold collectionPostChoice
  cases hrun : Bandits.Support.CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput P payload started weights) with
  | none =>
      have hrunRight := hrecord.symm.trans hrun
      simp only [hrunRight]
      rfl
  | some recording =>
      have hrunRight := hrecord.symm.trans hrun
      simp only [hrunRight]
      cases hservice : Bandits.Support.CoordinatorCollectionLedger.startRound ledger
          (time.val + 1) (collectionEnabled ledger time)
          (Bandits.Support.CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => rfl
      | rejected rejected => rfl
      | success ledgerStarted =>
          have hcut := receiveUp_eq_of_current state rows otherRows selected time active
            rewards otherRewards ledgerStarted hc ho hs
          calc
            collectionFinish (x := x) payload started recording (receiveUp P ledgerStarted) =
                collectionFinish (x := x) payload started recording (receiveUp Q ledgerStarted) :=
              congrArg (fun cut => collectionFinish (x := x) payload started recording cut) hcut
            _ = collectionFinish (x := y) payload started recording (receiveUp Q ledgerStarted) :=
              hfinish recording (receiveUp Q ledgerStarted)

end Bandits.Support.ReferenceActiveCoordinatorTemporal

end
