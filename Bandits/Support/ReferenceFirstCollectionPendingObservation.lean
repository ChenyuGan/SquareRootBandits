/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionEmptyTailObservation

/-!
# Incoming pending observation for the actual first collection

The observer reads the incoming actual record, including the cutoff reset.
Sources: `06_interruptions.tex:425-431,459-487`,
`05_binary_transport.tex:180-240`, and
`appendix_a_local_protocol.tex:44-64,100-108` in the pinned ZIP4 manuscript.
These are internal support results, without a stopped-phase or quota claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionPendingObservation

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

/-- Literal incoming task observation, with the reset visible at the cutoff
input and the ledger pending set visible at collection inputs. -/
def Q (b : ℕ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset (Fin (p.m - 1)) :=
  match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none => ∅
  | some r =>
    match r.input.state.coordinator with
    | .live registers _ _ =>
        if registers.payload.sigma.val = b ∧
            ReferenceCollectionPhaseHistory.cutoffChosen r.input = true then Finset.univ else ∅
    | .collection payload ledger _ => if payload.sigma.val = b then ledger.pending else ∅
    | .first | .dagger => ∅

/-- Natural-calendar extension of the actual first-payload pending observer. -/
def Praw (n : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Finset (Fin (p.m - 1)) :=
  if hn : n < p.T then
    Q rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ⟨n, hn⟩ z
  else ∅

@[simp] theorem Praw_at (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Praw rate rewards C_star C_h t.val z =
      Q rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) t z := by
  simp only [Praw, dite_eq_left t.isLt]

@[simp] theorem Praw_of_horizon_le (n : ℕ) (hn : p.T ≤ n)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Praw rate rewards C_star C_h n z = ∅ := by
  simp only [Praw, dite_eq_right (Nat.not_lt.mpr hn)]

variable {rate rewards C_star C_h}


private def outcomeIsCutoff :
    ReferenceLiveDispatchOutputMeasurability.OutcomeData p → Bool
  | .cutoffChosen _ _ _ => true
  | _ => false

private theorem outcomeIsCutoff_choiceData_cont
    (x : CoordinatorRoundDispatch.LiveInput p)
    (out : CoordinatorStartRoundCutoffDispatch.Output
      x.registers x.ownedRegisters x.followerBaseScore) :
    outcomeIsCutoff (ReferenceLiveDispatchOutputMeasurability.choiceData x out
      (ReferenceLiveDispatchOutputMeasurability.OutcomeData.continuingChosen
        (ReferenceLiveDispatchOutputMeasurability.dispatchData out) out.startResult)) = false := by
  unfold ReferenceLiveDispatchOutputMeasurability.choiceData
  split_ifs <;> rfl

private def cutoffStageDispatchCheckOnInput
    (x : CoordinatorRoundDispatch.LiveInput p) : Prop :=
  ∃ out : CoordinatorStartRoundCutoffDispatch.Output
      x.registers x.ownedRegisters x.followerBaseScore,
    CoordinatorStartRoundCutoffDispatch.dispatch x.registers x.ownedRegisters
      x.followerBaseScore = .ok out ∧
    (∃ ledger, out.collectionInitialization = .success (some ledger)) ∧
    CoordinatorLocalArmChoice.ChoiceInputsValid x.registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p out.startResult.clock.u)
      x.registers.time x.registers.complementWeights ∧
    out.startResult.clock.g ≤ p.T + 1 ∧ x.registers.complementEnvelopeValid


private theorem cutoffCheck_iff_outcome
    (z : ReferenceLiveDispatchMeasurability.LiveDispatchCoordinates p rate) :
    ReferenceCutoffStageSupportMeasurability.cutoffStageDispatchCheck z.1 z.2.1 z.2.2.1 ↔
      outcomeIsCutoff (ReferenceLiveDispatchOutputMeasurability.outcomeData
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates z))) = true := by
  classical
  let x := ReferenceLiveDispatchMeasurability.liveInputOfCoordinates z
  change cutoffStageDispatchCheckOnInput x ↔
    outcomeIsCutoff (ReferenceLiveDispatchOutputMeasurability.outcomeData
      (CoordinatorRoundDispatch.dispatchLive x)) = true
  rw [ReferenceLiveDispatchOutputMeasurability.outcomeData_dispatchLive]
  dsimp only [outcomeIsCutoff]
  unfold ReferenceLiveDispatchOutputMeasurability.dataFormula
  let dispatch := CoordinatorStartRoundCutoffDispatch.dispatch x.registers
    x.ownedRegisters x.followerBaseScore
  cases hd : dispatch with
  | error failure =>
      simp [cutoffStageDispatchCheckOnInput, dispatch, hd]
  | ok out =>
      cases hi : out.collectionInitialization with
      | invalid =>
          simp [cutoffStageDispatchCheckOnInput, dispatch, hd, hi]
      | rejected rejected =>
          simp [cutoffStageDispatchCheckOnInput, dispatch, hd, hi]
      | success value =>
          cases value with
          | none =>
              have hleft : ¬ cutoffStageDispatchCheckOnInput x := by
                simp [cutoffStageDispatchCheckOnInput, dispatch, hd, hi]
              have hright : outcomeIsCutoff
                  (ReferenceLiveDispatchOutputMeasurability.dataFormula x) = false := by
                simp only [ReferenceLiveDispatchOutputMeasurability.dataFormula,
                  dispatch, hd, hi]
                split_ifs
                all_goals
                  first
                  | rfl
                  | exact outcomeIsCutoff_choiceData_cont x out
              change cutoffStageDispatchCheckOnInput x ↔
                outcomeIsCutoff (ReferenceLiveDispatchOutputMeasurability.dataFormula x) = true
              simp [hleft, hright]
          | some ledger =>
              have hledger := CoordinatorRoundDispatch.cutoffDispatch_ledger_eq_candidate
                x.registers x.ownedRegisters x.followerBaseScore out ledger hd hi
              simp only [dispatch, hd, hi]
              change cutoffStageDispatchCheckOnInput x ↔
                outcomeIsCutoff (ReferenceLiveDispatchOutputMeasurability.choiceData x out
                  (ReferenceLiveDispatchOutputMeasurability.OutcomeData.cutoffChosen
                    (ReferenceLiveDispatchOutputMeasurability.dispatchData out)
                    (ReferenceLiveDispatchOutputMeasurability.ledgerData ledger))) = true
              rw [hledger.2.2]
              unfold ReferenceLiveDispatchOutputMeasurability.choiceData
              by_cases hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                  x.registers.payload (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                    out.startResult.clock.u) x.registers.time x.registers.complementWeights
              · by_cases hclock : out.startResult.clock.g ≤ p.T + 1
                · by_cases henvelope : x.registers.complementEnvelopeValid
                  · have hselected :=
                      CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                        x.registers.payload out.startResult.pending
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                          out.startResult.clock.u) x.registers.time x.registers.complementWeights x.row hchoice
                    have hnotnone : CoordinatorLocalArmChoice.coordinatorArmChoice
                        x.registers.payload out.startResult.pending
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                          out.startResult.clock.u) x.registers.time x.registers.complementWeights x.row ≠ none :=
                      hselected
                    have hexists := Option.ne_none_iff_exists.mp hnotnone
                    rcases hexists with ⟨arm, harm⟩
                    simp only [ite_eq_left hchoice, ite_eq_left hclock, ite_eq_left henvelope]
                    rw [show CoordinatorLocalArmChoice.coordinatorArmChoice
                      x.registers.payload out.startResult.pending
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p out.startResult.clock.u)
                      x.registers.time x.registers.complementWeights x.row = some arm from harm.symm]
                    simp [hchoice, hclock, henvelope,
                      cutoffStageDispatchCheckOnInput, dispatch, hd, hi]
                    rfl
                  · simp [hchoice, hclock, henvelope, cutoffStageDispatchCheckOnInput,
                      dispatch, hd]
                    rfl
                · simp [hchoice, hclock, cutoffStageDispatchCheckOnInput,
                    dispatch, hd, hi]
                  rfl
              · simp [hchoice, cutoffStageDispatchCheckOnInput, dispatch,
                  hd, hi]
                rfl


private theorem measurable_cutoffCheck (t : Fin p.T) :
    Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
        decide (ReferenceCutoffStageSupportMeasurability.cutoffStageDispatchCheck z.1 z.2 t)) := by
  let row := CoordinatorLiveChoiceRecorderStep.dummyCompleteRow p
  have hm := ReferenceLiveDispatchOutputMeasurability.measurable_dispatchLive_outcomeData
    (p := p) (rate := rate)
  have hcoords : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
        (z.1, (z.2, (t, row)))) :=
    measurable_fst.prodMk (measurable_snd.prodMk (measurable_const.prodMk measurable_const))
  have hb : Measurable (outcomeIsCutoff (p := p)) := measurable_of_countable _
  convert hb.comp (hm.comp hcoords) using 1
  funext z
  exact Bool.eq_iff_iff.mpr (by
    simp only [decide_eq_true_eq]
    exact cutoffCheck_iff_outcome (z.1, (z.2, (t, row))))

private theorem dispatchCheck_encodeLive_iff
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hc : x.state.coordinator = .live r q base) :
    ReferenceCutoffStageSupportMeasurability.cutoffStageDispatchCheck r.payload
        (ReferenceActivePhysicalStepMeasurability.encodeLive r q base) x.time ↔
      ReferenceCollectionPhaseHistory.cutoffChosen x = true := by
  have h := cutoffCheck_iff_outcome
    (ReferenceLiveDispatchMeasurability.liveDispatchCoordinatesOfRound x r q base)
  dsimp only [ReferenceLiveDispatchMeasurability.liveDispatchCoordinatesOfRound] at h
  rw [h]
  have hi := ReferenceLiveDispatchMeasurability.liveInputOfCoordinates_liveDispatchCoordinatesOfRound
    x r q base
  dsimp only [ReferenceLiveDispatchMeasurability.liveDispatchCoordinatesOfRound] at hi
  rw [hi]
  dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen, ReferenceActivePhysicalStep.prepare,
    ReferenceActivePhysicalStep.dispatch]
  simp only [hc, CoordinatorRoundDispatch.dispatch]
  cases CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x r q base) <;> rfl

private def codePending (b : ℕ) (t : Fin p.T)
    (c : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate) :
    Finset (Fin (p.m - 1)) :=
  match c with
  | .inr (.inl (payload, live)) =>
      if payload.sigma.val = b ∧ ReferenceCutoffStageSupportMeasurability.cutoffStageDispatchCheck payload live t then Finset.univ else ∅
  | .inr (.inr (.inl (payload, ledger, _))) =>
      if payload.sigma.val = b then ledger.pending else ∅
  | _ => ∅

private theorem actualRecord_time (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    r.input.time = t := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hz.1
    have heq := Option.some.inj (hr.symm.trans
      (ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch rate rewards C_star C_h t z _ hl hz.2))
    subst r
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

private theorem Q_eq_codePending (b : ℕ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Q rate rewards C_star C_h b t z =
      ((ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z).map
        (fun c => codePending b t c.1)).getD ∅ := by
  unfold Q ReferenceSourcePrefixHistoryFiltration.incoming
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.getD_some]
    have ht := actualRecord_time t z r hr
    cases hc : r.input.state.coordinator with
    | first =>
        simp only [ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc, codePending]
    | dagger =>
        simp only [ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc, codePending]
    | collection payload ledger saved =>
        simp only [ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc, codePending]
    | live registers owned base =>
        simp only [ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hc, codePending]
        rw [← ht, dispatchCheck_encodeLive_iff r.input registers owned base hc]
        split_ifs <;> rfl

/-- Every fixed payload observer factors through the strict source prefix,
including absent and future-launch inputs. -/
theorem Q_factor (control0 : ContinuousLearningRows.TimeControl p)
    (b : ℕ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Q rate rewards C_star C_h b t z = Q rate rewards C_star C_h b t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
  rw [Q_eq_codePending, Q_eq_codePending,
    ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 t z]

private theorem measurable_codePending (b : ℕ) (t : Fin p.T) :
    Measurable (codePending (rate := rate) b t) := by
  have hsigma := (measurable_of_countable (fun v : Fin p.T => v.val)).comp
    (ReferenceCollectionDispatchMeasurability.measurable_payloadSigma (rate := rate))
  have hlive : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
        if z.1.sigma.val = b ∧
          ReferenceCutoffStageSupportMeasurability.cutoffStageDispatchCheck z.1 z.2 t
        then (Finset.univ : Finset (Fin (p.m - 1))) else ∅) := by
    have hcheck : MeasurableSet {z : ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p |
          ReferenceCutoffStageSupportMeasurability.cutoffStageDispatchCheck z.1 z.2 t} := by
      simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
        (measurable_cutoffCheck (rate := rate) t) (measurableSet_singleton true)
    exact Measurable.ite
      ((measurableSet_eq_fun (hsigma.comp measurable_fst) measurable_const).inter hcheck)
      measurable_const measurable_const
  have hcollection : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool)) =>
        if z.1.sigma.val = b then z.2.1.pending else ∅) :=
    Measurable.ite (measurableSet_eq_fun (hsigma.comp measurable_fst) measurable_const)
      ((measurable_of_countable (fun z : ReferenceActivePhysicalStep.Ledger rate ×
        Option (Fin p.T × Bool) => z.1.pending)).comp measurable_snd) measurable_const
  exact Measurable.sumElim measurable_const
    (hlive.sumElim (hcollection.sumElim measurable_const))

/-- Pending membership is measurable at the incoming source field. The
continuous payload fibre retains its product Borel structure. -/
theorem Q_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (b : ℕ) (t : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (Q rate rewards C_star C_h b t) := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)
  have hmap := ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun v : ReferenceActivePhysicalStepMeasurability.StateCode p rate ×
      BootstrapPrivateRoundStreams.SourceInput p => codePending b t v.1.1)
    ((measurable_codePending b t).comp (measurable_fst.comp measurable_fst))
    _ (ReferenceSourcePrefixHistoryFiltration.incoming_measurable
      rate rewards C_star C_h control0 t)
  have hget : Measurable (fun e : Option (Finset (Fin (p.m - 1))) => e.getD ∅) :=
    by
      have h := (Measurable.sumElim measurable_id measurable_const :
        Measurable (Sum.elim id (fun _ : PUnit => (∅ : Finset (Fin (p.m - 1)))))).comp
          (comap_measurable (Equiv.optionEquivSumPUnit (Finset (Fin (p.m - 1)))))
      convert h using 1
      funext e
      cases e <;> rfl
  convert hget.comp hmap using 1
  funext z
  exact Q_eq_codePending b t z

theorem Q_mem_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (b : ℕ) (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z | i ∈ Q rate rewards C_star C_h b t z} :=
  (Q_measurable control0 b t) (measurableSet_mem_finset i)

/-- Nonlaunch, future launch and terminal launch contribute no observed task. -/
theorem Q_eq_empty_of_not_launchBy (b : ℕ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z) :
    Q rate rewards C_star C_h b t z = ∅ := by
  simp only [Q, ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
    rate rewards C_star C_h t z hz]

/-- The variable start is handled by already-launched strata, without
asserting adaptation of the future physical start. -/
theorem Praw_mem_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z | i ∈ Praw rate rewards C_star C_h t.val z} := by
  have heq : {z | i ∈ Praw rate rewards C_star C_h t.val z} =
      ⋃ b : Fin (t.val + 1),
        ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h b.val ∩
        {z | i ∈ Q rate rewards C_star C_h b.val t z} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, Praw_at]
    constructor
    · intro hi
      have hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
          rate rewards C_star C_h t.val z := by
        by_contra hnot
        rw [Q_eq_empty_of_not_launchBy _ t z hnot] at hi
        exact Finset.notMem_empty i hi
      exact ⟨⟨ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h,
        by have hs := hz.2; omega⟩, ⟨hz.1, rfl⟩, hi⟩
    · rintro ⟨b, hb, hi⟩
      change _ ∧ ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = b.val at hb
      rw [hb.2]
      exact hi
  rw [heq]
  exact MeasurableSet.iUnion fun b =>
    (ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_measurable
      rate rewards C_star C_h control0 t b.val (by omega)).inter
      (Q_mem_measurable control0 b.val i t)

private theorem actualRecord_window (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    {source : BootstrapPrivateRoundStreams.SourceInput p} (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (n : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input.time
      source = some (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length)[n.val] := by
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hwindow := ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
    rate source rewards C_star C_h count hcross hspan hshort n
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some initial :=
    Option.eq_some_of_isSome
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).2 hcross)
  have hactive :=
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
  have htime : B[n.val].input.time.val = s + (w + n.val) := by
    have ht := hwindow.2.1
    change B[n.val].input.time.val + 1 = s + w + 1 + n.val at ht
    omega
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hindex : w + n.val < count := by
    have hb := (List.getElem?_eq_some_iff.mp hwindow.1).1
    rwa [hcount] at hb
  have hrecordAt : B[n.val] = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s (w + n.val) (by omega) hactive := by
    have hat := ReferenceLocalReleaseGateChronology.run_record_at initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s hactive count
      hspan ⟨w + n.val, hindex⟩
    apply Option.some.inj
    calc
      some B[n.val] = E.records[w + n.val]? := hwindow.1.symm
      _ = _ := by
        rw [List.getElem?_eq_getElem (by rw [hcount]; exact hindex)]
        simpa only [E, initial,
          ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
          congrArg some hat
  have hsource := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h B[n.val].input.time source initial hlaunch
    (by rw [show ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s by rfl,
      htime]; omega)
  have hsource' : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h B[n.val].input.time source =
        some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
          (w + n.val) (by omega) hactive) := by
    simpa only [show ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s by rfl,
      htime, Nat.add_sub_cancel_left] using hsource
  simpa only [B, E, w] using hsource'.trans (congrArg some hrecordAt.symm)


private theorem firstLiveWindow_cutoff
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length < records.length) :
    ReferenceCollectionPhaseHistory.cutoffChosen
      (records[(ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length]).input = true := by
  induction records with
  | nil => simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow] at hshort
  | cons r rs ih =>
      cases hc : ReferenceCollectionPhaseHistory.cutoffChosen r.input with
      | false =>
          simpa [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hc] using
            ih (by simpa [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hc] using hshort)
      | true =>
          simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hc]

section Window

variable (source : BootstrapPrivateRoundStreams.SourceInput p) (count : ℕ)
variable (hcross : (ReferenceInitializationRun.output
  (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
variable (hspan : ReferenceInitializationRun.elapsed p
  (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
variable (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
  (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan).records).length < count)
variable (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
  (rate := rate) source rewards C_star C_h count hcross hspan hshort)

/-- The actual incoming observer on any dispatch on these same inputs. The
ledger at a positive stream index is the preceding FINISH output. The same
dispatch's empty suffix supplies all indices at or beyond `ell`. -/
theorem Q_window :
    let out := d.stream
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ k : Fin B.length,
      Q rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        B[k.val].input.time source =
      if k.val = 0 then Finset.univ else
        if hk : k.val < out.ell then (out.ledgers ⟨k.val - 1, by omega⟩).pending else ∅ := by
  intro out E w B k
  have hwindow : out.window = B := out.windowIsActual
  have hrecord := actualRecord_window rewards C_star C_h count hcross hspan hshort k
  change ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
    B[k.val].input.time source = some B[k.val] at hrecord
  by_cases hz : k.val = 0
  · rw [ite_eq_left hz]
    have hhead : B[k.val] = out.cutoff.cut := by
      simpa only [hwindow, hz] using out.cutoffIsHead
    rw [hhead] at hrecord ⊢
    obtain ⟨execution⟩ := out.cutoffExecution
    have hcount : E.records.length = count :=
      ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    have hw : w < E.records.length := by rw [hcount]; exact hshort
    have hcut : ReferenceCollectionPhaseHistory.cutoffChosen out.cutoff.cut.input = true := by
      have hat := out.cutoff.cutIndex
      have heq : E.records[w] = out.cutoff.cut := (List.getElem?_eq_some_iff.mp hat).2
      rw [← heq]
      exact firstLiveWindow_cutoff E.records hw
    have hsigma : execution.live.payload.sigma.val =
        ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
      rw [← execution.payloadIsLive]
      exact out.cutoffContext.2.1
    simp only [Q, hrecord, execution.actualLive, hsigma, hcut, and_self, ite_true]
  · rw [ite_eq_right hz]
    by_cases hk : k.val < out.ell
    · rw [dite_eq_left hk]
      obtain ⟨j, r, incoming, cell, _, hr, _, hprevious⟩ :=
        out.cell_at ⟨k.val, hk⟩ (show 0 < k.val by omega)
      have hr' : r = B[k.val] := by
        rw [hwindow] at hr
        exact (List.getElem?_eq_some_iff.mp hr).2.symm
      have hcoord := cell.readyInput.1
      rw [hr'] at hcoord
      have hsigma : out.payload.sigma.val =
          ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
        rw [out.payloadMatchesCutoff]
        exact out.cutoffContext.2.1
      simp only [Q, hrecord, hcoord, hsigma, ite_true, hprevious]
    · rw [dite_eq_right hk]
      have htail := ReferenceFirstCollectionEmptyStreamSuffix.actual_first_collection_empty_stream_suffix
        rate source rewards C_star C_h count hcross hspan hshort d
      dsimp only at htail
      obtain ⟨_, _, _, _, _, _, _, _, htail⟩ := htail
      have htailk := htail k (Nat.le_of_not_gt hk)
      rcases htailk with ⟨_, _, _, _, _, _, _, _, hphase, hempty⟩
      change ReferenceCollectionPhaseHistory.CollectionPhase B[k.val].input.state.coordinator at hphase
      change ∀ cp l saved, B[k.val].input.state.coordinator = .collection cp l saved →
        l.pending = ∅ ∧ l.sigma = d.ledger.sigma at hempty
      rcases hphase with hdagger | ⟨payload, ledger, saved, hcoord⟩
      · simp only [Q, hrecord, hdagger]
      · have he := (hempty payload ledger saved hcoord).1
        simp only [Q, hrecord, hcoord, he, ite_self]

private theorem stream_pending_antitone :
    ∀ a b : Fin d.stream.ell, a.val ≤ b.val →
      (d.stream.ledgers b).pending ⊆ (d.stream.ledgers a).pending := by
  intro a b hab
  have hrec : ∀ j (hj : j < d.stream.ell), a.val ≤ j →
      (d.stream.ledgers ⟨j, hj⟩).pending ⊆ (d.stream.ledgers a).pending := by
    intro j
    induction j with
    | zero =>
        intro hj ha
        have heq : (⟨0, hj⟩ : Fin d.stream.ell) = a := by
          apply Fin.ext
          change 0 = a.val
          omega
        rw [heq]
    | succ j ih =>
        intro hj ha
        by_cases heq : a.val = j + 1
        · have heq' : (⟨j + 1, hj⟩ : Fin d.stream.ell) = a := Fin.ext heq.symm
          rw [heq']
        · obtain ⟨_, r, incoming, cell, _, _, houtput, hprevious⟩ :=
            d.stream.cell_at ⟨j + 1, hj⟩ (show 0 < j + 1 by omega)
          have hstep : (d.stream.ledgers ⟨j + 1, hj⟩).pending ⊆
              (d.stream.ledgers ⟨j, by omega⟩).pending := by
            rw [← houtput, ReferenceFirstCollectionReadyStream.cell_pending_recurrence cell, hprevious]
            cases ReferenceCollectionPhaseHistory.acceptedLabel r.input with
            | none => exact Finset.Subset.refl _
            | some i => exact Finset.erase_subset i _
          exact hstep.trans (ih (by omega) (by omega))
  exact hrec b.val b.isLt hab

include hshort d in
/-- Pending observations shrink in the same actual collection window,
including its empty physical tail. -/
theorem Q_window_nested :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ k l : Fin B.length, k.val ≤ l.val →
      Q rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        B[l.val].input.time source ⊆
      Q rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        B[k.val].input.time source := by
  intro E w B k l hkl
  rw [Q_window source count hcross hspan hshort d l,
    Q_window source count hcross hspan hshort d k]
  by_cases hk0 : k.val = 0
  · rw [ite_eq_left hk0]
    exact Finset.subset_univ _
  · rw [ite_eq_right hk0, ite_eq_right (show l.val ≠ 0 by omega)]
    by_cases hl : l.val < d.stream.ell
    · rw [dite_eq_left hl, dite_eq_left (show k.val < d.stream.ell by omega)]
      exact stream_pending_antitone source count hcross hspan hshort d _ _
        (show k.val - 1 ≤ l.val - 1 from Nat.sub_le_sub_right hkl 1)
    · rw [dite_eq_right hl]
      exact Finset.empty_subset _

end Window

private def inputOrigin (x : ReferenceActivePhysicalStep.RoundInput p rate) : ReferenceActivePhysicalStep.DispatchCut x → Prop
  | .live r q base _ => x.state.coordinator = .live r q base
  | .collection payload ledger _ _ _ =>
      ∃ proposal, x.state.coordinator = .collection payload ledger proposal
  | .first _ => x.state.coordinator = .first
  | .dagger => x.state.coordinator = .dagger
  | .invalidCollectionCutoff => ∃ payload ledger proposal,
      x.state.coordinator = .collection payload ledger proposal

private theorem input_origin (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    inputOrigin x (ReferenceActivePhysicalStep.prepare x).coordinator := by
  change inputOrigin x (ReferenceActivePhysicalStep.dispatch x)
  unfold ReferenceActivePhysicalStep.dispatch
  cases hc : x.state.coordinator with
  | first => simp only [CoordinatorRoundDispatch.dispatch]; exact hc
  | live r q base =>
      simp only [CoordinatorRoundDispatch.dispatch]
      exact hc
  | collection payload ledger proposal =>
      simp only [CoordinatorRoundDispatch.dispatch]
      split
      · exact ⟨proposal, hc⟩
      · exact ⟨payload, ledger, proposal, hc⟩
  | dagger => exact hc

private theorem cutoff_input_live (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    ∃ registers owned base, x.state.coordinator = .live registers owned base := by
  have ho := input_origin x
  cases hd : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | live registers owned base outcome =>
      rw [hd] at ho
      exact ⟨registers, owned, base, ho⟩
  | first outcome => simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd] at hcut; cases hcut
  | collection payload ledger clock cutoff outcome =>
      simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd] at hcut
      cases hcut
  | invalidCollectionCutoff => simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd] at hcut; cases hcut
  | dagger => simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd] at hcut; cases hcut

private theorem cutoff_next_phase (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen x = true) :
    ReferenceCollectionPhaseHistory.CollectionPhase (ReferenceActivePhysicalStep.step x).next.coordinator := by
  rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
  cases hd : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | live old oldOwned oldBase outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hi he hv hc hp ha arm =>
          rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
            (ReferenceActivePhysicalStep.prepare x) old oldOwned oldBase _ hd]
          split
          · exact Or.inl rfl
          · exact ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
              (ReferenceActivePhysicalStep.prepare x) old.payload
              (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
              (ReferenceActivePhysicalStep.liveRegistersAt old x.time).complementWeights
      | _ => simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd] at hcut; cases hcut
  | _ => simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd] at hcut; cases hcut

/-- Strict physical birth times prevent an old payload from disappearing and
then being installed again inside the same computed run. -/
private theorem run_old_payload_before
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (table : ActualInitializationPhysicalStep.GridRewardTable p) (start n m : ℕ)
    (hspan : start + n ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hmn : m ≤ n) (hm : 0 < m) (payload : ReferenceActivePhysicalStep.Payload rate)
    (hsigma : payload.sigma.val = start)
    (hstored : ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows J table start n hspan active).finalState.coordinator =
        some payload) :
    ReferenceAssignmentPayloadPersistence.storedPayload
      (ReferenceActivePhysicalHorizon.run initial rows J table start m (by omega) active).finalState.coordinator =
        some payload := by
  induction n generalizing m payload with
  | zero => omega
  | succ n ih =>
      by_cases heq : m = n + 1
      · subst m
        exact hstored
      · have hn : 0 < n := by omega
        let r := ReferenceAssignmentPayloadChronology.actualRunRecordAt
          initial rows J table start n hspan active
        have hnext : ReferenceAssignmentPayloadPersistence.storedPayload
            (ReferenceActivePhysicalStep.step r.input).next.coordinator = some payload := by
          rw [ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt]
            at hstored
          exact hstored
        rcases ReferenceAssignmentPayloadChronology.actualStep_payload_classification r.input with
          hnone | ⟨old, hold, hout⟩ | ⟨fresh, hbirth, hout⟩
        · rw [hnext] at hnone
          cases hnone
        · have holdEq : old = payload := Option.some.inj (hout.symm.trans hnext)
          subst old
          change ReferenceAssignmentPayloadPersistence.storedPayload
            (ReferenceActivePhysicalHorizon.run initial rows J table start n (by omega) active).finalState.coordinator =
              some payload at hold
          exact ih m (by omega) (by omega) hm payload hsigma hold
        · have hfreshEq : fresh = payload := Option.some.inj (hout.symm.trans hnext)
          have htime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
            (ReferenceAssignmentPayloadChronology.actualStepRecord r.input) fresh hbirth
          rw [hfreshEq, hsigma] at htime
          change start = start + n at htime
          omega

private theorem run_old_live_no_cutoff
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (table : ActualInitializationPhysicalStep.GridRewardTable p) (start n : ℕ)
    (hspan : start + n ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers) (base : Fin (p.m - 1) → ℕ)
    (hlive : (ReferenceActivePhysicalHorizon.run initial rows J table start n hspan active).finalState.coordinator =
      .live registers owned base) (hsigma : registers.payload.sigma.val = start) :
    ∀ r ∈ (ReferenceActivePhysicalHorizon.run initial rows J table start n hspan active).records,
      ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
  induction n generalizing registers owned base with
  | zero => simp only [ReferenceActivePhysicalHorizon.run_zero_records, List.not_mem_nil, false_implies, implies_true]
  | succ n ih =>
      let r := ReferenceAssignmentPayloadChronology.actualRunRecordAt
        initial rows J table start n hspan active
      have hnext : (ReferenceActivePhysicalStep.step r.input).next.coordinator =
          .live registers owned base := by
        rw [ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt] at hlive
        exact hlive
      have hlast : ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
        cases hc : ReferenceCollectionPhaseHistory.cutoffChosen r.input with
        | false => rfl
        | true =>
            have hp := cutoff_next_phase r.input hc
            rw [hnext] at hp
            rcases hp with hp | ⟨_, _, _, hp⟩ <;> cases hp
      have hprev : ∀ q ∈ (ReferenceActivePhysicalHorizon.run initial rows J table start n
          (by omega) active).records, ReferenceCollectionPhaseHistory.cutoffChosen q.input = false := by
        by_cases hn : n = 0
        · subst n
          simp only [ReferenceActivePhysicalHorizon.run_zero_records, List.not_mem_nil, false_implies, implies_true]
        · obtain ⟨old, oldOwned, oldBase, hold, hs, _⟩ :=
            ReferenceLocalReleaseGateChronology.step_old_live_predecessor r.input start
              registers owned base hnext hsigma (show start < r.input.time.val by
                change start < start + n
                omega)
          exact ih (by omega) old oldOwned oldBase hold hs
      rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt]
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hprev q hq
      · have heq : q = r := List.mem_singleton.mp hq
        subst q
        exact hlast

private theorem first_collection_mem_of_split
    (before : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (during suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hbefore : ∀ q ∈ before, ReferenceCollectionPhaseHistory.cutoffChosen q.input = false)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true)
    (hduring : ∀ q ∈ during, ReferenceCollectionPhaseHistory.laterChosen q.input = false)
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)} (hr : r ∈ cut :: during) :
    r ∈ ReferenceCollectionPhaseHistory.collectionWindow (before ++ cut :: (during ++ suffix))
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (before ++ cut :: (during ++ suffix))).length := by
  have hfirst : ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (before ++ cut :: (during ++ suffix)) = before := by
    unfold ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    rw [List.takeWhile_append_of_pos (fun q hq => by rw [hbefore q hq]; rfl)]
    simp [hcut]
  rw [hfirst]
  unfold ReferenceCollectionPhaseHistory.collectionWindow
  rw [List.drop_append_length, List.drop_add_one_eq_tail_drop, List.drop_append_length]
  simp only [List.tail_cons, List.take_succ_cons, List.take_zero, List.singleton_append]
  rw [List.takeWhile_append_of_pos (fun q hq => by rw [hduring q hq]; rfl)]
  rcases List.mem_cons.mp hr with hr | hr
  · subst r
    exact List.mem_cons_self
  · exact List.mem_cons_of_mem cut (List.mem_append_left _ hr)

private theorem run_prefix_take
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (table : ActualInitializationPhysicalStep.GridRewardTable p) (start count n : ℕ)
    (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (hn : n ≤ count) :
    (ReferenceActivePhysicalHorizon.run initial rows J table start n (by omega) active).records =
      (ReferenceActivePhysicalHorizon.run initial rows J table start count hspan active).records.take n := by
  obtain ⟨suffix, he⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows J table start n (count - n) (by omega) active
  have he' : (ReferenceActivePhysicalHorizon.run initial rows J table start count hspan active).records =
      (ReferenceActivePhysicalHorizon.run initial rows J table start n (by omega) active).records ++ suffix := by
    simpa only [Nat.add_sub_of_le hn] using he
  rw [he', List.take_append_of_le_length (by rw [ReferenceActivePhysicalHorizon.run_record_count])]
  exact (List.take_of_length_le (by rw [ReferenceActivePhysicalHorizon.run_record_count])).symm

private theorem run_cutoff_mem_first_collection
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (table : ActualInitializationPhysicalStep.GridRewardTable p) (start count : ℕ)
    (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (j : Fin count)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers) (base : Fin (p.m - 1) → ℕ)
    (hlive : (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J table
      start j.val (by have hj := j.isLt; omega) active).input.state.coordinator = .live registers owned base)
    (hsigma : registers.payload.sigma.val = start)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J table
        start j.val (by have hj := j.isLt; omega) active).input = true) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J table start count hspan active
    ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J table
      start j.val (by have hj := j.isLt; omega) active ∈
      ReferenceCollectionPhaseHistory.collectionWindow E.records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length := by
  intro E
  let r := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J table
    start j.val (by have hj := j.isLt; omega) active
  let P := ReferenceActivePhysicalHorizon.run initial rows J table start j.val (by have hj := j.isLt; omega) active
  have hbefore := run_old_live_no_cutoff initial rows J table start j.val (by have hj := j.isLt; omega)
    active registers owned base hlive hsigma
  obtain ⟨suffix, he⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows J table start (j.val + 1) (count - (j.val + 1)) (by have hj := j.isLt; omega) active
  have hfull : E.records = P.records ++ r :: ([] ++ suffix) := by
    simpa only [Nat.add_sub_of_le (show j.val + 1 ≤ count by have hj := j.isLt; omega),
      ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt,
      List.append_assoc, List.singleton_append, List.nil_append] using he
  rw [hfull]
  exact first_collection_mem_of_split P.records r [] suffix hbefore hcut
    (by simp) List.mem_cons_self

private theorem run_collection_mem_first_collection
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (table : ActualInitializationPhysicalStep.GridRewardTable p) (start count : ℕ)
    (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) (j : Fin count)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hcollection : (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J table
      start j.val (by have hj := j.isLt; omega) active).input.state.coordinator = .collection payload ledger saved)
    (hsigma : payload.sigma.val = start) (hpending : ledger.pending.Nonempty) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J table start count hspan active
    ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J table
      start j.val (by have hj := j.isLt; omega) active ∈
      ReferenceCollectionPhaseHistory.collectionWindow E.records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length := by
  intro E
  let r := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J table
    start j.val (by have hj := j.isLt; omega) active
  let P := ReferenceActivePhysicalHorizon.run initial rows J table start j.val (by have hj := j.isLt; omega) active
  have hPcollection : P.finalState.coordinator = .collection payload ledger saved := hcollection
  obtain ⟨before, cut, during, hsplit, hcut, _, hduring, _⟩ :=
    ReferenceCollectionPhaseHistory.run_history initial rows J table start j.val
      (by have hj := j.isLt; omega) active hfirst payload ledger saved hPcollection
  let a := before.length
  have hlen : P.records.length = j.val := ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have ha : a < j.val := by rw [hsplit, List.length_append, List.length_cons] at hlen; dsimp [a]; omega
  have hget : P.records[a]? = some cut := by rw [hsplit]; simp [a]
  have hcutEq : cut = ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J table
      start a (by have hj := j.isLt; omega) active :=
    (List.getElem?_eq_some_iff.mp hget).2.symm.trans
      (ReferenceLocalReleaseGateChronology.run_record_at initial rows J table start active
        j.val (by have hj := j.isLt; omega) ⟨a, ha⟩)
  have hcutState : cut.input.state =
      (ReferenceActivePhysicalHorizon.run initial rows J table start a (by have hj := j.isLt; omega) active).finalState := by
    rw [hcutEq]
    rfl
  obtain ⟨registers, owned, base, hlive⟩ := cutoff_input_live cut.input hcut
  have haPos : 0 < a := by
    by_contra hnot
    have ha0 : a = 0 := by omega
    rw [hcutState] at hlive
    have hlive0 : initial.coordinator = .live registers owned base := by
      simpa only [ha0, ReferenceActivePhysicalHorizon.run_zero_final] using hlive
    rw [hfirst] at hlive0
    cases hlive0
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload P.finalState.coordinator = some payload := by
    rw [hPcollection]
    rfl
  have hstoredCut := run_old_payload_before initial rows J table start j.val a
    (by have hj := j.isLt; omega) active (Nat.le_of_lt ha) haPos payload hsigma hstored
  rw [← hcutState, hlive] at hstoredCut
  have hpayload : registers.payload = payload := Option.some.inj hstoredCut
  have hbeforeRecords :
      (ReferenceActivePhysicalHorizon.run initial rows J table start a (by have hj := j.isLt; omega) active).records = before := by
    rw [run_prefix_take initial rows J table start j.val a
      (by have hj := j.isLt; omega) active (Nat.le_of_lt ha), hsplit]
    simp [a]
  have hbefore := run_old_live_no_cutoff initial rows J table start a (by have hj := j.isLt; omega)
    active registers owned base (by rw [← hcutState]; exact hlive)
    (by rw [hpayload]; exact hsigma)
  rw [hbeforeRecords] at hbefore
  have hcurrent : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
    cases hc : ReferenceCollectionPhaseHistory.laterChosen r.input with
    | false => rfl
    | true =>
        obtain ⟨cp, l, proposal, he, hempty⟩ := ReferenceCollectionPhaseHistory.laterChosen_pending_empty r.input hc
        rw [hcollection] at he
        cases he
        exact (Finset.nonempty_iff_ne_empty.mp hpending hempty).elim
  obtain ⟨suffix, he⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows J table start (j.val + 1) (count - (j.val + 1)) (by have hj := j.isLt; omega) active
  have hfull : E.records = before ++ cut :: ((during ++ [r]) ++ suffix) := by
    simpa only [Nat.add_sub_of_le (show j.val + 1 ≤ count by have hj := j.isLt; omega),
      ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt, hsplit,
      List.append_assoc, List.cons_append, List.singleton_append] using he
  rw [hfull]
  apply first_collection_mem_of_split before cut (during ++ [r]) suffix hbefore hcut
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact (hduring q hq).2
    · have heq : q = r := List.mem_singleton.mp hq
      subst q
      exact hcurrent
  · exact List.mem_cons_of_mem cut (List.mem_append_right _ (List.mem_singleton_self _))

/-- Every nonempty actual first-payload pending observation occurs in the
first collection window of the complete physical suffix. The proof excludes
resurrection using actual step classification and strict installation times. -/
theorem Praw_localization (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hP : (Praw rate rewards C_star C_h t.val z).Nonempty) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let B := ReferenceCollectionPhaseHistory.collectionWindow R
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    ∃ k : Fin B.length, B[k.val].input.time = t := by
  intro R B
  rw [Praw_at] at hP
  have hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z := by
    by_contra hnot
    rw [Q_eq_empty_of_not_launchBy _ t z hnot] at hP
    exact Finset.not_nonempty_empty hP
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hz.1
  have hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some initial :=
    ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hz.1
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hs : s ≤ t.val := hz.2
  let active := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some rate z rewards C_star C_h initial hl
  let r := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (t.val - s) (by omega) active
  have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r :=
    ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch rate rewards C_star C_h t z initial hl hs
  have hfull : s + (p.T - s) ≤ p.T := by
    have hsT := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    dsimp only [s]
    omega
  let j : Fin (p.T - s) := ⟨t.val - s, by have ht := t.isLt; omega⟩
  have hfirst : initial.coordinator = .first := by
    have hc := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate z rewards C_star C_h hz.1).2
    have hsame : initial = ReferenceFirstCollectionEpochAlignment.actualLaunchState rate z rewards C_star C_h hz.1 :=
      Option.some.inj (hl.symm.trans (Option.eq_some_of_isSome
        ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate z rewards C_star C_h).2 hz.1)))
    rw [hsame]
    exact hc
  have hmem : r ∈ ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceActivePhysicalHorizon.run initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s) hfull active).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run initial z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s) hfull active).records).length := by
    cases hc : r.input.state.coordinator with
    | first => simp only [Q, hrecord, hc] at hP; exact (Finset.not_nonempty_empty hP).elim
    | dagger => simp only [Q, hrecord, hc] at hP; exact (Finset.not_nonempty_empty hP).elim
    | live registers owned base =>
        simp only [Q, hrecord, hc] at hP
        split_ifs at hP with h
        · exact run_cutoff_mem_first_collection initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s) hfull active j
            registers owned base hc h.1 h.2
        · exact (Finset.not_nonempty_empty hP).elim
    | collection payload ledger saved =>
        simp only [Q, hrecord, hc] at hP
        split_ifs at hP with h
        · exact run_collection_mem_first_collection initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s) hfull active hfirst j
            payload ledger saved hc h hP
        · exact (Finset.not_nonempty_empty hP).elim
  have hR : R = (ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s) hfull active).records :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch rate z rewards C_star C_h initial hl
  have hmemB : r ∈ B := by
    change r ∈ ReferenceCollectionPhaseHistory.collectionWindow R
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    rw [hR]
    exact hmem
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hmemB
  refine ⟨⟨k, hk⟩, ?_⟩
  rw [heq]
  apply Fin.ext
  change s + (t.val - s) = t.val
  omega

/-- Same-field conditional service on the actual incoming pending set.
The source almost-everywhere choice precedes every run length and interval
witness. A maximal original run and one dispatch serve all its pending dates. -/
theorem Praw_service (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      ∀ (i : Fin (p.m - 1)) (t : Fin p.T), i ∈ Praw rate rewards C_star C_h t.val z →
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          ReferenceFirstCollectionStagedConditionalService.X
            (rate := rate) rewards C_star C_h i t |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] z =
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) /
            (8 * (p.m - 1 : ℝ) * (p.K : ℝ)) := by
  filter_upwards [ReferenceFirstCollectionEmptyTailObservation.actual_initialized_first_collection_whole_window_service
    (rate := rate) rewards C_star C_h control0] with z hz
  by_cases hsupport : ∃ t : Fin p.T, (Praw rate rewards C_star C_h t.val z).Nonempty
  · obtain ⟨t0, hP0⟩ := hsupport
    have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h t0.val z := by
      by_contra hnot
      rw [Praw_at, Q_eq_empty_of_not_launchBy _ t0 z hnot] at hP0
      exact Finset.not_nonempty_empty hP0
    have hcross := hlaunch.1
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let count := p.T - s
    have hsT := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
    have hspan : s + count ≤ p.T := by dsimp only [count, s]; omega
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate z rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState rate z rewards C_star C_h hcross
    have hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some initial :=
      Option.eq_some_of_isSome
        ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate z rewards C_star C_h).2 hcross)
    have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h = E.records := by
      rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate z rewards C_star C_h initial hl]
      rfl
    have hlocAll (u : Fin p.T) (hP : (Praw rate rewards C_star C_h u.val z).Nonempty) :
        ∃ k : Fin B.length, B[k.val].input.time = u := by
      let observation := fun records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =>
        ∃ k : Fin (ReferenceCollectionPhaseHistory.collectionWindow records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length).length,
          (ReferenceCollectionPhaseHistory.collectionWindow records
            (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length)[k.val].input.time = u
      exact Eq.mp (congrArg observation hrecords) (Praw_localization u z hP)
    have hloc0 := hlocAll t0 hP0
    obtain ⟨k0, _⟩ := hloc0
    have hcount : E.records.length = count := ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    have hshort : w < count := by
      by_contra hnot
      have hw : E.records.length ≤ w := by omega
      have hw1 : E.records.length ≤ w + 1 := by omega
      have hB : B = [] := by
        simp only [B, ReferenceCollectionPhaseHistory.collectionWindow,
          List.drop_eq_nil_iff.mpr hw, List.drop_eq_nil_iff.mpr hw1,
          List.take_nil, List.takeWhile_nil, List.append_nil]
      have hk := k0.isLt
      have hBlen : B.length = 0 := congrArg List.length hB
      omega
    obtain ⟨d, hroot⟩ := hz count hcross hspan hshort
    dsimp only at hroot
    rcases hroot with ⟨hwindow, hcutoff, hcontinuing, _, _⟩
    intro i t hi
    rw [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t control0 t]
    have hloc := hlocAll t ⟨i, hi⟩
    obtain ⟨k, ht⟩ := hloc
    have hiQ : i ∈ Q rate rewards C_star C_h s B[k.val].input.time z := by
      simpa only [Praw_at, ht] using hi
    rw [Q_window z count hcross hspan hshort d k] at hiQ
    by_cases hk0 : k.val = 0
    · have hhead : B[k.val] = d.stream.cutoff.cut := by
        simpa only [hwindow, hk0] using d.stream.cutoffIsHead
      have htime : d.stream.cutoff.cut.input.time = t := by rw [← hhead]; exact ht
      simpa only [htime] using (hcutoff i).2
    · rw [ite_eq_right hk0] at hiQ
      by_cases hk : k.val < d.stream.ell
      · rw [dite_eq_left hk] at hiQ
        obtain ⟨r, incoming, old, memory, hr, hrest⟩ :=
          hcontinuing ⟨k.val, hk⟩ (show 0 < k.val by omega) i hiQ
        rcases hrest with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCE⟩
        have hrEq : r = B[k.val] := by
          rw [hwindow] at hr
          exact (List.getElem?_eq_some_iff.mp hr).2.symm
        have htime : r.input.time = t := by rw [hrEq]; exact ht
        simpa only [htime] using hCE
      · rw [dite_eq_right hk] at hiQ
        exact (Finset.notMem_empty i hiQ).elim
  · intro i t hi
    exact (hsupport ⟨t, i, hi⟩).elim

end Bandits.Support.ReferenceFirstCollectionPendingObservation

end
