/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInheritedDownFirstLiveCut
public import Bandits.Support.ReferenceAcceptedUpFollowerHistory

/-!
# Generated inherited DOWN completion after the first live window

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109`,
`sources/zip4/manuscript/05_binary_transport.tex:70-124`,
`sources/zip4/manuscript/06_interruptions.tex:246-295,303-348`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The results in this module concern the actual initialized generated run and
its retained local diagnostics. They keep failed and rejected records in the
physical chronology and make no claim about the manuscript's global closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceGeneratedDownBatchCalendar
open ReferenceGeneratedInheritedDownWrongCompletionWitness
open ReferenceAcceptedUpFollowerHistory
open ReferenceCollectionPhaseHistory

namespace Bandits.Support.ReferenceGeneratedInheritedDownPostcutExclusion

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private abbrev Record :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

private abbrev DownRecord := OrdinaryMessageCodec.DownRecord
  (ReferencePrelaunchFollower.codecParams p rate.eta)

private theorem generatedSeed_initial_state
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs) :
    let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
      rate rewards C_star C_h s hs x
    ReferenceActivePhysicalHorizon.allActiveAtStart seed s ∧
      seed.coordinator = .first ∧
      ReferenceFirstLiveConfirmationHistory.InitialFollowers seed ∧
      (∀ j : Fin (p.m - 1), ∃ state memory,
        seed.followers j = .ordinary state memory ∧ state.lastDown = none) := by
  classical
  dsimp only
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs x
  have hseedSpec := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
    rate rewards C_star C_h s hs x
  obtain ⟨active, hactive, _hunique⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate x.val rewards C_star C_h x.property.1
  have hseedActive : seed = active := Option.some.inj (hseedSpec.1.symm.trans hactive.1)
  obtain ⟨activeFields, hfieldsLaunch, hfields⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
      rate x.val rewards C_star C_h x.property.1
  have hseedFields : seed = activeFields := Option.some.inj (hseedSpec.1.symm.trans hfieldsLaunch)
  have hinitial : seed.coordinator = .first := by
    rw [hseedActive]
    exact hactive.2.1
  have hfollowers : ReferenceFirstLiveConfirmationHistory.InitialFollowers seed := by
    intro j state memory hstate
    rcases hfields j with ⟨hconfiguration, hlastDown, _, _, _, _, hunoccupied, _⟩
    have hconfiguration' :
        seed.followers j = .ordinary
          (ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate))
            (ActualReferenceInitializationBlock.refFollower j))
          (ActiveFollowerLifecycle.initialMemory p) := by
      rw [hseedFields]
      exact hconfiguration
    rw [hconfiguration'] at hstate
    cases hstate
    exact ⟨hunoccupied, hlastDown⟩
  have hseedFollowers : ∀ j : Fin (p.m - 1), ∃ state memory,
      seed.followers j = .ordinary state memory ∧ state.lastDown = none := by
    intro j
    rcases hfields j with ⟨hconfiguration, hlastDown, _, _, _, _, _, _⟩
    refine ⟨ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate))
        (ActualReferenceInitializationBlock.refFollower j),
      ActiveFollowerLifecycle.initialMemory p, ?_, hlastDown⟩
    rw [hseedFields]
    exact hconfiguration
  exact ⟨hseedSpec.2.1, hinitial, hfollowers, hseedFollowers⟩

/-- An actually retained accepted DOWN diagnostic has already executed the
decoder comparison. When its bank reaches quota, the generated calendar code
records the literal completed batch, independently of later release or finish
results. -/
private theorem retainedDown_implies_completedBatchAtRound
    (record : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (message : DownRecord (p := p) (rate := rate))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown record i message) :
    ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) := by
  classical
  rcases hretained with ⟨logged, cut, after, raw, scan, registers, lastService,
    hinput, hcut, houtcome⟩
  have hcutActual := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    record i logged cut hinput hcut
  have houtcomeActual := houtcome
  rw [hcutActual] at houtcomeActual
  let view := record.output.preparation.coordinator.downView
  let row := record.input.row
  let time := record.input.time
  let observation := ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i
  let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate logged

  have hselected : ActiveFollowerDownAcceptance.downSelected p i row time := by
    by_contra hbad
    have hresult :
        (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).outcome =
          .skipped logged .notSelectedDown := by
      simp [ReferenceDownReception.referenceDownCut, view, row, time, hbad]
    rw [hresult] at houtcomeActual
    cases houtcomeActual
  have hstatus : logged.status = .unoccupied := by
    by_contra hbad
    have hresult :
        (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).outcome =
          .skipped logged .occupiedAtChoice := by
      simp [ReferenceDownReception.referenceDownCut, view, row, time,
        hselected, hbad]
    rw [hresult] at houtcomeActual
    cases houtcomeActual
  have hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate logged := by
    by_contra hbad
    have hresult :
        (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).outcome =
          .inputFailure logged .registers := by
      simp [ReferenceDownReception.referenceDownCut, view, row, time,
        hselected, hstatus, hbad]
    rw [hresult] at houtcomeActual
    cases houtcomeActual
  have hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch := by
    by_contra hbad
    have hresult :
        (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).outcome =
          .inputFailure logged .decoderBatch := by
      simp [ReferenceDownReception.referenceDownCut, view, row, time,
        hselected, hstatus, hregisters, hbad]
    rw [hresult] at houtcomeActual
    cases houtcomeActual
  have hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer := by
    by_contra hbad
    have hresult :
        (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).outcome =
          .inputFailure logged .sparseBuffer := by
      simp [ReferenceDownReception.referenceDownCut, view, row, time,
        hselected, hstatus, hregisters, hbatch, hbad]
    rw [hresult] at houtcomeActual
    cases houtcomeActual
  have hmatches : decoded.2 =
      ReferenceDownReception.expectedDownFlatWord view i row time := by
    by_contra hbad
    have hresult :
        (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).outcome =
          .decodeOrParseRejected logged { logged with downBatch := decoded.1 } decoded.2 := by
      simp [ReferenceDownReception.referenceDownCut, view, row, time, observation,
        hselected, hstatus, hregisters, hbatch, hbuffer, decoded, hbad]
    rw [hresult] at houtcomeActual
    cases houtcomeActual
  have hcomparison :
      (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).rawComparison =
        some true := by
    simp [ReferenceDownReception.referenceDownCut, view, row, time, observation,
      hselected, hstatus, hregisters, hbatch, hbuffer, decoded, hmatches]

  have hrawDecoded : decoded.2 ≠ none := by
    intro hnone
    have hExpectedNone :
        ReferenceDownReception.expectedDownFlatWord view i row time = none :=
      hmatches.symm.trans hnone
    have hparsedNone : ReferenceDownReception.ordinaryParse p rate none = none := rfl
    have hresult :
        (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).outcome =
          .decodeOrParseRejected logged { logged with downBatch := decoded.1 } none := by
      simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
        hregisters, hbatch, hbuffer, decoded, hnone, hExpectedNone, hparsedNone]
    rw [hresult] at houtcomeActual
    cases houtcomeActual
  obtain ⟨word, hword⟩ : ∃ word, decoded.2 = some word := by
    cases hraw : decoded.2 with
    | none => exact False.elim (hrawDecoded hraw)
    | some word => exact ⟨word, rfl⟩

  have hreach : AffineBatchDecoder.quota p ≤
      (logged.downBatch.pending ++ AffineBatchDecoder.positiveAt p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate logged))
        time).length := by
    have houtput : AffineBatchDecoder.stepOutput p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate logged))
        logged.downBatch time = some word := by
      simpa only [decoded, ActiveFollowerDownAcceptance.currentDecodeStep,
        AffineBatchDecoder.decodeStep] using hword
    exact (AffineBatchDecoder.stepOutput_eq_some_iff p
      (ActiveFollowerDownAcceptance.currentInputExtension p
        (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate logged))
      logged.downBatch time word).mp houtput |>.1
  have hpositiveRound :
      AffineBatchDecoder.eligible
        (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate logged) := by
    by_cases heligible : AffineBatchDecoder.eligible
        (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate logged)
    · exact heligible
    · have hpositiveAt : AffineBatchDecoder.positiveAt p
          (ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate logged))
          time = [] := by
        simp [AffineBatchDecoder.positiveAt,
          ActiveFollowerDownAcceptance.currentInputExtension, heligible]
      rw [hpositiveAt, List.append_nil] at hreach
      exact False.elim ((Nat.not_le_of_gt hbatch.1) hreach)

  have hquota : logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p := by
    have hle : AffineBatchDecoder.quota p ≤ logged.downBatch.pending.length + 1 := by
      have hposAt : AffineBatchDecoder.positiveAt p
          (ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate logged))
          time = [AffineBatchDecoder.entry p
            (ActiveFollowerDownAcceptance.currentInputExtension p
              (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate logged))
            time] := by
        simp [AffineBatchDecoder.positiveAt,
          ActiveFollowerDownAcceptance.currentInputExtension, hpositiveRound]
      have hposLength : (AffineBatchDecoder.positiveAt p
          (ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate logged))
          time).length = 1 := by
        rw [hposAt]
        rfl
      have hsum : (logged.downBatch.pending ++ AffineBatchDecoder.positiveAt p
          (ActiveFollowerDownAcceptance.currentInputExtension p
            (ActiveFollowerDownAcceptance.currentRoundInput p i row time observation rate logged))
          time).length = logged.downBatch.pending.length + 1 := by
        simp [List.length_append, hposLength]
      rw [hsum] at hreach
      exact hreach
    exact Nat.le_antisymm (Nat.succ_le_of_lt hbatch.1) hle
  have hpositiveFeedback : 0 < observation.val.val :=
    (ActiveFollowerDownAcceptance.currentRoundInput_eligible_iff p i row time observation rate logged).mp
      hpositiveRound |>.2.2

  obtain ⟨choice, memory, actualLogged, hconfiguration, hchoiceStatus,
      hlogging, hdiagInput, hactualCut⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i cut hcut
  have hloggedEq : actualLogged = logged := Option.some.inj (hdiagInput.symm.trans hinput)
  subst actualLogged
  have hcallOrdinary := ReferenceFollowerDownDecoderReplay.actualDownCall_ordinary
    record i choice memory (by
      simpa [ReferenceFollowerDownDecoderReplay.preparedChoiceConfiguration] using hconfiguration)
  have hcallReconstruct :=
    ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_reconstructs i record
  have hcallSome : ∃ callCode,
      ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record = some callCode := by
    rw [hcallOrdinary] at hcallReconstruct
    cases hcode : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record with
    | none => simp [hcode] at hcallReconstruct
    | some callCode => exact ⟨callCode, rfl⟩
  rcases hcallSome with ⟨callCode, hcall⟩
  have hcallFields := ReferenceExecutedDownBankRecurrence.record_executed_down_call_fields
    record i callCode logged cut hcall hinput hcut (by
      rw [hcutActual, hcomparison]
      rfl) hpositiveFeedback

  have hloggedCode :
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i).2.2.2.1 =
        some (FollowerDownMeasurability.followerStateCode rate logged) := by
    rw [ReferenceGeneratedDownBatchBankBridge.roundDownObservation_diagnostics_eq_actual
      record i]
    simp [hinput]
  have hcutCode :
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i).2.2.2.2.2 =
        some (ReferenceDownCompletedAmbiguityMeasurability.cutFields cut) := by
    rw [ReferenceGeneratedDownBatchBankBridge.roundDownObservation_diagnostics_eq_actual
      record i]
    simp [hcut]
  have hcutComparison : cut.rawComparison.isSome = true := by
    rw [hcutActual, hcomparison]
    rfl
  have hbank :
      ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank callCode
          (FollowerDownMeasurability.followerStateCode rate logged) =
        ⟨[], logged.downBatch.completed ++
          [logged.downBatch.pending ++
            [⟨record.input.time, callCode.2.2.2.1⟩]]⟩ := by
    have hcodeStatus :
        FollowerDownMeasurability.followerStatusOfCode
          (FollowerDownMeasurability.followerStateCode rate logged).status = .unoccupied := by
      simpa only [FollowerDownMeasurability.followerStateCode,
        FollowerDownMeasurability.followerStatusOfCode_code] using hstatus
    have hbatchCode : FollowerDownMeasurability.decoderBatchOfCode
        (FollowerDownMeasurability.followerStateCode rate logged).downBatch =
          logged.downBatch := by
      simpa only [FollowerDownMeasurability.followerStateCode] using
        FollowerDownMeasurability.decoderBatchOfCode_code logged.downBatch
    have hinputCode :
        { selected := (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.selected,
          receiverEnabled := true,
          sample := (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.sample,
          roundedReward := (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2.roundedReward } =
        (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2 := by
      cases hi : (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2
      have hreceiver := hcallFields.2.2.2.2.2.1
      rw [hi] at hreceiver
      simp only [AffineBatchDecoder.RoundInput.mk.injEq]
      exact ⟨True.intro, hreceiver.symm, True.intro, True.intro⟩
    have hdecodedCode :
        ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank callCode
            (FollowerDownMeasurability.followerStateCode rate logged) =
          (AffineBatchDecoder.decodeStep p
            (ActiveFollowerDownAcceptance.currentInputExtension p
              (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2)
            logged.downBatch callCode.1).1 := by
      unfold ReferenceDownCompletedAmbiguityMeasurability.decodedLoggedBank
      simp only [hcodeStatus, decide_true]
      rw [hbatchCode, hinputCode]
    rw [hdecodedCode]
    have hquotaCode : logged.downBatch.pending.length + 1 = AffineBatchDecoder.quota p := hquota
    have hcomplete := AffineBatchDecoder.decodeStep_complete p
      (ActiveFollowerDownAcceptance.currentInputExtension p
        (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2)
      logged.downBatch callCode.1 hcallFields.2.2.2.2.2.2.2.1 hquotaCode
    have hentry : AffineBatchDecoder.entry p
        (ActiveFollowerDownAcceptance.currentInputExtension p
          (ReferenceDownCompletedAmbiguityMeasurability.decodeCall callCode).2)
        callCode.1 =
          ⟨record.input.time, callCode.2.2.2.1⟩ := by
      have htimeCode : callCode.1 = record.input.time := hcallFields.2.1
      simp only [AffineBatchDecoder.entry,
        ActiveFollowerDownAcceptance.currentInputExtension,
        ReferenceDownCompletedAmbiguityMeasurability.decodeCall]
      rw [htimeCode]
    rw [hcomplete]
    rw [hentry]

  unfold ReferenceGeneratedDownBatchCalendar.completedBatchAtRound
  refine ⟨callCode, FollowerDownMeasurability.followerStateCode rate logged,
    ReferenceDownCompletedAmbiguityMeasurability.cutFields cut, ?_, hloggedCode,
    hcutCode, ?_, ?_, ?_, ?_, ?_⟩
  · change ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
      some callCode
    exact hcall
  · change callCode.1 = record.input.time
    exact hcallFields.2.1
  · simpa [ReferenceDownCompletedAmbiguityMeasurability.cutFields] using hcutComparison
  · change 0 < (ActualInitializationPhysicalStep.observationOfGrid p
      (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i)).val.val
    have hgrid : ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i =
        record.gridFeedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) :=
      congrFun (ReferenceActiveHorizonMeasurability.roundRecordCode_front record).2.2.2
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    have hobs : observation = ActualInitializationPhysicalStep.observationOfGrid p
        (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i) := by
      dsimp [observation, ReferenceFollowerDownDecoderReplay.preparedOwnObservation]
      rw [hgrid]
      exact record.output.preparation.feedback.observations_eq _
    rw [← hobs]
    exact hpositiveFeedback
  · simpa only [FollowerDownMeasurability.followerStateCode,
      FollowerDownMeasurability.decoderBatchOfCode_code] using hquota
  · simpa [ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation,
      FollowerDownMeasurability.followerStateCode,
      FollowerDownMeasurability.decoderBatchOfCode_code] using hbank

/-- Before a follower's first generated completion, its actual retained
history contains neither an accepted UP reply nor a later assignment choice.
The endpoint is included. No current acceptance or control input is needed. -/
theorem generated_inherited_first_completion_no_up_or_later
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (hfirst :
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i x).2 n) ∧
        ∀ l (hl : l < n.val),
          ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i x).2 ⟨l, lt_trans hl n.isLt⟩)) :
    (∀ (k : Fin (p.T - s)), k.val ≤ n.val →
      ∀ message : ReferenceCollectionPhaseHistory.UpRecord p rate,
        ¬ ReferenceCollectionPhaseHistory.AcceptedUp
          (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
            rate rewards C_star C_h s hs x k).input i message) ∧
    (∀ (k : Fin (p.T - s)), k.val ≤ n.val →
      ReferenceCollectionPhaseHistory.laterChosen
        (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x k).input = false) := by
  classical
  let seed := generatedSourceSeed rate rewards C_star C_h s hs x
  obtain ⟨hactive, hinitial, _hfollowers, hseed⟩ :=
    generatedSeed_initial_state rate rewards C_star C_h s hs x
  let E := ReferenceActivePhysicalHorizon.run seed x.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s
    (p.T - s) (by omega) hactive
  have hrun : generatedSourceRun rate rewards C_star C_h s hs x = E := rfl
  have hlength : E.records.length = p.T - s :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hrecord (k : Fin (p.T - s)) :
      E.records[k.val]'(by omega) =
        generatedSourceRecordAt rate rewards C_star C_h s hs x k := by
    have hget := generatedSourceRecordAt_getElem? rate rewards C_star C_h s hs x k
    rw [hrun, List.getElem?_eq_getElem (by omega)] at hget
    exact Option.some.inj hget
  have hnoDown (j : Fin E.records.length) (hjn : j.val < n.val)
      (prior : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)) :
      ¬ RetainedDown E.records[j.val] i prior := by
    intro hretained
    have hcompletion := retainedDown_implies_completedBatchAtRound _ i prior hretained
    rw [hrecord ⟨j.val, by omega⟩] at hcompletion
    exact hfirst.2 j.val hjn hcompletion
  constructor
  · intro k hkn message haccepted
    obtain ⟨first, memory, hconfiguration, hlast⟩ := hseed i
    have hacceptedAt : AcceptedUp (E.records[k.val]'(by omega)).input i message := by
      rw [hrecord k]
      exact haccepted
    obtain ⟨j, hjk, prior, hretained, _⟩ :=
      run_acceptedUp_prior_down seed x.val.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s
        (p.T - s) (by omega) hactive i first memory hconfiguration hlast
        ⟨k.val, show k.val < E.records.length from by rw [hlength]; exact k.isLt⟩
        message hacceptedAt
    have hjk' : j.val < k.val := hjk
    exact hnoDown j (lt_of_lt_of_le hjk' hkn) prior hretained
  · intro k hkn
    cases hlater : laterChosen
        (generatedSourceRecordAt rate rewards C_star C_h s hs x k).input with
    | false => rfl
    | true =>
      have hlaterAt : laterChosen (nextInput seed x.val.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s k.val
          (by omega) hactive) = true := hlater
      obtain ⟨before, cutoff, during, payload, old, proposal,
          _hrecords, _hcutoff, _hcoordinator, _hempty, _hwindow, heach⟩ :=
        run_laterStart_prior_down seed x.val.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s k.val
          (by omega) hactive hinitial hseed hlaterAt
      obtain ⟨upIndex, upRecord, message, _hbefore, hup, _hupRecord, _haccepted,
          _hsigma, j, prior, sender, state, memory, hjup, hretained, _⟩ := heach i
      let prefixRun := ReferenceActivePhysicalHorizon.run seed x.val.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s k.val
        (by omega) hactive
      have hprefixLength : prefixRun.records.length = k.val :=
        ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
      have hprefix : prefixRun.records.IsPrefix E.records := by
        obtain ⟨suffix, heq⟩ := run_records_prefix seed x.val.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s k.val
          (p.T - s - k.val) (by omega) hactive
        exact ⟨suffix, by simpa only [Nat.add_sub_of_le (Nat.le_of_lt k.isLt)] using heq.symm⟩
      have hretainedFull : RetainedDown (E.records[j.val]'(by omega)) i prior := by
        rw [← hprefix.getElem j.isLt]
        exact hretained
      have hjn : j.val < n.val := lt_of_lt_of_le (lt_trans hjup hup) hkn
      exact False.elim (hnoDown ⟨j.val, by omega⟩ hjn prior hretainedFull)

-- These local transition facts keep rejected tails and dagger successors.
private theorem input_coordinator_first_of_prepared_first
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (outcome : CoordinatorRoundDispatch.FirstOutcome
      (ReferenceActivePhysicalStep.firstInput x))
    (hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator = .first outcome) :
    x.state.coordinator = .first := by
  have hdispatch : ReferenceActivePhysicalStep.dispatch x = .first outcome := by
    calc
      ReferenceActivePhysicalStep.dispatch x =
          (ReferenceActivePhysicalStep.prepare x).coordinator :=
        (ReferenceActivePhysicalStep.prepare x).coordinator_eq.symm
      _ = .first outcome := hprepared
  cases hstate : x.state.coordinator with
  | first => rfl
  | live registers owned base =>
      cases hrun : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput x registers owned base)) with
      | live actual =>
          have hcut : ReferenceActivePhysicalStep.dispatch x =
              .live registers owned base actual := by
            simp [ReferenceActivePhysicalStep.dispatch, hstate, hrun]
            rfl
          rw [hcut] at hdispatch
          cases hdispatch
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        cases hrun : CoordinatorRoundDispatch.dispatch
            (.collection (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) with
        | collection actual =>
            have hcut : ReferenceActivePhysicalStep.dispatch x =
                .collection payload ledger clock cutoff actual := by
              simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid, cutoff, clock, hrun]
              rfl
            rw [hcut] at hdispatch
            cases hdispatch
      · have hcut : ReferenceActivePhysicalStep.dispatch x = .invalidCollectionCutoff := by
          simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid]
        rw [hcut] at hdispatch
        cases hdispatch
  | dagger =>
      have hcut : ReferenceActivePhysicalStep.dispatch x = .dagger := by
        simp [ReferenceActivePhysicalStep.dispatch, hstate]
      rw [hcut] at hdispatch
      cases hdispatch

private theorem livePostChoice_configuration_ne_first
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration ≠
      .first := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared registers started) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
      | error reason => simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate registers.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none => simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason => simp [hservice, hfinish,
                  ReferenceActivePhysicalStep.coordinatorFailure]
              | ok finished => simp [hservice, hfinish]


private theorem collectionPostChoice_configuration_ne_first
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    (ReferenceActivePhysicalStep.collectionPostChoice
      prepared payload ledger started weights).configuration ≠ .first := by
  rcases collectionPostChoice_no_installation prepared payload ledger started weights with
    hd | ⟨nextPayload, nextLedger, proposal, hc⟩
  · rw [hd]; exact fun h => by cases h
  · rw [hc]; exact fun h => by cases h

private theorem step_coordinator_ne_first
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (ReferenceActivePhysicalStep.step x).next.coordinator ≠ .first := by
  rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | dagger =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.DispatchCut.selection, hcoord]
  | first outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_first_equation
        (ReferenceActivePhysicalStep.prepare x) outcome hcoord
      by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.first outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | chosen installed choice =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
              installed.followerBaseScore installed.startRoundResult
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | live registers owned base outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_live_equation
        (ReferenceActivePhysicalStep.prepare x) registers owned base outcome hcoord
      by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.live registers owned base outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | continuingChosen dispatched startRound continuation choice =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x)
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
              (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base dispatched.startResult
        | cutoffChosen dispatched startRound ledger initialization ledgerCandidate domain clock pending noAssignment choice =>
            exact collectionPostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) registers.payload
              (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | collection payload ledger clock cutoff outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
        (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff outcome hcoord
      by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | continuing core prepared boundary currentScores =>
            exact collectionPostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) payload ledger prepared.clockStarted
              (CoordinatorCollectionInteractive.PreObservationInputs.weights
                (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                prepared.inputsValid.ledger_valid prepared.inputsValid.assignment_eq)
        | laterChosen core consistent started startRound instruction assignmentStart output consistency clockData installed choice =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
              installed.retainedBaseScore started
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | invalidCollectionCutoff =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.DispatchCut.selection, hcoord,
        ReferenceActivePhysicalStep.coordinatorFailure]

private theorem run_final_coordinator_first_only
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode).finalState.coordinator = .first) :
    count = 0 := by
  cases count with
  | zero => rfl
  | succ count =>
      have hlast := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
        initial rows selected rewards start count (by omega) hmode
      have hne : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
          (count + 1) (by omega) hmode).finalState.coordinator ≠ .first := by
        rw [hlast]
        have hstep := step_coordinator_ne_first
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected rewards
            start count (by omega) hmode).input
        simpa [ReferenceAssignmentPayloadChronology.actualRunRecordAt] using hstep
      exact False.elim (hne hfirst)


private theorem installation_sigma_of_no_later
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (endpoint : ℕ)
    (hno : ∀ record ∈ (run initial rows J rewards start count hspan active).records,
      record.input.time.val ≤ endpoint → laterChosen record.input = false)
    (payload : Payload rate) (birth : Record (p := p) (rate := rate))
    (hmem : birth ∈ (run initial rows J rewards start count hspan active).records)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth birth payload)
    (htime : birth.input.time.val ≤ endpoint) : payload.sigma.val = start := by
  have hbirthTime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq birth payload hbirth
  have hnoBirth := hno birth hmem htime
  have hactual : birth.output.preparation.coordinator = (prepare birth.input).coordinator := by
    rw [birth.output_eq]
    rfl
  cases hc : birth.output.preparation.coordinator with
  | first outcome =>
    have hinput := input_coordinator_first_of_prepared_first birth.input outcome
      (hactual.symm.trans hc)
    obtain ⟨k, hk, htimeAt, hstate⟩ :=
      ReferenceSelectedPayloadChronology.actualRunRecord_has_prefix
        initial rows J rewards start count hspan active birth hmem
    have hzero := run_final_coordinator_first_only initial rows J rewards start k
      (by omega) active (hstate.symm ▸ hinput)
    rw [hzero, Nat.add_zero] at htimeAt
    exact hbirthTime.trans htimeAt
  | collection payload ledger clock cutoff outcome =>
    cases outcome <;>
      simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hc] at hbirth
    have hfalse : laterChosen birth.input = true := by
      simp only [laterChosen, ← hactual, hc]
    rw [hfalse] at hnoBirth
    cases hnoBirth
  | live registers owned base outcome =>
    cases outcome <;>
      simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hc] at hbirth
  | dagger => simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hc] at hbirth
  | invalidCollectionCutoff =>
    simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hc] at hbirth

private theorem selected_sigma_of_no_later
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (endpoint : ℕ)
    (hno : ∀ record ∈ (run initial rows J rewards start count hspan active).records,
      record.input.time.val ≤ endpoint → laterChosen record.input = false)
    (record : Record (p := p) (rate := rate))
    (selected : Selection record.input)
    (hrecord : record ∈ (run initial rows J rewards start count hspan active).records)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (htime : record.input.time.val ≤ endpoint) :
    selected.view.payload.sigma.val = start := by
  obtain ⟨birth, hmem, hbirth, hbirthTime, hbefore⟩ :=
    ReferenceSelectedPayloadChronology.actualRun_selectedPayload_has_birth
      initial rows J rewards start count hspan active hfirst record selected hrecord hselected
  exact installation_sigma_of_no_later initial rows J rewards start count hspan active
    endpoint hno selected.view.payload birth hmem hbirth
    (hbirthTime.trans_le (hbefore.trans htime))

private theorem dispatch_origin (x : RoundInput p rate) :
    match (prepare x).coordinator with
    | .first _ => x.state.coordinator = .first
    | .live registers owned base _ => x.state.coordinator = .live registers owned base
    | .collection payload ledger _ _ _ =>
        ∃ proposal, x.state.coordinator = .collection payload ledger proposal
    | .invalidCollectionCutoff => True
    | .dagger => x.state.coordinator = .dagger := by
  change match dispatch x with
    | .first _ => _
    | .live registers owned base _ => _
    | .collection payload ledger _ _ _ => _
    | .invalidCollectionCutoff => _
    | .dagger => _
  cases hc : x.state.coordinator with
  | first => rw [dispatch_first x hc]
  | live registers owned base =>
    have he : dispatch x = .live registers owned base
        (CoordinatorRoundDispatch.dispatchLive (liveInput x registers owned base)) := by
      simp only [dispatch, hc, CoordinatorRoundDispatch.dispatch]
      rfl
    rw [he]
  | dagger => rw [dispatch_dagger x hc]
  | collection payload ledger proposal =>
    by_cases hv : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := collectionClock payload ledger proposal cutoff
      have he : dispatch x = .collection payload ledger clock cutoff
          (CoordinatorRoundDispatch.dispatchCollection
            (collectionInput x payload ledger clock cutoff)) := by
        simp only [dispatch, hc, hv, CoordinatorRoundDispatch.dispatch]
        rfl
      rw [he]
      exact ⟨proposal, rfl⟩
    · rw [(dispatch_collection_invalid_cutoff x payload ledger proposal hc hv).1]
      trivial

private theorem step_collection_phase
    (x : RoundInput p rate) (hphase : CollectionPhase x.state.coordinator)
    (hno : laterChosen x = false) : CollectionPhase (step x).next.coordinator := by
  rcases hphase with hd | ⟨payload, ledger, proposal, hc⟩
  · exact Or.inl (step_coordinator_dagger x hd).1
  · have ho := dispatch_origin x
    change CollectionPhase (prepare x).observeCoordinator.configuration
    unfold PreparedRound.observeCoordinator
    split
    · split <;> exact Or.inl rfl
    · cases he : (prepare x).coordinator with
      | first outcome => rw [he] at ho; rw [hc] at ho; cases ho
      | live r q base outcome => rw [he] at ho; rw [hc] at ho; cases ho
      | collection cp cl clock cutoff outcome =>
        cases outcome with
        | continuing core snapshot boundary scores =>
          exact collectionPostChoice_no_installation (prepare x) cp cl snapshot.clockStarted
            (CoordinatorCollectionInteractive.PreObservationInputs.weights
              (collectionInput x cp cl clock cutoff)
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
        | laterChosen core consistent started hstart instruction hi output hcons data installed selected =>
          simp only [laterChosen, he, Bool.true_eq_false] at hno
        | _ => exact Or.inl rfl
      | invalidCollectionCutoff => exact Or.inl rfl
      | dagger => exact Or.inl rfl

private theorem cutoff_step_collection_phase (x : RoundInput p rate)
    (hcut : cutoffChosen x = true) : CollectionPhase (step x).next.coordinator := by
  change CollectionPhase (prepare x).observeCoordinator.configuration
  cases he : (prepare x).coordinator with
  | live registers owned base outcome =>
    cases outcome <;> simp only [cutoffChosen, he, Bool.false_eq_true] at hcut
    rename_i dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected
    rw [observeCoordinator_live_equation (prepare x) _ _ _ _ he]
    split
    · exact Or.inl rfl
    · exact collectionPostChoice_no_installation (prepare x) registers.payload
        (sharedLedger ledger) dispatched.startResult
        (liveRegistersAt registers x.time).complementWeights
  | first outcome => simp only [cutoffChosen, he, Bool.false_eq_true] at hcut
  | collection payload ledger clock cutoff outcome =>
    cases outcome <;> simp only [cutoffChosen, he, Bool.false_eq_true] at hcut
  | invalidCollectionCutoff => simp only [cutoffChosen, he, Bool.false_eq_true] at hcut
  | dagger => simp only [cutoffChosen, he, Bool.false_eq_true] at hcut

private theorem connected_collection_phase
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (Record (p := p) (rate := rate))}
    (chain : Connected initial records final)
    (hphase : CollectionPhase initial.coordinator)
    (hno : ∀ r ∈ records, laterChosen r.input = false) :
    CollectionPhase final.coordinator := by
  induction records generalizing initial with
  | nil => subst final; exact hphase
  | cons r rest ih =>
    obtain ⟨hpre, hrest⟩ := chain
    apply ih hrest
    · rw [r.output_eq]
      exact step_collection_phase r.input (hpre ▸ hphase) (hno r List.mem_cons_self)
    · exact fun record hr => hno record (List.mem_cons_of_mem r hr)

private theorem connected_cutoff_phase
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (Record (p := p) (rate := rate))}
    (chain : Connected initial records final)
    (hcut : ∃ r ∈ records, cutoffChosen r.input = true)
    (hno : ∀ r ∈ records, laterChosen r.input = false) :
    CollectionPhase final.coordinator := by
  induction records generalizing initial with
  | nil => obtain ⟨r, hr, _⟩ := hcut; cases hr
  | cons r rest ih =>
    obtain ⟨hpre, hrest⟩ := chain
    obtain ⟨cut, hmem, hcut⟩ := hcut
    rcases List.mem_cons.mp hmem with heq | hmem
    · subst cut
      apply connected_collection_phase hrest
      · rw [r.output_eq]
        exact cutoff_step_collection_phase r.input hcut
      · exact fun record hr => hno record (List.mem_cons_of_mem r hr)
    · exact ih hrest ⟨cut, hmem, hcut⟩
        (fun record hr => hno record (List.mem_cons_of_mem r hr))

private theorem firstLiveWindow_endpoint
    (records : List (Record (p := p) (rate := rate)))
    (hlt : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length < records.length) :
    cutoffChosen (records[(ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length]).input =
      true := by
  induction records with
  | nil => simp only [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, List.takeWhile_nil,
      List.length_nil, Nat.lt_irrefl] at hlt
  | cons r rest ih =>
    cases hc : cutoffChosen r.input with
    | true => simp only [ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
        List.takeWhile_cons, hc, Bool.not_true, Bool.false_eq_true, ite_false,
        List.length_nil, List.getElem_cons_zero]
    | false =>
      simp only [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, List.takeWhile_cons,
        hc, Bool.not_false, ite_true, List.length_cons, Nat.add_lt_add_iff_right] at hlt ⊢
      exact ih hlt

private theorem collection_selected_pending
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (active : allActiveAtStart initial start) (hfirst : initial.coordinator = .first)
    (i : Fin (p.m - 1))
    (hnoUp : ∀ record ∈ (run initial rows J rewards start count (by omega) active).records,
      ∀ message, ¬ AcceptedUp record.input i message)
    (hnoLater : laterChosen (nextInput initial rows J rewards start count hspan active) = false)
    (hphase : cutoffChosen (nextInput initial rows J rewards start count hspan active) = true ∨
      CollectionPhase (nextInput initial rows J rewards start count hspan active).state.coordinator)
    (selected : Selection (nextInput initial rows J rewards start count hspan active))
    (hselected : (prepare (nextInput initial rows J rewards start count hspan active)).coordinator.selection =
      some selected) : i ∈ selected.view.pendingAtChoice := by
  let x := nextInput initial rows J rewards start count hspan active
  change laterChosen x = false at hnoLater
  change cutoffChosen x = true ∨ CollectionPhase x.state.coordinator at hphase
  have ho := dispatch_origin x
  have hselected' : (prepare x).coordinator.selection = some selected := hselected
  cases he : (prepare x).coordinator with
  | first outcome =>
    rcases hphase with hcut | hphase
    · simp only [cutoffChosen, he, Bool.false_eq_true] at hcut
    · rw [he] at ho
      rcases hphase with hd | ⟨payload, ledger, proposal, hc⟩
      · exact False.elim (by rw [ho] at hd; cases hd)
      · exact False.elim (by rw [ho] at hc; cases hc)
  | live registers owned base outcome =>
    have hcut : cutoffChosen x = true := by
      rcases hphase with hcut | hphase
      · exact hcut
      · rw [he] at ho
        rcases hphase with hd | ⟨payload, ledger, proposal, hc⟩
        · rw [ho] at hd; cases hd
        · rw [ho] at hc; cases hc
    cases outcome <;> simp only [cutoffChosen, he, Bool.false_eq_true] at hcut
    rename_i dispatched hstart ledger hinit hledger hvalid hclock hpending hnone choice
    have hfields := congrArg (Option.map (fun value : Selection x => value.view.pendingAtChoice))
      hselected'
    simp only [he, DispatchCut.selection, selectionAt, dite_true, Option.map_some] at hfields
    have hp : selected.view.pendingAtChoice = Finset.univ :=
      (Option.some.inj hfields).symm.trans hpending
    exact hp.symm ▸ Finset.mem_univ i
  | collection payload ledger clock cutoff outcome =>
    cases outcome with
    | continuing core snapshot boundary scores =>
      rw [he] at ho
      obtain ⟨proposal, hinput⟩ := ho
      have hfinal : (run initial rows J rewards start count (by omega) active).finalState.coordinator =
          .collection payload ledger proposal := hinput
      obtain ⟨before, cut, during, hrecords, _hbefore, _hcut, _hwindow,
          hpending, _hnodup, hwitness⟩ := run_collection_pending_exact initial rows J rewards
        start count (by omega) active hfirst payload ledger proposal hfinal
      have hi : i ∈ ledger.pending := by
        rw [hpending]
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, ?_⟩
        intro hmem
        have hlist : i ∈ acceptedLabels (cut :: during) := List.mem_toFinset.mp hmem
        obtain ⟨record, hrecord, hlabel⟩ := List.mem_filterMap.mp hlist
        obtain ⟨message, haccepted, _⟩ := hwitness record hrecord i hlabel
        apply hnoUp record _ message haccepted
        rw [hrecords]
        exact List.mem_append_right before hrecord
      have hfields := congrArg (Option.map (fun value : Selection x => value.view.pendingAtChoice))
        hselected'
      simp only [he, DispatchCut.selection, Option.map_some] at hfields
      have hp : selected.view.pendingAtChoice = ledger.pending :=
        (Option.some.inj hfields).symm.trans snapshot.clockStarted_frame.2.1
      exact hp.symm ▸ hi
    | laterChosen core consistent started hstart instruction hi output hcons data installed choice =>
      simp only [laterChosen, he, Bool.true_eq_false] at hnoLater
    | _ => simp [he, DispatchCut.selection] at hselected'
  | dagger => simp [he, DispatchCut.selection] at hselected'
  | invalidCollectionCutoff =>
    simp [he, DispatchCut.selection] at hselected'

private theorem referenceDownCut_expectedWord
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (logged : ReferencePrelaunchFollower.State p rate.eta) :
    (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).expectedWord =
      ReferenceDownReception.expectedDownFlatWord view i row time := by
  classical
  unfold ReferenceDownReception.referenceDownCut
  split
  · split
    · split
      · split
        · split
          · dsimp only
            split <;> rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

private theorem wrong_cut_excluded_of_selected_word
    (Rn : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (current : Selection Rn.input)
    (hcurrentSelection : Rn.output.preparation.coordinator.selection = some current)
    (hcut : (Rn.output.followers i).down = some cut)
    (hwrongCut : ReferenceDownReception.wrongUniqueAccepted cut)
    (hraw : cut.raw = some word)
    (hpending : i ∈ current.view.pendingAtChoice)
    (hwordCurrent : word = CoordinatorLocalArmChoice.storedDownFlatWord current.view.payload i) :
    False := by
  classical
  obtain ⟨choiceState, memory, logged, _, _, _, hlogged, _⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice
      Rn i cut hcut
  have hcutActual :=
    ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
      Rn i logged cut hlogged hcut
  have hfalseActual := hwrongCut.1
  rw [hcutActual] at hfalseActual
  have hcompared :
      (ReferenceDownReception.referenceDownCut p
        Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
        rate logged).rawComparison ≠ none := by
    rw [hfalseActual]
    simp
  have hcomparisonSome :
      (ReferenceDownReception.referenceDownCut p
        Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
        rate logged).rawComparison.isSome = true := by
    rw [hfalseActual]
    rfl
  have hgate :
      ReferenceActiveAffinePositiveTest.downReceiverGate i Rn.input.row
        Rn.input.time logged := by
    have hcall := ReferenceActiveAffinePositiveTest.referenceDownCut_has_call
      Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i) logged
    rw [hcall] at hcomparisonSome
    exact of_decide_eq_true hcomparisonSome
  have hrawDecode :=
    ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
      Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
      (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
      rate logged hcompared
  have hrawActual := hraw
  rw [hcutActual] at hrawActual
  have hdecoded :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i Rn.input.row Rn.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
        rate logged).2 = some word := hrawDecode.symm.trans hrawActual
  have hview : Rn.output.preparation.coordinator.downView = some current.view := by
    simp only [ReferenceActivePhysicalStep.DispatchCut.downView,
      hcurrentSelection, Option.map_some]
  have hcutExpected :
      cut.expectedWord =
        ReferenceDownReception.expectedDownFlatWord
          Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time := by
    calc
      cut.expectedWord =
          (ReferenceDownReception.referenceDownCut p
            Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
            (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
            rate logged).expectedWord :=
        congrArg ReferenceDownReception.ReferenceDownCutOutput.expectedWord hcutActual
      _ = ReferenceDownReception.expectedDownFlatWord
          Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time :=
        referenceDownCut_expectedWord _ _ _ _ _ _
  have hsenderCurrent :
      ReferenceDownReception.selectedDownSenderBranch current.view i
        Rn.input.row Rn.input.time := by
    exact ⟨hgate.1.1, hgate.1.2, hpending⟩
  have hselectedExpected :=
    ReferenceActivePhysicalStep.Selection.expected_down_word current i hsenderCurrent
  have hselectedExpected' :
      ReferenceDownReception.expectedDownFlatWord
          (some current.view) i Rn.input.row Rn.input.time =
        some (CoordinatorLocalArmChoice.storedDownFlatWord current.view.payload i) := by
    simpa only [ReferenceActivePhysicalStep.RoundInput.row]
      using hselectedExpected
  have hcutExpectedCurrent : cut.expectedWord =
      ReferenceDownReception.expectedDownFlatWord
        (some current.view) i Rn.input.row Rn.input.time := by
    rw [hview] at hcutExpected
    exact hcutExpected
  have hactualExpected : cut.expectedWord = some word := by
    rw [hcutExpectedCurrent, hselectedExpected']
    exact congrArg some hwordCurrent.symm
  have hdecodedMatchesExpected :
      (ActiveFollowerDownAcceptance.currentDecodeStep p i Rn.input.row Rn.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
        rate logged).2 =
        ReferenceDownReception.expectedDownFlatWord
          Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time := by
    calc
      _ = some word := hdecoded
      _ = cut.expectedWord := hactualExpected.symm
      _ = ReferenceDownReception.expectedDownFlatWord
          Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time :=
        hcutExpected
  have hcomparisonTrue :
      (ReferenceDownReception.referenceDownCut p
        Rn.output.preparation.coordinator.downView i Rn.input.row Rn.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation Rn i)
        rate logged).rawComparison = some true := by
    simp [ReferenceDownReception.referenceDownCut, hgate.1, hgate.2.1,
      hgate.2.2.1, hgate.2.2.2.1, hgate.2.2.2.2,
      hdecodedMatchesExpected]
  rw [hcomparisonTrue] at hfalseActual
  cases hfalseActual

/-- The inherited first-completion cut after eliminating the selected postcut
case. The same cohort, birth, raw diagnostic and detector witnesses are
retained; current no-selection remains an explicit physical residual. -/
theorem generated_inherited_postcut_wrong_completion_cut
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (control0 : ContinuousLearningRows.TimeControl p)
    (hfirst :
      ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
          ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
            rate rewards C_star C_h s hs i x).2 n) ∧
        ∀ l (hl : l < n.val),
          ¬ ReferenceGeneratedDownBatchCalendar.completedBatchAtRound rate
            ((ReferenceGeneratedDownBatchCalendar.generatedSourceObservation
              rate rewards C_star C_h s hs i x).2 ⟨l, lt_trans hl n.isLt⟩))
    (hwrong : ∃ cut,
      ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n).output.followers i).down = some cut ∧
        ReferenceDownReception.wrongUniqueAccepted cut) :
    let B0 := (ReferenceGeneratedInheritedDownCompletion.generatedInheritedInitialFollower
      rate rewards C_star C_h s hs x i).downBatch
    let E := ReferenceGeneratedDownBatchCalendar.generatedSourceRun
      rate rewards C_star C_h s hs x
    let F := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    let Rn := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x n
    ∃ cut word alpha, ∃ hAlpha : alpha ≤ p.T,
      (Rn.output.followers i).down = some cut ∧
      ReferenceDownReception.wrongUniqueAccepted cut ∧
      cut.raw = some word ∧ alpha ≤ s ∧
      ReferenceGeneratedPrelaunchDownPrefix.birthAt rate rewards C_star C_h
        x.val i alpha hAlpha B0.completed.length ∧
      ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
        rate rewards C_star C_h x.val i B0.completed.length = some alpha ∧
      (∀ test ∈ ReferenceGeneratedInheritedDownCohort.generatedInheritedDownFirstCohortTests
          rate rewards C_star C_h s hs i x,
        AffineChannelLaw.affineHash test.sample word = 1) ∧
      Rn ∈ (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate x.val rewards C_star C_h).take (p.T - s) ∧
      (x.val ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha B0.completed.length hAlpha word control0
          (AffineBatchDecoder.quota p) ∨
        Rn.output.preparation.coordinator.selection = none) := by
  classical
  intro B0 E F Rn
  let seed := generatedSourceSeed rate rewards C_star C_h s hs x
  obtain ⟨hactive, hinitial, _hfollowers, _hseed⟩ :=
    generatedSeed_initial_state rate rewards C_star C_h s hs x
  have hgen : generatedSourceRun rate rewards C_star C_h s hs x = E := rfl
  have hrun : E = run seed x.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s
      (p.T - s) (by omega) hactive := rfl
  by_cases hwindow : n.val < F.length
  · obtain ⟨cut, word, alpha, hAlpha, hcut, hwrongCut, hraw, hAlphaS,
        hbirth, hboundary, hhash, hcurrentSuffix, hcase⟩ :=
      ReferenceGeneratedInheritedDownFirstLiveCut.generated_inherited_firstLive_wrong_completion_cut
        rate rewards C_star C_h s hs x i n control0 hfirst hwrong
    refine ⟨cut, word, alpha, hAlpha, hcut, hwrongCut, hraw, hAlphaS,
      hbirth, hboundary, hhash, hcurrentSuffix, ?_⟩
    rcases hcase with hdetector | hpostcut | hnone
    · exact Or.inl hdetector
    · exact False.elim ((Nat.not_le_of_gt hwindow) hpostcut)
    · exact Or.inr hnone
  obtain ⟨cut, word, alpha, hAlpha, hcut, hwrongCut, hraw, hAlphaS,
      hbirth, hboundary, hhash, hcurrentSuffix, hobstruction⟩ :=
    ReferenceGeneratedInheritedDownCandidateOrigin.generated_inherited_down_candidate_origin
      rate rewards C_star C_h s hs x i n control0 hfirst hwrong
  refine ⟨cut, word, alpha, hAlpha, hcut, hwrongCut, hraw, hAlphaS,
    hbirth, hboundary, hhash, hcurrentSuffix, ?_⟩
  rcases hobstruction with hdetector | hearlier
  · exact Or.inl hdetector
  rcases hearlier with ⟨earlier, _hearlierPrefix, _hearlierSent, offset,
    record, hrecordRun, _hrecordSuffix, hrecordTime, htimeOrder, _hearlierTime,
    _hexecuted, call, cutEarlier, _hcall, _hcutEarlier, _hearlierSample,
    _hexpectedEarlier, selected, hselectedEarlier, _hsenderEarlier,
    message, _hmessage, hwordMessage, _hencode, _hparseMessage, _hcurrentParse,
    _hsigmaMessage, birthRecord, hbirthRecord, hinstallation, hbirthTime,
    hbirthBefore⟩
  cases hcurrent : Rn.output.preparation.coordinator.selection with
  | none => exact Or.inr rfl
  | some current =>
    have hhistory := generated_inherited_first_completion_no_up_or_later
      rate rewards C_star C_h s hs x i n hfirst
    have hlength : E.records.length = p.T - s := run_record_count _ _ _ _ _ _ _ _
    have hrecord (k : Fin (p.T - s)) :
        E.records[k.val]'(by omega) =
          generatedSourceRecordAt rate rewards C_star C_h s hs x k := by
      have hget := generatedSourceRecordAt_getElem? rate rewards C_star C_h s hs x k
      rw [hgen, List.getElem?_eq_getElem (by omega)] at hget
      exact Option.some.inj hget
    have htimes : E.records.map (fun r => r.input.time.val) = calendar s (p.T - s) :=
      run_time_values _ _ _ _ _ _ _ _
    have htimeAt (j : ℕ) (hj : j < E.records.length) :
        (E.records[j]'hj).input.time.val = s + j := by
      have hjRange : j < p.T - s := by omega
      have hget := congrArg (fun values : List ℕ => values[j]?) htimes
      simpa only [List.getElem?_map, List.getElem?_eq_getElem hj,
        calendar, List.getElem?_range', hjRange, Option.map_some,
        Nat.one_mul, Option.some.injEq] using hget
    have hnoLater : ∀ r ∈ E.records, r.input.time.val ≤ s + n.val →
        laterChosen r.input = false := by
      intro r hr htime
      obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hr
      have hjTime := htimeAt j hj
      rw [heq] at hjTime
      have hjn : j ≤ n.val := by omega
      have heqGenerated : r = generatedSourceRecordAt rate rewards C_star C_h s hs x
          ⟨j, by omega⟩ := heq.symm.trans (hrecord ⟨j, by omega⟩)
      rw [heqGenerated]
      exact hhistory.2 ⟨j, by omega⟩ hjn
    let prefixRun := run seed x.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s n.val
      (by omega) hactive
    have hprefixLength : prefixRun.records.length = n.val := run_record_count _ _ _ _ _ _ _ _
    have hprefix : prefixRun.records.IsPrefix E.records := by
      rw [hrun]
      obtain ⟨suffix, heq⟩ := run_records_prefix seed x.val.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s n.val
        (p.T - s - n.val) (by omega) hactive
      exact ⟨suffix, by simpa only [Nat.add_sub_of_le (Nat.le_of_lt n.isLt)] using heq.symm⟩
    have hprefixFacts (r : Record (p := p) (rate := rate)) (hr : r ∈ prefixRun.records) :
        (∀ msg, ¬ AcceptedUp r.input i msg) ∧ laterChosen r.input = false := by
      obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hr
      have hjn : j < n.val := by rw [hprefixLength] at hj; exact hj
      have heqGenerated : r = generatedSourceRecordAt rate rewards C_star C_h s hs x
          ⟨j, by omega⟩ := heq.symm.trans ((hprefix.getElem hj).trans (hrecord ⟨j, by omega⟩))
      rw [heqGenerated]
      exact ⟨hhistory.1 ⟨j, by omega⟩ (Nat.le_of_lt hjn),
        hhistory.2 ⟨j, by omega⟩ (Nat.le_of_lt hjn)⟩
    have hFlt : F.length < E.records.length := by omega
    have hcutoff := firstLiveWindow_endpoint E.records hFlt
    change cutoffChosen (E.records[F.length]'hFlt).input = true at hcutoff
    have hphase : cutoffChosen Rn.input = true ∨ CollectionPhase Rn.input.state.coordinator := by
      by_cases heq : F.length = n.val
      · apply Or.inl
        have hcutoff' : cutoffChosen (E.records[n.val]'(by omega)).input = true := by
          simpa only [heq] using hcutoff
        rw [hrecord n] at hcutoff'
        exact hcutoff'
      · have hcutIndex : F.length < prefixRun.records.length := by omega
        have hcutPrefix : cutoffChosen (prefixRun.records[F.length]'hcutIndex).input = true := by
          rw [hprefix.getElem hcutIndex]
          exact hcutoff
        have hp := connected_cutoff_phase prefixRun.connected
          ⟨prefixRun.records[F.length], List.getElem_mem hcutIndex, hcutPrefix⟩
          (fun r hr => (hprefixFacts r hr).2)
        exact Or.inr hp
    have hcurrentPrepared : (prepare Rn.input).coordinator.selection = some current := by
      have heq := hcurrent
      rw [Rn.output_eq] at heq
      exact heq
    have hpending := collection_selected_pending seed x.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s n.val
      (by omega) hactive hinitial i (fun r hr => (hprefixFacts r hr).1)
      (hhistory.2 n le_rfl) hphase current hcurrentPrepared
    have hcurrentRun : Rn ∈ E.records := by
      change generatedSourceRecordAt rate rewards C_star C_h s hs x n ∈ E.records
      rw [← hrecord n]
      exact List.getElem_mem (by omega)
    have hcurrentTime : Rn.input.time.val = s + n.val := rfl
    rw [hgen] at hrecordRun
    have hsigmaCurrent := selected_sigma_of_no_later seed x.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s (p.T - s)
      (by omega) hactive hinitial (s + n.val) hnoLater Rn current hcurrentRun hcurrent
      (by rw [hcurrentTime])
    rw [hgen] at hbirthRecord
    have hsigmaEarlier := installation_sigma_of_no_later seed x.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s (p.T - s)
      (by omega) hactive (s + n.val) hnoLater selected.view.payload birthRecord
      hbirthRecord hinstallation (by omega)
    have hpayloadEq :=
      ReferenceSelectedPayloadChronology.run_two_actualSelectedPayloads_eq_of_equal_sigma
        seed x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s
        (p.T - s) (by omega) hactive hinitial Rn record current selected hcurrentRun
        hrecordRun hcurrent hselectedEarlier (hsigmaCurrent.trans hsigmaEarlier.symm)
    have hwordCurrent : word = CoordinatorLocalArmChoice.storedDownFlatWord current.view.payload i :=
      hwordMessage.trans
        (congrArg (fun payload => CoordinatorLocalArmChoice.storedDownFlatWord payload i) hpayloadEq).symm
    exact False.elim (wrong_cut_excluded_of_selected_word Rn i cut word current
      hcurrent hcut hwrongCut hraw hpending hwordCurrent)

end Bandits.Support.ReferenceGeneratedInheritedDownPostcutExclusion

end
