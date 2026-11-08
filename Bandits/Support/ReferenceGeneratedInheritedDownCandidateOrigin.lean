/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedInheritedDownWrongCompletionWitness
public import Bandits.Support.ReferenceSelectedPayloadChronology

/-!
# Selected origin of an inherited sent DOWN candidate

This module turns the actual earlier sent-word branch of the inherited first
wrong-completion witness into its selected sender, complete encoded DOWN
record, parser identities, and same-run assignment birth. The inputs remain
the original generated source, whole reward table, accepted rate, unrestricted
constants, and actual physical diagnostics.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-106`,
`sources/zip4/manuscript/05_binary_transport.tex:96-106`,
`sources/zip4/manuscript/06_interruptions.tex:270-275,327-344`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-33`.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceDownReception
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.ReferenceGeneratedDownBatchCalendar
open Bandits.Support.ReferenceGeneratedInheritedDownWrongCompletionWitness
open Bandits.Support.ReferenceSelectedPayloadChronology
open Bandits.Support.ReferenceAssignmentPayloadPersistence

namespace Bandits.Support.ReferenceGeneratedInheritedDownCandidateOrigin

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem finishFollower_diagnostic_pair
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p) :
    ((ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput,
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).down) =
    match prepared.configuration with
    | .dagger => (none, none)
    | .ordinary state _ =>
        let recorded := ReferenceActivePhysicalStep.recordFollower view prepared.follower
          prepared.row prepared.activation prepared.time prepared.active prepared.arm observation state
        (recorded.downInput, recorded.down) := by
  cases hconfiguration : prepared.configuration with
  | dagger => simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration]
  | ordinary state memory =>
      simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration]
      cases hrecord : (ReferenceActivePhysicalStep.recordFollower view prepared.follower
        prepared.row prepared.activation prepared.time prepared.active prepared.arm observation state).result with
      | error failure => rfl
      | ok postRecord =>
          dsimp only
          cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
              prepared.row prepared.time observation state memory postRecord with
          | error failure => rfl
          | ok next => cases next; rfl

private theorem retained_cut_has_logged_input
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : (record.output.followers i).down = some cut) :
    ∃ logged,
      (record.output.followers i).downInput = some logged ∧
      cut = ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView i record.input.row record.input.time
        (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) rate logged := by
  let prepared := ReferenceActivePhysicalStep.prepare record.input
  have hfollowers : record.output.followers i = prepared.observeFollower i := by
    rw [record.output_eq]
    rfl
  have hdiagnostics := finishFollower_diagnostic_pair prepared.coordinator.downView
    (prepared.followers.followers i)
    (prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))
  have hcut' : (prepared.observeFollower i).down = some cut := by
    rw [← hfollowers]
    exact hcut
  change ((prepared.observeFollower i).downInput, (prepared.observeFollower i).down) = _ at hdiagnostics
  cases hconfiguration : (prepared.followers.followers i).configuration with
  | dagger =>
      simp only [hconfiguration] at hdiagnostics
      have hsecond := congrArg Prod.snd hdiagnostics
      rw [hcut'] at hsecond
      cases hsecond
  | ordinary state memory =>
      let recorded := ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
        (prepared.followers.followers i).follower (prepared.followers.followers i).row
        (prepared.followers.followers i).activation (prepared.followers.followers i).time
        (prepared.followers.followers i).active (prepared.followers.followers i).arm
        (prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state
      have hpair : ((prepared.observeFollower i).downInput, (prepared.observeFollower i).down) =
          (recorded.downInput, recorded.down) := by
        simpa [recorded, hconfiguration] using hdiagnostics
      have hrecordDown : recorded.down = some cut := by
        have hsecond := congrArg Prod.snd hpair
        rw [hcut'] at hsecond
        exact hsecond.symm
      by_cases hstatus : state.status = .unoccupied
      · cases hlogging : ActiveFollowerLogging.checkedLogging
          (prepared.followers.followers i).follower
          (prepared.followers.followers i).row
          (prepared.followers.followers i).activation
          (prepared.followers.followers i).time
          ((prepared.followers.followers i).arm,
            prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state with
        | error failure =>
            simp [recorded, ReferenceActivePhysicalStep.recordFollower, hstatus, hlogging]
              at hrecordDown
        | ok logged =>
            have hdiag := ReferenceActivePhysicalStep.recordFollower_logged
              prepared.coordinator.downView (prepared.followers.followers i).follower
              (prepared.followers.followers i).row
              (prepared.followers.followers i).activation
              (prepared.followers.followers i).time
              (prepared.followers.followers i).active
              (prepared.followers.followers i).arm
              (prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i))
              state logged hstatus hlogging
            have hfirst : (prepared.observeFollower i).downInput = recorded.downInput := by
              exact congrArg Prod.fst hpair
            have hinput : (record.output.followers i).downInput = some logged := by
              calc
                (record.output.followers i).downInput = (prepared.observeFollower i).downInput := by
                  rw [hfollowers]
                _ = recorded.downInput := hfirst
                _ = some logged := hdiag.1
            exact ⟨logged, hinput,
              ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
                record i logged cut hinput hcut⟩
      · simp [recorded, ReferenceActivePhysicalStep.recordFollower, hstatus] at hrecordDown

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
          · dsimp
            split <;> rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

private theorem referenceDownCut_mismatch_parse
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hwrong : ReferenceDownReception.wrongUniqueAccepted
      (ReferenceDownReception.referenceDownCut p view i row time observation rate logged))
    (hraw : (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).raw =
      some word) :
    (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).ordinaryParse =
      ReferenceDownReception.ordinaryParse p rate (some word) := by
  have hfalse : (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).rawComparison =
      some false := hwrong.1
  have hselected : ActiveFollowerDownAcceptance.downSelected p i row time := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, hnot] at hfalse
  have hstatus : logged.status = .unoccupied := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, hselected, hnot] at hfalse
  have hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate logged := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, hselected, hstatus, hnot] at hfalse
  have hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, hselected, hstatus, hregisters, hnot] at hfalse
  have hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer := by
    by_contra hnot
    simp [ReferenceDownReception.referenceDownCut, hselected, hstatus, hregisters, hbatch,
      hnot] at hfalse
  have hmismatch : ReferenceDownReception.rawMismatch
      (ReferenceDownReception.referenceDownCut p view i row time observation rate logged) := hfalse
  obtain ⟨_, hrawEq, _, hparse, _⟩ :=
    ReferenceDownReception.referenceDownCut_raw_mismatch_preserves view i row time observation
      rate logged hselected hstatus hregisters hbatch hbuffer hmismatch
  have hdecoded : (ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate
      logged).2 = some word := hrawEq.symm.trans hraw
  rw [hparse, hdecoded]

private theorem actual_wrongDownCut_parse
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hcut : (record.output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut)
    (hraw : cut.raw = some word) :
    cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate (some word) := by
  obtain ⟨logged, hlogged, hcutEq⟩ := retained_cut_has_logged_input record i cut hcut
  have hwrong' := hwrong
  rw [hcutEq] at hwrong'
  have hraw' := hraw
  rw [hcutEq] at hraw'
  have hparse := referenceDownCut_mismatch_parse
    record.output.preparation.coordinator.downView i record.input.row record.input.time
    (ReferenceFollowerDownDecoderReplay.preparedOwnObservation record i) logged word hwrong' hraw'
  rw [← hcutEq] at hparse
  exact hparse

/-- An actual retained cut whose expected word is present came from the
actual selected DOWN sender. The word and parser result are the complete
assignment record encoded by the retained selection. -/
theorem actual_expectedDownWord_origin
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hcut : (record.output.followers i).down = some cut)
    (hexpected : cut.expectedWord = some word) :
    ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
      ReferenceDownReception.selectedDownSenderBranch selected.view i record.input.row
        record.input.time ∧
      word = CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i ∧
      ReferenceDownReception.ordinaryParse p rate (some word) =
        some (selected.view.payload.downRecord i) ∧
      (OrdinaryMessageCodec.wordEquivFlat
        (ReferencePrelaunchFollower.codecParams p rate.eta))
          (OrdinaryMessageCodec.encodeDown _ (selected.view.payload.downRecord i)) = word := by
  obtain ⟨logged, _, hcutEq⟩ := retained_cut_has_logged_input record i cut hcut
  have hexpected' :
      ReferenceDownReception.expectedDownFlatWord
        record.output.preparation.coordinator.downView i record.input.row record.input.time =
        some word := by
    have h := hexpected
    rw [hcutEq, referenceDownCut_expectedWord] at h
    exact h
  cases hselection : record.output.preparation.coordinator.selection with
  | none =>
      simp [ReferenceActivePhysicalStep.DispatchCut.downView, hselection,
        ReferenceDownReception.expectedDownFlatWord] at hexpected'
  | some selected =>
      have hselection' : record.output.preparation.coordinator.selection = some selected := hselection
      have hexpectedSelected :
          ReferenceDownReception.expectedDownFlatWord (some selected.view) i record.input.row
            record.input.time = some word := by
        simpa [ReferenceActivePhysicalStep.DispatchCut.downView, hselection'] using hexpected'
      have hchoiceBranch :
          CoordinatorLocalArmChoice.coordinatorArmChoice selected.view.payload
              selected.view.pendingAtChoice selected.view.cutoff record.input.time
              selected.view.complementWeights record.input.row ≠ none ∧
            ReferenceDownReception.selectedDownSenderBranch selected.view i
              record.input.row record.input.time := by
        by_cases hcondition :
            CoordinatorLocalArmChoice.coordinatorArmChoice selected.view.payload
                selected.view.pendingAtChoice selected.view.cutoff record.input.time
                selected.view.complementWeights record.input.row ≠ none ∧
              ReferenceDownReception.selectedDownSenderBranch selected.view i
                record.input.row record.input.time
        · exact hcondition
        · have hnone : ReferenceDownReception.expectedDownFlatWord (some selected.view) i
              record.input.row record.input.time = none := by
            simp [ReferenceDownReception.expectedDownFlatWord, hcondition]
          rw [hnone] at hexpectedSelected
          cases hexpectedSelected
      have hbranch := hchoiceBranch.2
      have hselectedWord : ReferenceDownReception.expectedDownFlatWord (some selected.view) i
          record.input.row record.input.time =
            some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) :=
        (ReferenceDownReception.expectedDownFlatWord_eq_some_iff selected.view i
          record.input.row record.input.time).mpr hchoiceBranch
      have hword : word = CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i :=
        Option.some.inj (hexpectedSelected.symm.trans hselectedWord)
      let message := selected.view.payload.downRecord i
      have hparse : ReferenceDownReception.ordinaryParse p rate (some word) = some message := by
        rw [hword]
        unfold ReferenceDownReception.ordinaryParse CoordinatorLocalArmChoice.storedDownFlatWord
        change OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
          (some ((OrdinaryMessageCodec.wordEquivFlat
            (ReferencePrelaunchFollower.codecParams p rate.eta)).symm
              ((OrdinaryMessageCodec.wordEquivFlat
                (ReferencePrelaunchFollower.codecParams p rate.eta))
                  (selected.view.payload.downWord i)))) = _
        rw [Equiv.symm_apply_apply]
        exact selected.view.payload.parseDown_downWord i
      have hencode :
          (OrdinaryMessageCodec.wordEquivFlat
            (ReferencePrelaunchFollower.codecParams p rate.eta))
              (OrdinaryMessageCodec.encodeDown _ message) = word := by
        change (OrdinaryMessageCodec.wordEquivFlat
          (ReferencePrelaunchFollower.codecParams p rate.eta))
            (OrdinaryMessageCodec.encodeDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (selected.view.payload.downRecord i)) = word
        simpa [CoordinatorLocalArmChoice.storedDownFlatWord,
          AssignmentStartPayload.Input.downWord, AffineBatchDecoder.width,
          ReferencePrelaunchFollower.codecParams] using hword.symm
      exact ⟨selected, rfl, hbranch, hword, hparse, hencode⟩

/-- The inherited first-completion obstruction with its earlier-sent branch
resolved to an actual selected sender and a whole same-run DOWN record. Every
original W witness remains present, including the candidate's first-cohort
hash equations and the actual earlier call and physical sample. -/
theorem generated_inherited_down_candidate_origin
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
    ∃ cut word alpha, ∃ hAlpha : alpha ≤ p.T,
      ((ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n).output.followers i).down = some cut ∧
      ReferenceDownReception.wrongUniqueAccepted cut ∧
      cut.raw = some word ∧ alpha ≤ s ∧
      ReferenceGeneratedPrelaunchDownPrefix.birthAt rate rewards C_star C_h
        x.val i alpha hAlpha B0.completed.length ∧
      ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownCohortBoundary
        rate rewards C_star C_h x.val i B0.completed.length = some alpha ∧
      (∀ test ∈ ReferenceGeneratedInheritedDownCohort.generatedInheritedDownFirstCohortTests
          rate rewards C_star C_h s hs i x,
        AffineChannelLaw.affineHash test.sample word = 1) ∧
      ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n ∈
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate x.val rewards C_star C_h).take (p.T - s) ∧
      (x.val ∈ ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha B0.completed.length hAlpha word control0
          (AffineBatchDecoder.quota p) ∨
        ∃ earlier : ReferenceGeneratedDownBatchCalendar.ExecutedTest p,
          earlier ∈ ReferenceGeneratedInheritedDownPrefixMarker.inheritedDownPrefix
            (rate := rate) rewards C_star C_h s hs i x n.val ∧
          earlier.sent = some word ∧
          ∃ offset : Fin (p.T - s),
            ∃ record : ReferenceFollowerDownDecoderReplay.Record p rate,
              record ∈ (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                rate rewards C_star C_h s hs x).records ∧
              record ∈ (ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate x.val rewards C_star C_h).take (p.T - s) ∧
              record.input.time.val = s + offset.val ∧
              s + offset.val < s + n.val ∧
              earlier.time = record.input.time ∧
              ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
                (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation
                  record.input i) = some earlier ∧
              ∃ call cutEarlier,
                ReferenceFollowerDownDecoderReplay.actualDownCall i record = some call ∧
                (record.output.followers i).down = some cutEarlier ∧
                earlier.sample = ((x.val.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p x.val)).2
                  earlier.time).2 (0, i) ∧
                cutEarlier.expectedWord = some word ∧
                ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
                  record.output.preparation.coordinator.selection = some selected ∧
                  ReferenceDownReception.selectedDownSenderBranch selected.view i
                    record.input.row record.input.time ∧
                  ∃ message : OrdinaryMessageCodec.DownRecord
                    (ReferencePrelaunchFollower.codecParams p rate.eta),
                    message = selected.view.payload.downRecord i ∧
                    word = CoordinatorLocalArmChoice.storedDownFlatWord
                      selected.view.payload i ∧
                    (OrdinaryMessageCodec.wordEquivFlat
                      (ReferencePrelaunchFollower.codecParams p rate.eta))
                        (OrdinaryMessageCodec.encodeDown _ message) = word ∧
                    ReferenceDownReception.ordinaryParse p rate (some word) = some message ∧
                    cut.ordinaryParse = some message ∧
                    message.val.sigma = selected.view.payload.sigma.val + 1 ∧
                    ∃ birthRecord : ReferenceActivePhysicalHorizon.RoundRecord
                      (p := p) (rate := rate),
                      birthRecord ∈ (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
                        rate rewards C_star C_h s hs x).records ∧
                      ReferenceAssignmentPayloadPersistence.InstallationBirth birthRecord
                        selected.view.payload ∧
                      birthRecord.input.time.val = selected.view.payload.sigma.val ∧
                      birthRecord.input.time.val ≤ record.input.time.val) := by
  classical
  have hbase :=
    ReferenceGeneratedInheritedDownWrongCompletionWitness.generated_inherited_down_first_wrong_completion_witness
      rate rewards C_star C_h s hs x i n control0 hfirst hwrong
  rcases hbase with ⟨cut, word, alpha, hAlpha, hcut, hwrongCut, hraw, hAlphaS,
    hbirth, hboundary, hhash, hcurrentSuffix, hobstruction⟩
  rcases hobstruction with hdetector | hearlier
  · exact ⟨cut, word, alpha, hAlpha, hcut, hwrongCut, hraw, hAlphaS,
      hbirth, hboundary, hhash, hcurrentSuffix, Or.inl hdetector⟩
  · rcases hearlier with ⟨earlier, hearlierPrefix, hearlierSent, offset,
      record, hrecordRun, hrecordSuffix, hrecordTime, htimeOrder, hearlierTime,
      hexecuted, call, cutEarlier, hcall, hcutEarlier, hearlierSample,
      hexpectedEarlier⟩
    refine ⟨cut, word, alpha, hAlpha, hcut, hwrongCut, hraw, hAlphaS,
      hbirth, hboundary, hhash, hcurrentSuffix, Or.inr ?_⟩
    refine ⟨earlier, hearlierPrefix, hearlierSent, offset, record, hrecordRun,
      hrecordSuffix, hrecordTime, htimeOrder, hearlierTime, hexecuted, call,
      cutEarlier, hcall, hcutEarlier, hearlierSample, hexpectedEarlier, ?_⟩
    obtain ⟨selected, hselected, hsender, hword, hparse, hencode⟩ :=
      actual_expectedDownWord_origin record i cutEarlier word hcutEarlier hexpectedEarlier
    have hcurrentParse := actual_wrongDownCut_parse
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n) i cut word hcut hwrongCut hraw
    let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
      rate rewards C_star C_h s hs x
    have hseedSpec := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
      rate rewards C_star C_h s hs x
    have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := hseedSpec.2.1
    obtain ⟨active, hactive, _hactiveUnique⟩ :=
      ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
        rate x.val rewards C_star C_h x.property.1
    have hseedEq : seed = active := Option.some.inj (hseedSpec.1.symm.trans hactive.1)
    have hinitial : seed.coordinator = .first := by
      rw [hseedEq]
      exact hactive.2.1
    have hrecordSameRun : record ∈
        (ReferenceActivePhysicalHorizon.run seed (x.val.1.2)
          (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s (p.T - s)
          (by omega) hmode).records := by
      simpa [ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
        ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput,
        ReferenceActiveHorizonMeasurability.runOfInput] using hrecordRun
    obtain ⟨birthRecord, hbirthRecord, hinstallation, hbirthTime, hbirthBefore⟩ :=
      ReferenceSelectedPayloadChronology.actualRun_selectedPayload_has_birth
        seed (x.val.1.2) (ActualInitializationPhysicalStep.selectedRowIndex p x.val)
        rewards s (p.T - s) (by omega) hmode hinitial record selected hrecordSameRun hselected
    have hbirthGenerated : birthRecord ∈
        (ReferenceGeneratedDownBatchCalendar.generatedSourceRun
          rate rewards C_star C_h s hs x).records := by
      simpa [ReferenceGeneratedDownBatchCalendar.generatedSourceRun,
        ReferenceGeneratedDownBatchCalendar.generatedSourceRunInput,
        ReferenceActiveHorizonMeasurability.runOfInput] using hbirthRecord
    refine ⟨selected, hselected, hsender, ?_⟩
    refine ⟨selected.view.payload.downRecord i, rfl, hword, ?_, hparse, ?_, ?_⟩
    · simpa [AssignmentStartPayload.Input.downRecord_fields] using hencode
    · exact hcurrentParse.trans hparse
    · constructor
      · rw [selected.view.payload.downRecord_fields i]
      · refine ⟨birthRecord, hbirthGenerated, hinstallation, hbirthTime, ?_⟩
        rw [hbirthTime]
        exact hbirthBefore

end Bandits.Support.ReferenceGeneratedInheritedDownCandidateOrigin

end
